Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Decidable.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Z.Lia.
Require Import compiler.FlatImp.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import compiler.Simp.

Local Open Scope Z_scope.

Module map.
  Lemma split_put_l2r{K V: Type}{map: map.map K V}{ok: map.ok map}
        {keqb: K -> K -> bool}{keqb_spec: EqDecider keqb}:
    forall m m1 m2 k v,
      map.get m1 k = None ->
      map.split m (map.put m1 k v) m2 ->
      map.split m m1 (map.put m2 k v).
  Proof.
    unfold map.split, map.disjoint.
    intros. simp. split.
    - apply map.map_ext.
      intros.
      rewrite !map.get_putmany_dec.
      rewrite !map.get_put_dec.
      destr (keqb k k0).
      + subst.
        destr (map.get m2 k0). 2: reflexivity.
        specialize H0r with (2 := E).
        rewrite map.get_put_same in H0r.
        exfalso. eauto.
      + destr (map.get m2 k0); reflexivity.
    - intros.
      rewrite map.get_put_dec in H1.
      destr (keqb k k0).
      + subst.
        simp.
        congruence.
      + specialize H0r with (2 := H1).
        rewrite map.get_put_diff in H0r by congruence.
        eauto.
  Qed.
End map.

Section FitsStack.
  Context {p: FlatToRiscvCommon.parameters}.

  Definition stack_usage_impl(outer_rec: env -> stmt Z -> option Z)(e: env): stmt Z -> option Z :=
    fix inner_rec s :=
      match s with
      | SLoad _ _ _ | SStore _ _ _ | SLit _ _ | SOp _ _ _ _ | SSet _ _ | SSkip | SInteract _ _ _ => Some 0
      | SIf _ s1 s2 | SLoop s1 _ s2 | SSeq s1 s2 =>
        match inner_rec s1, inner_rec s2 with
        | Some u1, Some u2 => Some (Z.max u1 u2)
        | _, _ => None
        end
      | SCall binds fname args =>
        match map.get e fname with
        | Some (argnames, retnames, body) =>
          match outer_rec (map.remove e fname) body with
          | Some u => Some (framelength (argnames, retnames, body) + u)
          | None => None
          end
        | None => None
        end
    end.

  Fixpoint stack_usage_rec(env_size_S: nat): env -> stmt Z -> option Z :=
    match env_size_S with
    | O => fun _ _ => None
    | S env_size => stack_usage_impl (stack_usage_rec env_size)
    end.

  Definition count_funs: env -> nat := map.fold (fun acc _ _ => S acc) O.

  (* returns the number of stack words needed to execute f_entrypoint (which must have no args
     and no return values), None if a function not in funimpls is called or a function is recursive *)
  Definition stack_usage_of_fun(funimpls: env)(f_entrypoint: String.string): option Z :=
    stack_usage_rec (S (count_funs funimpls)) funimpls (SCall nil f_entrypoint nil).

  Definition update_stack_usage(e_glob: env)
             (current: option Z)(fname: String.string)(fimpl: list Z * list Z * stmt Z): option Z :=
    match current with
    | Some cur => match fimpl with
                  | (nil, nil, fbody) => match stack_usage_of_fun e_glob fname with
                                         | Some res => Some (Z.max cur res)
                                         | None => None
                                         end
                  | _ => Some cur
                  end
    | None => None
    end.

  Definition stack_usage(funimpls: env): option Z :=
    map.fold (update_stack_usage funimpls) (Some 0) funimpls.

  Lemma fits_stack_monotone: forall e z1 s,
      fits_stack z1 e s -> forall z2, z1 <= z2 -> fits_stack z2 e s.
  Proof.
    induction 1; intros; econstructor; eauto; try blia.
    eapply IHfits_stack. blia.
  Qed.

  Context {env_ok: map.ok env}.

  Lemma fits_stack_monotone_env: forall e1 z s,
      fits_stack z e1 s -> forall e2, map.extends e2 e1 -> fits_stack z e2 s.
  Proof.
    induction 1; intros; econstructor; eauto; try blia.
    eapply IHfits_stack. (* TODO make map solver work: Solver.map_solver env_ok. *)
    unfold map.extends in *.
    intros.
    rewrite map.get_remove_dec.
    Tactics.destruct_one_match.
    - subst. rewrite map.get_remove_same in H2. assumption.
    - rewrite map.get_remove_diff in H2 by congruence. eauto.
  Qed.

  Lemma stack_usage_rec_correct: forall n e s z,
      stack_usage_rec n e s = Some z ->
      fits_stack z e s.
  Proof.
    induction n; intros.
    - simpl in H. discriminate.
    - simpl in H.
      revert z H.
      induction s; intros; simpl in H; simp.
      all: try (constructor; eauto using fits_stack_monotone, Z.le_max_l, Z.le_max_r; blia).
      econstructor. 1: eassumption.
      eapply IHn. Fail rewrite E0. (* PARAMRECORDS *) etransitivity. 1: exact E0.
      f_equal. unfold framelength. blia.
  Qed.

  (* The art of figuring out the right induction hypothesis... *)
  Let P(e_glob e_done: env)(r: option Z): Prop :=
    forall e_rest f fbody z,
      r = Some z ->
      map.get e_done f = Some (nil, nil, fbody) ->
      map.split e_glob e_done e_rest ->
      fits_stack (z - framelength (nil, nil, fbody)) (map.remove e_glob f) fbody.

  Lemma stack_usage_correct_aux: forall e_glob e_done,
      P e_glob e_done (map.fold (update_stack_usage e_glob) (Some 0) e_done).
  Proof.
    intro e_glob. eapply map.fold_spec.
    - subst P. cbv beta. intros. rewrite map.get_empty in H0. discriminate.
    - intros. subst P. cbv beta in *.
      intros.
      destruct v as [ [ newargs newrets ] newbody ].
      unfold update_stack_usage in *.
      simp.
      pose proof H3 as A.
      apply map.split_put_l2r in A. 2: assumption.
      destruct newargs; destruct newrets. {
        unfold stack_usage_of_fun in *.
        simpl in H1.
        simp.
        assert (map.get e_glob k = Some (nil, nil, newbody)) as Q. {
          clear -H3 E0 H env_ok.
          unfold map.split, map.disjoint in *.
          simp.
          etransitivity. 1: exact E0.
          rewrite map.get_putmany_left in E0.
          - rewrite map.get_put_same in E0. congruence.
          - match goal with
            | |- ?x = None => destr x
            end.
            2: reflexivity.
            exfalso.
            eapply H3r. 2: exact E.
            rewrite map.get_put_same. reflexivity.
        }
        simpl in Q,E0. rewrite Q in E0. symmetry in E0. simp.
        rewrite map.get_put_dec in H2.
        eapply stack_usage_rec_correct in E1.
        destr (String.eqb k f).
        * simp. subst.
          eapply fits_stack_monotone. 1: eassumption.
          unfold framelength.
          blia.
        * specialize H0 with (1 := eq_refl).
          eapply fits_stack_monotone.
          -- eauto.
          -- blia.
      }
      all: rewrite map.get_put_dec in H2.
      all: destr (String.eqb k f); try discriminate.
      all: simp; eauto.
  Qed.

  Lemma stack_usage_correct: forall e z f fbody,
      map.get e f = Some (nil, nil, fbody) ->
      stack_usage e = Some z ->
      fits_stack (z - framelength (nil, nil, fbody)) (map.remove e f) fbody.
  Proof.
    intros. unfold stack_usage in *.
    pose proof stack_usage_correct_aux as Q.
    subst P.
    cbv beta in Q.
    eapply Q with (e_rest := map.empty); try eassumption.
    apply map.split_empty_r.
    reflexivity.
  Qed.

End FitsStack.
