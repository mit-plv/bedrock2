Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Decidable.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Z.Lia.
Require Import compiler.FlatImp.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import coqutil.Tactics.Simp.

Local Open Scope Z_scope.

Section FitsStack.
  Context {p: FlatToRiscvCommon.parameters}.

  (* returns two numbers:
     - number of stack words needed by current statement
     - number of stack words needed by its callees
     The total required stack is the sum of the two. *)
  Definition stack_usage_impl(outer_rec: env -> stmt Z -> option (Z*Z))(e: env): stmt Z -> option (Z*Z) :=
    fix inner_rec s :=
      match s with
      | SLoad _ _ _ _ | SStore _ _ _ _ | SInlinetable _ _ _ _ | SLit _ _
      | SOp _ _ _ _ | SSet _ _ | SSkip | SInteract _ _ _ => Some (0,0)
      | SStackalloc x n body =>
        if Z.leb 0 n then
          if Z.eqb (n mod Memory.bytes_per_word (Decode.bitwidth iset)) 0 then
            match inner_rec body with
            | Some (M, N) => Some (M + n / Memory.bytes_per_word (Decode.bitwidth iset), N)
            | None => None
            end
          else None
        else None
      | SIf _ s1 s2 | SLoop s1 _ s2 | SSeq s1 s2 =>
        match inner_rec s1, inner_rec s2 with
        | Some (M1, N1), Some (M2, N2) => Some (Z.max M1 M2, Z.max N1 N2)
        | _, _ => None
        end
      | SCall binds fname args =>
        match map.get e fname with
        | Some (argnames, retnames, body) =>
          match outer_rec (map.remove e fname) body with
          (* M is already accounted for in framelength *)
          | Some (M, N) => Some (0, N + framelength (argnames, retnames, body))
          | None => None
          end
        | None => None
        end
    end.

  Fixpoint stack_usage_rec(env_size_S: nat): env -> stmt Z -> option (Z*Z) :=
    match env_size_S with
    | O => fun _ _ => None
    | S env_size => stack_usage_impl (stack_usage_rec env_size)
    end.

  Definition count_funs: env -> nat := map.fold (fun acc _ _ => S acc) O.

  (* returns the number of stack words needed to execute f_entrypoint (which must have no args
     and no return values), None if a function not in funimpls is called or a function is recursive *)
  Definition stack_usage_of_fun(funimpls: env)(f_entrypoint: String.string): option Z :=
    match stack_usage_rec (S (count_funs funimpls)) funimpls (SCall nil f_entrypoint nil) with
    | Some (M, N) => Some (M + N)
    | None => None
    end.

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

  Lemma fits_stack_monotone: forall e y1 z1 s,
      fits_stack y1 z1 e s -> forall y2 z2, y1 <= y2 -> z1 <= z2 -> fits_stack y2 z2 e s.
  Proof.
    induction 1; intros; econstructor; eauto; try blia; eapply IHfits_stack; blia.
  Qed.

  Context {env_ok: map.ok env}.

  Lemma fits_stack_monotone_env: forall e1 y z s,
      fits_stack y z e1 s -> forall e2, map.extends e2 e1 -> fits_stack y z e2 s.
  Proof.
    induction 1; intros; econstructor; eauto; try blia.
    eapply IHfits_stack. (* TODO make map solver work: Solver.map_solver env_ok. *)
    unfold map.extends in *.
    intros.
    rewrite map.get_remove_dec.
    Tactics.destruct_one_match.
    - subst. rewrite map.get_remove_same in H3. assumption.
    - rewrite map.get_remove_diff in H3 by congruence. eauto.
  Qed.

  Lemma stack_usage_rec_equals_stackalloc_words: forall n s e M N,
      stack_usage_rec n e s = Some (M, N) ->
      M = FlatToRiscvDef.stackalloc_words s.
  Proof.
    induction n; intros; simpl in *. 1: discriminate.
    revert M N H.
    induction s; intros; simpl in *; simp;
      try specialize IHs with (1 := eq_refl);
      try specialize IHs1 with (1 := eq_refl);
      try specialize IHs2 with (1 := eq_refl);
      try blia.
    subst.
    apply Z.leb_le in E. apply Z.eqb_eq in E0.
    assert (0 < Memory.bytes_per_word (Decode.bitwidth iset)). {
      unfold Memory.bytes_per_word.
      destruct iset; reflexivity.
    }
    assert (0 <= nbytes / Memory.bytes_per_word (Decode.bitwidth iset)). {
      apply Z.div_pos; assumption.
    }
    remember (FlatToRiscvDef.stackalloc_words s) as sw.
    remember (Memory.bytes_per_word (Decode.bitwidth iset)) as bw.
    (* TODO why does "Z.div_mod_to_equations. blia." not work? *)
    replace (BinIntDef.Z.max 0 nbytes) with nbytes by blia.
    apply Zmod_divides in E0. 2: blia.
    simp.
    replace (bw * c + bw - 1) with (c * bw + (bw - 1)) by blia.
    rewrite Z.div_add_l by blia.
    rewrite (Z.div_small (bw - 1) bw) by blia.
    rewrite Z.mul_comm.
    rewrite Z.div_mul; blia.
  Qed.

  Lemma stack_usage_rec_correct: forall n e s y z,
      stack_usage_rec n e s = Some (y, z) ->
      fits_stack y z e s.
  Proof.
    induction n; intros.
    - simpl in H. discriminate.
    - simpl in H.
      revert y z H.
      induction s; intros; simpl in H; simp.
      all: try (constructor; eauto using fits_stack_monotone, Z.le_max_l, Z.le_max_r; blia).
      + specialize (IHs _ _ eq_refl).
        pose proof fits_stack_nonneg as P. specialize P with (1 := IHs).
        apply Z.leb_le in E. apply Z.eqb_eq in E0.
        econstructor.
        * assert (0 <= nbytes / Memory.bytes_per_word (Decode.bitwidth iset)). {
            apply Z.div_pos. 1: assumption. unfold Memory.bytes_per_word.
            destruct iset; reflexivity.
          }
          blia.
        * assumption.
        * assumption.
        * rewrite Z.add_simpl_r. assumption.
      + specialize IHn with (1 := E0).
        pose proof fits_stack_nonneg as P. specialize P with (1 := IHn). destruct P.
        econstructor. 1: reflexivity. 1: eassumption.
        pose proof stack_usage_rec_equals_stackalloc_words as P.
        specialize P with (1 := E0). subst.
        match goal with
        | |- fits_stack _ ?z _ _ => replace z with z1
        end.
        1: assumption.
        unfold framelength.
        blia.
  Qed.

  (* The art of figuring out the right induction hypothesis... *)
  Let P(e_glob e_done: env)(r: option Z): Prop :=
    forall e_rest f fbody z,
      r = Some z ->
      map.get e_done f = Some (nil, nil, fbody) ->
      map.split e_glob e_done e_rest ->
      fits_stack (FlatToRiscvDef.stackalloc_words fbody)
                 (z - framelength (nil, nil, fbody)) (map.remove e_glob f) fbody.

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
          clear -H3 E1 H env_ok.
          unfold map.split, map.disjoint in *.
          simp.
          etransitivity. 1: exact E1.
          rewrite map.get_putmany_left in E1.
          - rewrite map.get_put_same in E1. congruence.
          - match goal with
            | |- ?x = None => destr x
            end.
            2: reflexivity.
            exfalso.
            eapply H3p1. 2: exact E.
            rewrite map.get_put_same. reflexivity.
        }
        simpl in Q,E1. rewrite Q in E1. symmetry in E1. simp.
        rewrite map.get_put_dec in H2.
        pose proof stack_usage_rec_equals_stackalloc_words as P.
        specialize P with (1 := E2). subst.
        eapply stack_usage_rec_correct in E2.
        destr (String.eqb k f).
        * simp. subst.
          eapply fits_stack_monotone. 1: eassumption.
          all: unfold framelength.
          all: blia.
        * specialize H0 with (1 := eq_refl).
          eapply fits_stack_monotone.
          -- eauto.
          -- blia.
          -- unfold framelength. blia.
      }
      all: rewrite map.get_put_dec in H2.
      all: destr (String.eqb k f); try discriminate.
      all: simp; eauto.
  Qed.

  Lemma stack_usage_correct: forall e z f fbody,
      map.get e f = Some (nil, nil, fbody) ->
      stack_usage e = Some z ->
      fits_stack (FlatToRiscvDef.stackalloc_words fbody)
                 (z - framelength (nil, nil, fbody)) (map.remove e f) fbody.
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
