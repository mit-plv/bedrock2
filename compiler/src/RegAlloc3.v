Require Import compiler.FlatImp.
Require Import compiler.Decidable.
Require Import Coq.Lists.List.
Require Import riscv.Utility.
Require Import compiler.Op.
Require Import compiler.util.Map.
Require Import compiler.util.Set.
Require Import compiler.Memory.
Require Import compiler.util.Tactics.
Require Import compiler.util.MapSolverTest.


Section TODO.
  Context {K V: Type}.
  Context {Mf: MapFunctions K V}.
  (*
  Axiom get_in_domain: forall k m, k \in (domain m) -> exists v, get m k = Some v.
  Axiom domain_put: forall k v m, domain (put m k v) = union (domain m) (singleton_set k).
  *)

  (* specs *)
  Axiom put_put_same: forall k v1 v2 m, put (put m k v1) k v2 = put m k v2.
  Axiom reverse_reverse_get: forall k v m, reverse_get m v = Some k -> get m k = Some v.
  Axiom get_in_range: forall k v m, get m k = Some v -> v \in range m.
  Axiom remove_by_value_spec: forall k v m, get (remove_by_value m v) k <> Some v.

  (* TODO some of this should go into state calculus *)
  (* probably derived *)
  Axiom not_in_range_of_remove_by_value: forall m v, ~ v \in range (remove_by_value m v).
  Axiom extends_remove_by_value: forall m v, extends m (remove_by_value m v).

  Axiom remove_by_value_put: forall k v m,
      remove_by_value (put m k v) v = remove_by_value m v.
  Axiom remove_by_value_idemp: forall v m,
      remove_by_value (remove_by_value m v) v = remove_by_value m v.
  Axiom extends_remove_by_value_same: forall x m1 m2,
      extends m1 m2 ->
      extends (remove_by_value m1 x) (remove_by_value m2 x).
  Axiom equality_by_extends: forall m1 m2,
      extends m1 m2 ->
      extends m2 m1 ->
      m1 = m2. (* requires functional extensionality, or unique internal representation *)
End TODO.

Local Notation "'bind_opt' x <- a ; f" :=
  (match a with
   | Some x => f
   | None => None
   end)
  (right associativity, at level 70, x pattern).


Section Live.

  Context {var func A: Set}.
  Context {varset: SetFunctions var}.
  Local Notation stmt := (stmt var func).
  Local Notation vars := (set var).

  (* set of variables which is certainly written while executing s *)
  Fixpoint certainly_written(s: stmt): vars :=
    match s with
    | SLoad x y    => singleton_set x
    | SStore x y   => singleton_set x
    | SLit x v     => singleton_set x
    | SOp x op y z => singleton_set x
    | SSet x y     => singleton_set x
    | SIf cond s1 s2 => intersect (certainly_written s1) (certainly_written s2)
    | SLoop s1 cond s2 => certainly_written s1
    | SSeq s1 s2 => union (certainly_written s1) (certainly_written s2)
    | SSkip => empty_set
    | SCall argnames fname resnames => of_list resnames
    end.

  (* set of variables which is live before executing s *)
  Fixpoint live(s: stmt): vars :=
    match s with
    | SLoad x y    => singleton_set y
    | SStore x y   => union (singleton_set x) (singleton_set y)
    | SLit x v     => empty_set
    | SOp x op y z => union (singleton_set y) (singleton_set z)
    | SSet x y     => singleton_set y
    | SIf cond s1 s2   => union (singleton_set cond) (union (live s1) (live s2))
    | SLoop s1 cond s2 => union (live s1) (diff (union (singleton_set cond) (live s2))
                                                (certainly_written s1))
    | SSeq s1 s2       => union (live s1) (diff (live s2) (certainly_written s1))
    | SSkip => empty_set
    | SCall argnames fname resnames => of_list argnames
    end.

End Live.

Section RegAlloc.

  Variable srcvar: Set.
  Context {srcvar_eq_dec: DecidableEq srcvar}.
  Variable impvar: Set.
  Context {impvar_eq_dec: DecidableEq impvar}.
  Variable func: Set.
  Context {func_eq_dec: DecidableEq func}.

  Context {Map: MapFunctions impvar srcvar}.
  Notation srcvars := (@set srcvar (@map_range_set _ _ Map)).
  Notation impvars := (@set impvar (@map_domain_set _ _ Map)).
  Existing Instance map_domain_set.
  Existing Instance map_range_set.

  (* annotated statement: each assignment is annotated with impvar which it assigns,
     loop has map invariant *)
  Inductive astmt: Type :=
    | ASLoad(x: srcvar)(x': impvar)(a: srcvar)
    | ASStore(a: srcvar)(v: srcvar)
    | ASLit(x: srcvar)(x': impvar)(v: Z)
    | ASOp(x: srcvar)(x': impvar)(op: bopname)(y z: srcvar)
    | ASSet(x: srcvar)(x': impvar)(y: srcvar)
    | ASIf(cond: srcvar)(bThen bElse: astmt)
    | ASLoop(body1: astmt)(cond: srcvar)(body2: astmt)
    | ASSeq(s1 s2: astmt)
    | ASSkip
    | ASCall(binds: list (srcvar * impvar))(f: func)(args: list srcvar).

(*
  Ltac head e :=
    match e with
    | ?a _ => head a
    | _ => e
    end.

  Goal forall (s: astmt), False.
    intro s.
    destruct s eqn: E;
    match type of E with
    | _ = ?r => let h := head r in idtac "| set ( case :=" h ")"
    end.
  Abort.
*)

  Local Notation stmt  := (FlatImp.stmt srcvar func). (* input type *)
  Local Notation stmt' := (FlatImp.stmt impvar func). (* output type *)

  Variable dummy_impvar: impvar.

  Definition start_interval(current: srcvars * impvars * map impvar srcvar)(x: srcvar)
    : srcvars * impvars * map impvar srcvar :=
    let '(o, a, m) := current in
    let o := union o (singleton_set x) in
    let '(r, a) := pick_or_else a dummy_impvar in
    let m := put m r x in
    (o, a, m).

  Variable available_impvars: impvars.

  Definition annotate_assignment(s: stmt)(y: impvar): astmt :=
    match s with
    | SLoad x a => ASLoad x y a
    | SLit x v => ASLit x y v
    | SOp x op a b => ASOp x y op a b
    | SSet x a => ASSet x y a
    | _ => ASSkip (* not an assignment *)
    end.

  Fixpoint regalloc
           (m: map impvar srcvar)(* current mapping *)
           (s: stmt)             (* current sub-statement *)
           (l: srcvars)          (* variables which have a life after statement s *)
    : (astmt *             (* annotated statement *)
       map impvar srcvar)  (* new mapping *)
    :=
    (* variables which currently occupy a register (maybe unjustified) *)
    let o_original := range m in
    (* these are the variables which actually deserve to occupy a register: *)
    let o := union (live s) (diff l (certainly_written s)) in
    (* intervals which ended... *)
    let became_dead := diff o_original o in
    (* ... allow us to prune m: *)
    let m := remove_values m became_dead in
    (* *currently* available registers *)
    let a := diff available_impvars (domain m) in
    match s with
    | SLoad x _ | SLit x _ | SOp x _ _ _ | SSet x _ =>
        match reverse_get m x with
        | Some y => (* nothing to do because no new interval starts *)
                    (annotate_assignment s y, m)
        | None   => (* new interval starts *)
                    let y := fst (pick_or_else a dummy_impvar) in
                    (annotate_assignment s y, put m y x)
        end
    | SStore x y => (ASStore x y, m)
    | SIf cond s1 s2   =>
        let '(s1', m1) := regalloc m s1 l in
        let '(s2', m2) := regalloc m s2 l in
        (ASIf cond s1' s2', intersect_map m1 m2)
    | SLoop s1 cond s2 =>
        let '(s1', m) := regalloc m s1 (union (union (singleton_set cond) (live s2)) l) in
        let '(s2', m) := regalloc m s2 (union l (live s)) in
        (ASLoop s1' cond s2', m)
    | SSeq s1 s2 =>
        let '(s1', m) := regalloc m s1 (union (live s2) l) in
        let '(s2', m) := regalloc m s2 l in
        (ASSeq s1' s2', m)
    | SSkip => (ASSkip, m)
  (*| SCall argnames fname resnames => fold_left start_interval resnames (o, a, m) *)
    | SCall _ _ _ => (ASSkip, empty_map) (* TODO *)
    end.

  Definition loop_inv(mappings: map impvar srcvar -> astmt -> map impvar srcvar)
                     (m: map impvar srcvar)(s1 s2: astmt): map impvar srcvar :=
    intersect_map m (mappings (mappings m s1) s2).

  (* impvar -> srcvar mappings which are guaranteed to hold after running s
     (under-approximation) *)
  Definition mappings :=
    fix rec(m: map impvar srcvar)(s: astmt): map impvar srcvar :=
      match s with
      | ASLoad x x' _ | ASLit x x' _ | ASOp x x' _ _ _ | ASSet x x' _ =>
          (* if several impvars store the value of x, they won't all store the value of
             x after the update, but only x' will, because only x' is written in the target
             program, so we first have to remove the others *)
          put (remove_by_value m x) x' x
      | ASStore a v => m
      | ASIf cond s1 s2 => intersect_map (rec m s1) (rec m s2)
      | ASLoop s1 cond s2 => rec (loop_inv rec m s1 s2) s1
      | ASSeq s1 s2 => rec (rec m s1) s2
      | ASSkip => m
      | ASCall binds f args => empty_map (* TODO *)
      end.

  Hint Resolve
       extends_put_same
       extends_remove_by_value_same
       extends_intersect_map_lr
       extends_refl
    : map_hints.

  Hint Rewrite
       remove_by_value_put
       remove_by_value_idemp
    : map_rew.

  Hint Extern 1 => autorewrite with map_rew : map_hints.

  Lemma mappings_monotone: forall s m1 m2,
      extends m1 m2 ->
      extends (mappings m1 s) (mappings m2 s).
  Proof.
    induction s; intros; simpl in *; unfold loop_inv in *; eauto 7 with map_hints.
  Qed.

  Lemma mappings_intersect_map: forall s m1 m2,
      mappings (intersect_map m1 m2) s = intersect_map (mappings m1 s) (mappings m2 s).
  Proof.
    induction s; intros; simpl in *; unfold loop_inv; eauto with map_hints.
    - admit.
    - admit.
    - admit.
    - admit.
    - admit.
    - rewrite IHs1.
      (* used to hold at some point
      rewrite IHs2.
      forget (mappings m1 s1) as m11.
      forget (mappings m1 s2) as m12.
      forget (mappings m2 s1) as m21.
      forget (mappings m2 s2) as m22.
      rewrite? intersect_map_assoc.
      f_equal.
      rewrite <-? intersect_map_assoc.
      f_equal.
      apply intersect_map_comm.
    - rewrite IHs1. rewrite IHs2. rewrite IHs1.
      forget (mappings (mappings (mappings m2 s1) s2) s1) as m2121.
      forget (mappings (mappings (mappings m1 s1) s2) s1) as m1121.
      forget (mappings m1 s1) as m11.
      forget (mappings m2 s1) as m21.
      rewrite? intersect_map_assoc.
      f_equal.
      rewrite <-? intersect_map_assoc.
      f_equal.
      apply intersect_map_comm.
    - rewrite IHs1. rewrite IHs2. reflexivity.
  Qed.
       *)
  Admitted.

  Lemma mappings_mappings_extends_mappings: forall s m,
      extends (mappings (mappings m s) s) (mappings m s).
  Proof.
    induction s; intros; simpl in *;
      try solve [
            (* these can be specialized infinitely many times with themselves *)
            try clear IHs;
            try clear IHs1;
            try clear IHs2;
            map_solver impvar srcvar ].
    - apply intersect_map_extends.
      +
  Admitted.

  Lemma mappings_bw_monotone: forall s m1 m2,
      bw_extends m1 m2 ->
      bw_extends (mappings m1 s) (mappings m2 s).
  Proof using.
    induction s; intros; simpl in *; unfold loop_inv in *; eauto 7 with map_hints.
    admit. admit. admit. admit.
    admit.
    eapply IHs1.
    (* TODO not sure! *)
  Admitted.

  Lemma mappings_idemp: forall s m1 m2,
      m2 = mappings m1 s ->
      mappings m2 s = m2.
  Proof.
    induction s; intros; simpl in *;
      try reflexivity;
      try (subst; apply put_put_same).
(*
    {
      erewrite IHs1 with (m2 := m2); [erewrite IHs2 with (m2 := m2)|].
      subst.
      - admit. (* ok *)
      - symmetry. eapply IHs2. (* stuck in a loop *)
*)
  Admitted.

  Definition checker :=
    fix rec(m: map impvar srcvar)(s: astmt): option stmt' :=
      match s with
      | ASLoad x x' a =>
          bind_opt a' <- reverse_get m a;
          Some (SLoad x' a')
      | ASStore a v =>
          bind_opt a' <- reverse_get m a;
          bind_opt v' <- reverse_get m v;
          Some (SStore a' v')
      | ASLit x x' v =>
          Some (SLit x' v)
      | ASOp x x' op y z =>
          bind_opt y' <- reverse_get m y;
          bind_opt z' <- reverse_get m z;
          Some (SOp x' op y' z')
      | ASSet x x' y =>
          bind_opt y' <- reverse_get m y;
          Some (SSet x' y')
      | ASIf cond s1 s2 =>
          bind_opt cond' <- reverse_get m cond;
          bind_opt s1' <- rec m s1;
          bind_opt s2' <- rec m s2;
          Some (SIf cond' s1' s2')
      | ASLoop s1 cond s2 =>
          let m1 := loop_inv mappings m s1 s2 in
          let m2 := mappings m1 s1 in
          bind_opt cond' <- reverse_get m2 cond;
          bind_opt s1' <- rec m1 s1;
          bind_opt s2' <- rec m2 s2;
          Some (SLoop s1' cond' s2')
      | ASSeq s1 s2 =>
          bind_opt s1' <- rec m s1;
          bind_opt s2' <- rec (mappings m s1) s2;
          Some (SSeq s1' s2')
      | ASSkip => Some SSkip
      | ASCall binds f args => None (* TODO *)
      end.

  Definition erase :=
    fix rec(s: astmt): stmt :=
      match s with
      | ASLoad x x' a => SLoad x a
      | ASStore a v => SStore a v
      | ASLit x x' v => SLit x v
      | ASOp x x' op y z => SOp x op y z
      | ASSet x x' y => SSet x y
      | ASIf cond s1 s2 => SIf cond (rec s1) (rec s2)
      | ASLoop s1 cond s2 => SLoop (rec s1) cond (rec s2)
      | ASSeq s1 s2 => SSeq (rec s1) (rec s2)
      | ASSkip => SSkip
      | ASCall binds f args => SCall (List.map fst binds) f args
      end.

  (* TODO needs better interface: both at beginning and at end, specify mapping we care about *)
  Definition register_allocation(s: stmt)(resultVars: srcvars)
    : map impvar srcvar * option stmt' :=
    let initialMap := empty_map in
    let '(annotated, resultMap) := regalloc initialMap s resultVars in
    (resultMap, checker initialMap annotated).

  (* claim: for all astmt a, if checker succeeds and returns s', then
     (erase a) behaves the same as s' *)

  Context {mword: Set}.
  Context {MW: MachineWidth mword}.
  Context {srcStateMap: MapFunctions srcvar mword}.
  Context {impStateMap: MapFunctions impvar mword}.
  Context {srcFuncMap: MapFunctions func (list srcvar * list srcvar * stmt)}.
  Context {impFuncMap: MapFunctions func (list impvar * list impvar * stmt')}.

  Definition eval: nat -> map srcvar mword -> mem -> stmt -> option (map srcvar mword * mem)
    := eval_stmt _ _ empty_map.

  Definition eval': nat -> map impvar mword -> mem -> stmt' -> option (map impvar mword * mem)
    := eval_stmt _ _ empty_map.

  (*
  Definition states_compat(st: map srcvar mword)(r: map impvar srcvar)(st': map impvar mword) :=
    forall (x: srcvar) (w: mword),
      (* TODO restrict to live variables *)
      get st x = Some w ->
      exists (x': impvar), get r x' = Some x /\ get st' x' = Some w.
  *)

  Definition states_compat(st: map srcvar mword)(r: map impvar srcvar)(st': map impvar mword) :=
    forall (x: srcvar) (x': impvar),
      get r x' = Some x ->
      forall w,
        get st x = Some w ->
        get st' x' = Some w.

  Lemma states_compat_put: forall st1 st1' v x x' r,
      ~ x \in (range r) ->
      states_compat st1 r st1' ->
      states_compat (put st1 x v) (put r x' x) (put st1' x' v).
  Proof.
    unfold states_compat.
    intros.
    rewrite get_put.
    do 2 match goal with
    | H: get (put _ _ _) _ = _ |- _ => rewrite get_put in H
    end.
    destruct_one_match; clear E.
    - subst.
      replace x0 with x in H2 by congruence.
      destruct_one_match_hyp; [assumption|contradiction].
    - destruct_one_match_hyp.
      + subst.
        apply get_in_range in H1.
        contradiction.
      + eauto.
  Qed.

  Lemma states_compat_extends: forall st st' r1 r2,
      extends r1 r2 ->
      states_compat st r1 st' ->
      states_compat st r2 st'.
  Proof.
    unfold states_compat. eauto.
  Qed.

  Hint Resolve
       states_compat_put
       not_in_range_of_remove_by_value
       states_compat_extends
       extends_remove_by_value
       extends_intersect_map_l
       extends_intersect_map_r
    : checker_hints.

  Lemma loop_inv_init: forall r s1 s2,
      extends r (loop_inv mappings r s1 s2).
  Proof.
    intros. unfold loop_inv. eauto with checker_hints.
  Qed.

  (* depends on unproven mappings_intersect_map mappings_mappings_extends_mappings *)
  Lemma loop_inv_step: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      extends (mappings (mappings Inv s1) s2) Inv.
  Proof.
    intros. subst Inv. unfold loop_inv.
    change (mappings (mappings r s1) s2) with (mappings r (ASSeq s1 s2)).
    change (mappings (mappings (intersect_map r (mappings r (ASSeq s1 s2))) s1) s2)
      with (mappings (intersect_map r (mappings r (ASSeq s1 s2))) (ASSeq s1 s2)).
    forget (ASSeq s1 s2) as s. clear s1 s2.
    rewrite mappings_intersect_map.
    eapply extends_trans; [|apply extends_intersect_map_r].
    apply intersect_map_extends.
    - apply extends_refl.
    - apply mappings_mappings_extends_mappings.
  Qed.

  Lemma test: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      False.
  Proof.
    intros.
    pose proof (loop_inv_step r s1 s2) as P. simpl in P.
    change (mappings (mappings (loop_inv mappings r s1 s2) s1) s2) with
           (mappings (mappings Inv s1) s2) in P.
    unfold loop_inv in P.
    (* "extends _ (intersect_map _ _)" is useless *)
  Abort.

  Lemma loop_inv_step_bw: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      bw_extends (mappings (mappings Inv s1) s2) Inv.
  Proof using.
    intros. subst Inv. unfold loop_inv.
  Admitted.

  Lemma extends_loop_inv: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      extends Inv (loop_inv mappings Inv s1 s2).
  Proof.
    intros.
    subst Inv. unfold loop_inv.
    apply extends_intersect_map_lr.
    - apply extends_intersect_map_l.
    - apply mappings_monotone. apply mappings_monotone.
      apply extends_intersect_map_l.
  Qed.

  Lemma bw_extends_loop_inv: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      bw_extends Inv (loop_inv mappings Inv s1 s2).
  Proof using.
  Admitted.

  (* this direction would be needed to get full idempotence of loop_inv *)
  Lemma loop_inv_extends: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      extends (loop_inv mappings Inv s1 s2) Inv.
  Proof.
    intros. subst Inv.
    unfold loop_inv.
    change (mappings (mappings r s1) s2) with (mappings r (ASSeq s1 s2)).
    change (mappings (mappings (intersect_map r (mappings r (ASSeq s1 s2))) s1) s2)
      with (mappings (intersect_map r (mappings r (ASSeq s1 s2))) (ASSeq s1 s2)).
    forget (ASSeq s1 s2) as s. clear s1 s2.
    remember (intersect_map r (mappings r s)) as r1.
  (*
  Proof.
    intros. unfold extends, loop_inv. intros.
    apply intersect_map_spec.
    split; [assumption|].

    pose proof mappings_monotone as P. unfold extends in P.
    eapply P.

    subst Inv. unfold loop_inv.
    set (a := (intersect_map r (mappings (mappings r s1) s2))).

    pose proof extends_loop_inv as Q. simpl in Q.*)
  Abort.

  Lemma loop_inv_idemp: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      loop_inv mappings Inv s1 s2 = Inv.
  Proof using .
  Abort.

  Definition precond(m: map impvar srcvar)(s: astmt): map impvar srcvar :=
    match s with
    | ASLoop s1 cond s2 => loop_inv mappings m s1 s2
    | _ => m
    end.

  Lemma precond_weakens: forall m s,
      extends m (precond m s).
  Proof.
    intros. destruct s; try apply extends_refl.
    unfold precond, loop_inv.
    apply extends_intersect_map_l.
  Qed.

  Hint Resolve precond_weakens : checker_hints.

  Lemma checker_correct: forall n r st1 st1' m1 st2 m2 s annotated s',
      eval n st1 m1 s = Some (st2, m2) ->
      erase annotated = s ->
      checker r annotated = Some s' ->
      states_compat st1 (precond r annotated) st1' ->
      exists st2',
        eval' n st1' m1 s' = Some (st2', m2) /\
        states_compat st2 (mappings r annotated) st2'.
  Proof.
    induction n; intros; [
      match goal with
      | H: eval 0 _ _ _ = Some _ |- _ => solve [inversion H]
      end
    |].
    unfold eval, eval' in *.
    invert_eval_stmt;
      try destruct_pair_eqs;
      match goal with
      | H: erase ?s = _ |- _ =>
        destruct s;
        inversion H;
        subst;
        clear H
      end;
      subst;
      match goal with
      | H: checker _ ?x = _ |- _ => pose proof H as C; remember x as AS in C
      end;
      simpl in *;
      repeat (destruct_one_match_hyp; [|discriminate]);
      repeat match goal with
             | H: Some _ = Some _ |- _ => inversion H; subst; clear H
             | H: reverse_get _ _ = Some _ |- _ =>
                  let H' := fresh H "_rrg" in
                  unique pose proof (reverse_reverse_get _ _ _ H) as H'
             | H: states_compat _ _ _ |- _ => erewrite H by eassumption
             end;
      repeat match goal with
             | H: states_compat _ _ _ |- _ => erewrite H by eassumption
             | H: _ = _ |- _ => rewrite H
             end;
      repeat (rewrite reg_eqb_ne by congruence);
      repeat (rewrite reg_eqb_eq by congruence);
      eauto with checker_hints.
    - clear Case_SIf_Then.
      edestruct IHn as [st2' [? ?]]; eauto with checker_hints.
    - clear Case_SIf_Else.
      edestruct IHn as [st2' [? ?]]; eauto with checker_hints.
    - clear Case_SLoop_Done.
      edestruct IHn as [st2' [? ?]]; eauto with checker_hints.
      rewrite H0.
      pose proof H1 as P.
      unfold states_compat in P.
      specialize P with (2 := H).
      rewrite P.
      + rewrite reg_eqb_eq by reflexivity. eauto.
      + eassumption.

    - clear Case_SLoop_NotDone.
      pose proof E0 as C1. pose proof E1 as C2.
      eapply IHn in E0; [| |reflexivity|]; [|eassumption|]; cycle 1. {
        eapply states_compat_extends; [|eassumption].
        apply precond_weakens.
      }
      destruct_products.
      eapply IHn in E1; [| |reflexivity|]; [|eauto with checker_hints..].
      destruct_products.
      (* get rid of r and replace it by Inv everywhere *)
      remember (loop_inv mappings r annotated1 annotated2) as Inv.
      (* Search r. only HeqInv and C *)
      specialize IHn with (annotated := (ASLoop annotated1 cond annotated2)).
      move IHn at bottom.
      specialize IHn with (r := r).
      specialize IHn with (2 := eq_refl).
      specialize IHn with (1 := H).
      specialize IHn with (s' := SLoop s i s0).
      edestruct IHn as [? [? ?]].
      + exact C.
      + unfold precond.
        eapply states_compat_extends; [|eassumption].
        subst Inv.
        apply loop_inv_step.
      + eexists.
        rewrite_match.
        pose proof E0r as P.
        unfold states_compat in P.
        erewrite P by eassumption. clear P.
        rewrite reg_eqb_ne by congruence.
        split; [eassumption|].
        simpl in H1.
        subst Inv.
        assumption.

    - clear Case_SSeq.
      eapply IHn in E.
      destruct_products.
      eapply IHn in E0.
      destruct_products.
      eexists.
      rewrite El. all: typeclasses eauto with core checker_hints.
    - clear Case_SCall.
      discriminate.
  Qed.

  Lemma checker_monotone: forall r1 r2 s s',
      extends r2 r1 ->
      checker r1 s = Some s' ->
      checker r2 s = Some s'.
  Proof using.
  Admitted.

  Lemma regalloc_succeeds: forall s annotated m m' l,
      subset (live s) (range m) ->
      regalloc m s l = (annotated, m') ->
      exists s', checker m annotated = Some s'.
  Proof.
    induction s; intros; simpl in *;
      [ set ( case := ASLoad )
      | set ( case := ASStore )
      | set ( case := ASLit )
      | set ( case := ASOp )
      | set ( case := ASSet )
      | set ( case := ASIf )
      | set ( case := ASLoop )
      | set ( case := ASSeq )
      | set ( case := ASSkip )
      | set ( case := ASCall ) ];
      move case at top;
      repeat ((destruct_pair_eqs; subst) || (destruct_one_match_hyp; try discriminate));
      simpl.
    - (* ASLoad: reverse_get of regalloc Some *)
      destruct (reverse_get m a) eqn: F.
      + (* reverse_get of checker Some *)
        eexists. reflexivity.
      + (* reverse_get of checker None *)
        exfalso. map_solver impvar srcvar.
    - (* ASLoad: reverse_get of regalloc None --> a fresh var will be picked *)
      destruct (reverse_get m a) eqn: F.
      + (* reverse_get of checker Some *)
        eexists. reflexivity.
      + (* reverse_get of checker None *)
        exfalso. map_solver impvar srcvar.
    - destruct (reverse_get m a) eqn: F; destruct (reverse_get m v) eqn: G;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - eauto.
    - eauto.
    - destruct (reverse_get m y) eqn: F; destruct (reverse_get m z) eqn: G;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - destruct (reverse_get m y) eqn: F; destruct (reverse_get m z) eqn: G;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - destruct (reverse_get m y) eqn: F;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - destruct (reverse_get m y) eqn: F;
        [eexists; reflexivity| (exfalso; map_solver impvar srcvar)..].
    - specialize IHs1 with (2 := E).
      specialize IHs2 with (2 := E0).
      destruct IHs1 as [s1' IHs1].
      {
        clear IHs2 E E0.


Ltac canonicalize_all K V ::=
  repeat match goal with
         | H: _ |- _ => progress canonicalize_map_hyp H
         end;
  invert_Some_eq_Some;
  repeat (autorewrite with rew_set_op_specs rew_map_specs || rewrite_get_put K V).

Ltac pick_one_existential :=
  multimatch goal with
  | x: ?T |- exists (_: ?T), _ => exists x
  end.

Ltac map_solver K V :=
  assert_is_type K;
  assert_is_type V;
  repeat autounfold with unf_map_defs unf_set_defs in *;
  destruct_products;
  intros;
  canonicalize_all K V;
  let RGN := fresh "RGN" in pose proof (@reverse_get_None K V _) as RGN;
  let RGS := fresh "RGS" in pose proof (@reverse_get_Some K V _) as RGS;
  repeat match goal with
  | H: forall (x: ?E), _, y: ?E |- _ =>
    first [ unify E K | unify E V ];
    ensure_no_body H;
    match type of H with
    | DecidableEq E => fail 1
    | _ => let H' := fresh H y in
           pose proof (H y) as H';
           canonicalize_map_hyp H';
           ensure_new H'
    end
  | H: forall (x: _), _, y: ?E |- _ =>
    let T := type of E in unify T Prop;
    ensure_no_body H;
    let H' := fresh H y in
    pose proof H as H';
    specialize H' with (1 := y); (* might instantiate a few universally quantified vars *)
    canonicalize_map_hyp H';
    ensure_new H'
  | H: ?P -> _ |- _ =>
    let T := type of P in unify T Prop;
    let F := fresh in
    assert P as F by eauto;
    let H' := fresh H "_eauto" in
    pose proof (H F) as H';
    clear F;
    canonicalize_map_hyp H';
    ensure_new H'
  end;
  let solver := congruence || auto || (exfalso; eauto) ||
                match goal with
                | H: ~ _ |- False => solve [apply H; intuition (auto || congruence || eauto)]
                end in
  let fallback := (destruct_one_map_match K V || pick_one_existential);
                  canonicalize_all K V in
  repeat (propositional;
          propositional_ors;
          try solve [ solver ];
          try fallback).


        map_solver impvar srcvar.

      }
      destruct IHs2 as [s2' IHs2].
      {
        clear IHs1 E E0.
        map_solver impvar srcvar.
      }
      destruct (reverse_get m cond) eqn: F; [| exfalso; map_solver impvar srcvar].
      eapply checker_monotone in IHs1; [ rewrite IHs1 | map_solver impvar srcvar ].
      eapply checker_monotone in IHs2; [ rewrite IHs2 | map_solver impvar srcvar ].
      eexists. reflexivity.
    -

  Abort.


End RegAlloc.
