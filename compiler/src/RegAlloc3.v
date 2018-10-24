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

  (* operations *)
  Axiom reverse_get: map K V -> V -> option K.
  Axiom intersect_map: map K V -> map K V -> map K V.
  Axiom remove_by_value: map K V -> V -> map K V.

  (* specs *)
  Axiom put_put_same: forall k v1 v2 m, put (put m k v1) k v2 = put m k v2.
  Axiom reverse_reverse_get: forall k v m, reverse_get m v = Some k -> get m k = Some v.
  Axiom get_in_range: forall k v m, get m k = Some v -> v \in range m.
  Axiom remove_by_value_spec: forall k v m, get (remove_by_value m v) k <> Some v.
  Axiom get_intersect_map: forall k v m1 m2,
      get (intersect_map m1 m2) k = Some v <-> get m1 k = Some v /\ get m2 k = Some v.

  (* TODO some of this should go into state calculus *)
  (* probably derived *)
  Axiom not_in_range_of_remove_by_value: forall m v, ~ v \in range (remove_by_value m v).
  Axiom extends_remove_by_value: forall m v, extends m (remove_by_value m v).
  Axiom extends_intersect_map_l: forall r1 r2, extends r1 (intersect_map r1 r2).
  Axiom extends_intersect_map_r: forall r1 r2, extends r2 (intersect_map r1 r2).
  Axiom extends_intersect_map_lr: forall m11 m12 m21 m22,
      extends m11 m21 ->
      extends m12 m22 ->
      extends (intersect_map m11 m12) (intersect_map m21 m22).

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

  Local Notation stmt  := (FlatImp.stmt srcvar func). (* input type *)
  Local Notation stmt' := (FlatImp.stmt impvar func). (* output type *)

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
  Abort.

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

  Lemma loop_inv_step: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      extends (mappings (mappings Inv s1) s2) Inv.
  Proof.
    intros. subst Inv. unfold loop_inv.
  Admitted.

  Lemma loop_inv_idemp: forall r s1 s2,
      let Inv := loop_inv mappings r s1 s2 in
      loop_inv mappings Inv s1 s2 = Inv.
  Proof using .
  Admitted.

  Lemma checker_correct: forall n r st1 st1' m1 st2 m2 s annotated s',
      eval n st1 m1 s = Some (st2, m2) ->
      erase annotated = s ->
      checker r annotated = Some s' ->
      states_compat st1 r st1' ->
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
      edestruct IHn as [st2' [? ?]]; [ (eassumption || reflexivity).. | ].
      eauto with checker_hints.
    - clear Case_SIf_Else.
      edestruct IHn as [st2' [? ?]]; [ (eassumption || reflexivity).. | ].
      eauto with checker_hints.
    - clear Case_SLoop_Done.
      edestruct IHn as [st2' [? ?]]; eauto with checker_hints.
      + eapply states_compat_extends; [|eassumption].
        apply loop_inv_init.
      + rewrite H0.
        pose proof H1 as P.
        unfold states_compat in P.
        specialize P with (2 := H).
        rewrite P.
        * rewrite reg_eqb_eq by reflexivity. eauto.
        * eassumption.

    - clear Case_SLoop_NotDone.
      pose proof E0 as C1. pose proof E1 as C2.
      eapply IHn in E0; [| |reflexivity|]; [|eassumption|]; cycle 1. {
        eapply states_compat_extends; [|eassumption].
        apply loop_inv_init.
      }
      destruct_products.
      eapply IHn in E1; [| |reflexivity|]; [|eassumption|eassumption].
      destruct_products.
      specialize IHn with (annotated := (ASLoop annotated1 cond annotated2)).
      move IHn at bottom.
      specialize IHn with (r := (loop_inv mappings r annotated1 annotated2)). (* <- a choice *)
      specialize IHn with (2 := eq_refl).
      specialize IHn with (1 := H).
      specialize IHn with (s' := SLoop s i s0).
      edestruct IHn as [? [? ?]].
      + clear -C.
        simpl in *.
        repeat (destruct_one_match_hyp; [|discriminate]).
        repeat match goal with
               | H: Some _ = Some _ |- _ => inversion H; subst; clear H
               | H: reverse_get _ _ = Some _ |- _ =>
                 let H' := fresh H "_rrg" in
                 unique pose proof (reverse_reverse_get _ _ _ H) as H'
               end.
        set (Inv := (loop_inv mappings r annotated1 annotated2)) in *.
        set (m1 := (mappings Inv annotated1)) in *.
        set (Inv' := (loop_inv mappings Inv annotated1 annotated2)).
        assert (Inv' = Inv) as EI. {
          clear. subst Inv'. apply loop_inv_idemp.
        }
        rewrite EI.
        subst m1.
        rewrite_match.
        reflexivity.
      + eapply states_compat_extends; [|eassumption].
        set (Inv := (loop_inv mappings r annotated1 annotated2)) in *.
        apply loop_inv_step.
      + eexists.
        rewrite_match.
        pose proof E0r as P.
        unfold states_compat in P.
        erewrite P by eassumption. clear P.
        rewrite reg_eqb_ne by congruence.
        split; [eassumption|].
        simpl in H1.
        rewrite loop_inv_idemp in H1.
        exact H1.

    - clear Case_SSeq.
      eapply IHn in E.
      destruct_products.
      eapply IHn in E0.
      destruct_products.
      eexists.
      rewrite El. all: typeclasses eauto with core.
    - clear Case_SCall.
      discriminate.
  Qed.

End RegAlloc.
