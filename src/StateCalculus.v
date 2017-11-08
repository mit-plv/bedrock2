Require Import lib.LibTactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import Coq.Logic.ClassicalFacts.
Require Import compiler.Axioms.
Require Import compiler.Common.
Require Import lib.fiat_crypto_tactics.Not.
Require Import lib.fiat_crypto_tactics.UniquePose.

Section StateCalculus.

  Context {var: Type}. (* variable name (key) *)
  Context {dec_eq_var: DecidableEq var}.
  Context {val: Type}. (* value *)
  Context {dec_eq_val: DecidableEq val}.
  Context {state: Type}.
  Context {stateMap: Map state var val}.

  (* models a set of vars *)
  Definition vars := var -> Prop.

  Definition extends(s1 s2: state) := forall x w, get s2 x = Some w -> get s1 x = Some w.

  Definition only_differ(s1: state)(vs: vars)(s2: state) :=
    forall x, x \in vs \/ get s1 x = get s2 x.

  Definition undef(s: state)(vs: vars) := forall x, x \in vs -> get s x = None.

  Definition subset(vs1 vs2: vars) := forall x, x \in vs1 -> x \in vs2.

  Lemma intersect_spec: forall (x: var) (A B: vars),
    x \in (intersect A B) <-> x \in A /\ x \in B.
  Proof. intros. cbv. tauto. Qed.

  Lemma union_spec: forall (x: var) (A B: vars),
    x \in (union A B) <-> x \in A \/ x \in B.
  Proof. intros. cbv. tauto. Qed.

  Lemma diff_spec: forall (x: var) (A B: vars),
    x \in (diff A B) <-> x \in A /\ ~ x \in B.
  Proof. intros. cbv. tauto. Qed.

  Lemma singleton_set_spec: forall (x y: var),
    x \in singleton_set y <-> x = y.
  Proof. intros. cbv. tauto. Qed.

  Lemma get_put: forall (s: state) (x y: var) (v: val),
    get (put s x v) y = if dec (x = y) then Some v else get s y.
  Proof.
    intros. destruct (dec (x = y)).
    - subst. rewrite get_put_same. reflexivity.
    - rewrite get_put_diff by assumption. reflexivity.
  Qed.

End StateCalculus.


Hint Unfold extends only_differ undef : unfold_state_calculus.
Ltac unf := repeat autounfold with unfold_state_calculus.

Hint Rewrite @intersect_spec @union_spec @diff_spec @singleton_set_spec : rewrite_set_op_specs.

(* only needed to get the DecidableEq *)
Ltac rewrite_get_put :=
  repeat match goal with
  | D: DecidableEq ?Var |- context [@get _ ?Var _ _ (put _ _ _) _] =>
     rewrite (@get_put Var D) in *
  | D: DecidableEq ?Var, _: context [@get _ ?Var _ _ (put _ _ _) _] |- _ =>
     rewrite (@get_put Var D) in *
  end.

Ltac state_calc :=
  unf; intros; autorewrite with rewrite_set_op_specs in *; rewrite_get_put;
  repeat match goal with
  | x: ?T, H: forall (y: ?T), _ |- _ => unique pose proof (H x)
  end;
  repeat (intuition (auto || congruence) || destruct_one_dec_eq).


Section Tests.

  Context {var: Type}. (* variable name (key) *)
  Context {dec_eq_var: DecidableEq var}.
  Context {val: Type}. (* value *)
  Context {dec_eq_val: DecidableEq val}.
  Context {state: Type}.
  Context {stateMap: Map state var val}.


  Lemma extends_refl: forall s, extends s s.
  Proof. state_calc. Qed.

  Lemma only_differ_union_l: forall s1 s2 r1 r2,
    only_differ s1 r1 s2 ->
    only_differ s1 (union r1 r2) s2.
  Proof. state_calc. Qed.

  Lemma only_differ_union_r: forall s1 s2 r1 r2,
    only_differ s1 r2 s2 ->
    only_differ s1 (union r1 r2) s2.
  Proof. state_calc. Qed.

  Lemma only_differ_one: forall s x v,
    only_differ s (singleton_set x) (put s x v).
  Proof. state_calc. Qed.

  Lemma only_differ_refl: forall s1 r,
    only_differ s1 r s1.
  Proof. state_calc. Qed.

  Lemma only_differ_sym: forall s1 s2 r,
    only_differ s1 r s2 ->
    only_differ s2 r s1.
  Proof. state_calc. Qed.

  Lemma only_differ_trans: forall s1 s2 s3 r,
    only_differ s1 r s2 ->
    only_differ s2 r s3 ->
    only_differ s1 r s3.
  Proof. state_calc. Qed.

  Lemma undef_shrink: forall st vs1 vs2,
    undef st vs1 ->
    subset vs2 vs1 ->
    undef st vs2.
  Proof. state_calc. Qed.

  Lemma only_differ_subset: forall s1 s2 r1 r2,
    subset r1 r2 ->
    only_differ s1 r1 s2 ->
    only_differ s1 r2 s2.
  Proof. state_calc. Qed.

  Lemma extends_if_only_differ_in_undef: forall s1 s2 s vs,
    extends s1 s ->
    undef s vs ->
    only_differ s1 vs s2 ->
    extends s2 s.
  Proof. state_calc. Qed.

  Lemma extends_if_only_differ_is_undef: forall s1 s2 vs,
    undef s1 vs ->
    only_differ s1 vs s2 ->
    extends s2 s1.
  Proof. state_calc. Qed.

  Lemma extends_put_same: forall s1 s2 x v,
    extends s2 s1 ->
    extends (put s2 x v) (put s1 x v).
  Proof. state_calc. Qed.

  Lemma only_differ_get_unchanged: forall s1 s2 x v d,
    get s1 x = v ->
    only_differ s1 d s2 ->
    ~ x \in d ->
    get s2 x = v.
  Proof. state_calc. Qed.

  Lemma only_differ_put: forall s (d: vars) x v,
    x \in d ->
    only_differ s d (put s x v).
  Proof. state_calc. Qed.

End Tests.
