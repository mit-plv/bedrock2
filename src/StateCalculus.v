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
    x \in @singleton_set vars _ _ y <-> x = y.
    (* explicitly write vars, because otherwise (var -> Prop) is inferred and rewrite doesn't work *)
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
Ltac unf := repeat autounfold with unfold_state_calculus in *.

Hint Rewrite @intersect_spec @union_spec @diff_spec @singleton_set_spec : rewrite_set_op_specs.

(* bad attempt to get the DecidableEq, it might not be in the context, but global *)
Ltac rewrite_get_put_bad :=
  repeat match goal with
  | D: DecidableEq ?Var |- context [@get _ ?Var _ _ (put _ _ _) _] =>
     rewrite (@get_put Var D) in *
  | D: DecidableEq ?Var, _: context [@get _ ?Var _ _ (put _ _ _) _] |- _ =>
     rewrite (@get_put Var D) in *
  end.

Ltac rewrite_get_put :=
  erewrite? get_put in *;
  (* the above line is sometimes not enough, so be more explicit: *)
  repeat match goal with
  | H: _ |- _ => erewrite? get_put in H
  end.

Ltac state_calc :=
  unf; intros; autorewrite with rewrite_set_op_specs in *; rewrite_get_put;
  repeat match goal with
  | x: ?T, H: forall (y: ?T), _ |- _ => unique pose proof (H x)
  end;
  repeat (intuition (auto || congruence) || destruct_one_dec_eq).
