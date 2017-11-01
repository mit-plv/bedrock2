Require Import lib.LibTactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import compiler.Axioms.
Require Import compiler.Common.

Section StateCalculus.

  Context {var: Type}. (* variable name (key) *)
  Context {dec_eq_var: DecidableEq var}.
  Context {val: Type}. (* value *)
  Context {state: Type}.
  Context {stateMap: compiler.Common.Map state var val}.

  Definition extends(s1 s2: state) := forall x v, get s2 x = Some v -> get s1 x = Some v.

  Lemma extends_refl: forall s, extends s s.
  Proof. unfold extends. firstorder. Qed.

  Lemma put_extends: forall s x v,
    extends (put s x v) s.
  Proof. unfold extends. intros. Abort.

  (* models a set of vars *)
  Definition vars := var -> Prop.

  Definition vars_empty: vars := fun _ => False.

  Definition vars_one(x: var): vars := fun y => x = y.

  Definition vars_union(vs1 vs2: vars): vars := fun x => vs1 x \/ vs2 x.

  Definition vars_add(vs: vars)(new: var): vars := vars_union vs (vars_one new).

  Definition only_differ(s1: state)(vs: vars)(s2: state) :=
    forall x, vs x \/ get s1 x = get s2 x.

  Lemma only_differ_union_l: forall s1 s2 r1 r2,
    only_differ s1 r1 s2 ->
    only_differ s1 (vars_union r1 r2) s2.
  Proof. firstorder. Qed.

  Lemma only_differ_union_r: forall s1 s2 r1 r2,
    only_differ s1 r2 s2 ->
    only_differ s1 (vars_union r1 r2) s2.
  Proof. firstorder. Qed.

  Lemma only_differ_one: forall s x v,
    only_differ s (vars_one x) (put s x v).
  Proof.
    cbv [only_differ vars_one]. intros. destruct (dec (x = x0)); [ auto | ].
    right. symmetry. apply get_put_diff. assumption.
  Qed.

  Lemma only_differ_refl: forall s1 r,
    only_differ s1 r s1.
  Proof. firstorder. Qed.

  Lemma only_differ_sym: forall s1 s2 r,
    only_differ s1 r s2 ->
    only_differ s2 r s1.
  Proof. firstorder. Qed.

  Lemma only_differ_trans: forall s1 s2 s3 r,
    only_differ s1 r s2 ->
    only_differ s2 r s3 ->
    only_differ s1 r s3.
  Proof.
    unfold only_differ. introv E1 E2. intro x.
    specialize (E1 x). specialize (E2 x).
    destruct E1; [auto|]. destruct E2; [auto|]. right. congruence.
  Qed.

  Definition undef(s: state)(vs: vars) := forall x, vs x -> get s x = None.

  Definition subset(vs1 vs2: vars) := forall x, vs1 x -> vs2 x.

  Lemma undef_shrink: forall st vs1 vs2,
    undef st vs1 ->
    subset vs2 vs1 ->
    undef st vs2.
  Proof. unfold undef, subset. firstorder. Qed.

  Lemma only_differ_subset: forall s1 s2 r1 r2,
    subset r1 r2 ->
    only_differ s1 r1 s2 ->
    only_differ s1 r2 s2.
  Proof.
    unfold subset, only_differ. intros. firstorder.
  Qed.

  Lemma extends_if_only_differ_in_undef: forall s1 s2 s vs,
    extends s1 s ->
    undef s vs ->
    only_differ s1 vs s2 ->
    extends s2 s.
  Proof.
    unfold extends, undef, only_differ.
    introv E U O G.
    specialize (O x). destruct O as [O | O].
    - specialize (U _ O). congruence. (* contradiction *)
    - rewrite <- O. apply E. assumption.
  Qed.

  Lemma extends_if_only_differ_is_undef: forall s1 s2 vs,
    undef s1 vs ->
    only_differ s1 vs s2 ->
    extends s2 s1.
  Proof.
    intros. eapply extends_if_only_differ_in_undef; [eapply extends_refl | eassumption..].
  Qed.

  Lemma extends_put_same: forall s1 s2 x v,
    extends s2 s1 ->
    extends (put s2 x v) (put s1 x v).
  Proof.
    unfold extends. introv E G.
    destruct (dec (x = x0)).
    - subst x0. rewrite get_put_same in G. inversion G. subst v0; clear G.
      apply get_put_same.
    - rewrite get_put_diff by assumption.
      rewrite get_put_diff in G by assumption. auto.
  Qed.

  Lemma only_differ_get_unchanged: forall s1 s2 x v d,
    get s1 x = v ->
    only_differ s1 d s2 ->
    ~ d x ->
    get s2 x = v.
  Proof.
    introv G D N.
    unfold only_differ in D. destruct (D x); congruence.
  Qed.

  Lemma only_differ_put: forall s (d: vars) x v,
    d x ->
    only_differ s d (put s x v).
  Proof.
    unfold only_differ. intros.
    destruct (dec (x = x0)).
    - subst x0. left. assumption.
    - right. rewrite get_put_diff; auto.
  Qed.

End StateCalculus.
