Require Import lib.LibTactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import compiler.Axioms.
Require Import compiler.Common.

Section StateCalculus.

  Context {var: Type}. (* variable name (key) *)
  Context {dec_eq_var: DecidableEq var}.
  Context {val: Type}. (* value *)
  Context {dec_eq_val: DecidableEq val}.
  Context {state: Type}.
  Context {stateMap: Map state var val}.

  (* models a set of vars *)
  Definition vars := var -> Prop.

  (* definitions which need to know that sets are modeled as functions and access elements
     (don't unfold) *)

  Definition dom(s: state): vars := fun x => get s x <> None.

  (* the domain on which s1 and s2 differ *)
  Definition domdiff(s1 s2: state): vars := fun x => get s1 x <> get s2 x.

  Definition is_empty(v: vars) := forall x, ~ x \in v.

  Definition complement(v: vars) := fun x => ~ x \in v.

  Hint Unfold dom domdiff is_empty complement : unfold00.

  (* derived definitions *)

  Definition subset(vs1 vs2: vars) := is_empty (intersect vs1 (complement vs2)).

  Definition extends(s1 s2: state) := is_empty (intersect (domdiff s1 s2) (dom s2)).

  Definition only_differ(s1: state)(vs: vars)(s2: state) :=
    subset (domdiff s1 s2) vs.

  Definition undef(s: state)(vs: vars) := is_empty (intersect (dom s) vs).

  Hint Unfold subset extends only_differ undef : unfold_state_calculus.

  Ltac unf := repeat autounfold with unfold00 unfold_state_calculus.

  Ltac unf1 := repeat autounfold with unfold_state_calculus.

  Ltac state_calc := repeat autounfold with unfold_state_calculus; firstorder.

  Lemma extends_refl: forall s, extends s s.
  Proof. state_calc. Qed.

(* should be part of typeclass (spec)
  Lemma in_union: forall x A B, x \in union A B <-> x \in A \/ x \in B.
  Proof. intros; split; cbv. unfold union.
*)

  Lemma only_differ_union_l: forall s1 s2 r1 r2,
    only_differ s1 r1 s2 ->
    only_differ s1 (union r1 r2) s2.
  Proof. state_calc. Qed.

  Lemma only_differ_union_r: forall s1 s2 r1 r2,
    only_differ s1 r2 s2 ->
    only_differ s1 (union r1 r2) s2.
  Proof. state_calc. Qed.

  Lemma domdiff_put_general: forall s1 s2 x v,
    domdiff s1 (put s2 x v) =
      union (domdiff s1 s2 ) (if dec (get s1 x = Some v) then empty_set else singleton_set x).
  Proof.
    cbv -[get put dec]. intros. destruct_one_match; extensionality y; apply prop_ext; split;
      (destruct (dec (x = y)); [subst; rewrite get_put_same | rewrite get_put_diff by assumption]).
  Abort.

  Lemma domdiff_put: forall s1 x v,
    domdiff s1 (put s1 x v) = if dec (get s1 x = Some v) then empty_set else singleton_set x.
  Proof.
    cbv -[get put dec]. intros. destruct_one_match; extensionality y; apply prop_ext; split;
      destruct (dec (x = y)); subst; try rewrite get_put_same; auto;
      rewrite get_put_diff by assumption; auto.
    intro H. exfalso. auto.
  Qed.

  (* TODO make this nicer *)
  Lemma only_differ_one: forall s x v,
    only_differ s (singleton_set x) (put s x v).
  Proof. unf1.
    intros.
    replace (domdiff s (put s x v))
       with (if dec (get s x = Some v) then empty_set else singleton_set x).
    - destruct_one_match; firstorder.
    - symmetry. apply domdiff_put. 
  Qed. (*
    cbv [only_differ vars_one]. intros. destruct (dec (x = x0)); [ auto | ].
    right. symmetry. apply get_put_diff. assumption.
  Qed.*)

  Lemma only_differ_refl: forall s1 r,
    only_differ s1 r s1.
  Proof. state_calc. Qed.

  Lemma only_differ_sym: forall s1 s2 r,
    only_differ s1 r s2 ->
    only_differ s2 r s1.
  Proof. state_calc. Qed.

  Lemma elim_impl: forall P Q,
    ~ P \/ Q -> P -> Q.
  Proof. firstorder. Qed.
  Lemma elim_impl2: forall P Q R,
    ~ P \/ ~ Q \/ R -> P -> Q -> R.
  Proof. firstorder. Qed.

(*
  Lemma not_forall: forall {T: Type} (x: T) (P: T -> Prop),
    (~ forall x, ~ P x) <-> exists x, P x.
  Proof. split. *)
  Lemma non_empty_classical: forall v,
    ~ is_empty v <-> exists x, x \in v. Admitted.

  Lemma nonempty_or: forall v1 v2,
    (~ is_empty v1) \/ (~ is_empty v2) <-> ~ is_empty (union v1 v2).
  Proof.
    split; [cbv|]; intros.
    - destruct H.
      + apply H. intros. eapply H0. eauto.
      + apply H. intros. eapply H0. eauto.
    - rewrite! non_empty_classical in *. destruct H as [x H]. cbv in H.
      destruct H; eauto.
  Qed.

(*  Lemma non_empty_complement: forall v,
    (~ is_empty v) *)

  Lemma only_differ_trans: forall s1 s2 s3 r,
    only_differ s1 r s2 ->
    only_differ s2 r s3 ->
    only_differ s1 r s3.
  Proof.
    unf1. intros s1 s2 s3 r. apply elim_impl2.
    match goal with |- ?P \/ ?Q \/ ?R => cut ((P \/ Q) \/ R); [tauto|] end.
    rewrite nonempty_or.
  Abort. (*
    unfold only_differ. introv E1 E2. intro x.
    specialize (E1 x). specialize (E2 x).
    destruct E1; [auto|]. destruct E2; [auto|]. right. congruence.
  Qed.*)

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
    ~ x \in d ->
    get s2 x = v.
  Proof.
    introv G D N.
    unfold only_differ in D. destruct (D x); congruence.
  Qed.

  Lemma only_differ_put: forall s (d: vars) x v,
    x \in d ->
    only_differ s d (put s x v).
  Proof.
    unfold only_differ. intros.
    destruct (dec (x = x0)).
    - subst x0. left. assumption.
    - right. rewrite get_put_diff; auto.
  Qed.

End StateCalculus.
