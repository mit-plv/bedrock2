Require Import compiler.Decidable.
Require Import compiler.util.Set.
Require Import compiler.util.Map.

Section Tests.

  Context {var: Type}. (* variable name (key) *)
  Context {dec_eq_var: DecidableEq var}.
  Context {val: Type}. (* value *)
  Context {dec_eq_val: DecidableEq val}.

  Context {stateMap: MapFunctions var val}.
  Notation state := (map var val).
  Context {varset: SetFunctions var}.
  Notation vars := (set var).

  Ltac t := map_solver var val.

  Lemma extends_refl: forall s, extends s s.
  Proof. t. Qed.

  Lemma extends_trans: forall s1 s2 s3,
      extends s1 s2 ->
      extends s2 s3 ->
      extends s1 s3.
  Proof. t. Qed.

  Lemma extends_intersect_map_l: forall r1 r2,
      extends r1 (intersect_map r1 r2).
  Proof. t. Qed.

  Lemma extends_intersect_map_r:
    forall r1 r2, extends r2 (intersect_map r1 r2).
  Proof. t. Qed.

  Lemma extends_intersect_map_lr: forall m11 m12 m21 m22,
      extends m11 m21 ->
      extends m12 m22 ->
      extends (intersect_map m11 m12) (intersect_map m21 m22).
  Proof. t. Qed.

  Lemma intersect_map_extends: forall m1 m2 m,
      extends m1 m ->
      extends m2 m ->
      extends (intersect_map m1 m2) m.
  Proof. t. Qed.

  Lemma only_differ_union_l: forall s1 s2 r1 r2,
    only_differ s1 r1 s2 ->
    only_differ s1 (union r1 r2) s2.
  Proof. t. Qed.

  Lemma only_differ_union_r: forall s1 s2 r1 r2,
    only_differ s1 r2 s2 ->
    only_differ s1 (union r1 r2) s2.
  Proof. t. Qed.

  Lemma only_differ_one: forall s x v,
    only_differ s (singleton_set x) (put s x v).
  Proof. t. Qed.

  Lemma only_differ_refl: forall s1 r,
    only_differ s1 r s1.
  Proof. t. Qed.

  Lemma only_differ_sym: forall s1 s2 r,
    only_differ s1 r s2 ->
    only_differ s2 r s1.
  Proof. t. Qed.

  Lemma only_differ_trans: forall s1 s2 s3 r,
    only_differ s1 r s2 ->
    only_differ s2 r s3 ->
    only_differ s1 r s3.
  Proof. t. Qed.

  Lemma undef_on_shrink: forall st vs1 vs2,
    undef_on st vs1 ->
    subset vs2 vs1 ->
    undef_on st vs2.
  Proof. t. Qed.

  Lemma only_differ_subset: forall s1 s2 r1 r2,
    subset r1 r2 ->
    only_differ s1 r1 s2 ->
    only_differ s1 r2 s2.
  Proof. t. Qed.

  Lemma extends_if_only_differ_in_undef: forall s1 s2 s vs,
    extends s1 s ->
    undef_on s vs ->
    only_differ s1 vs s2 ->
    extends s2 s.
  Proof. t. Qed.

  Lemma extends_if_only_differ_is_undef: forall s1 s2 vs,
    undef_on s1 vs ->
    only_differ s1 vs s2 ->
    extends s2 s1.
  Proof. t. Qed.

  Lemma extends_put_same: forall s1 s2 x v,
    extends s2 s1 ->
    extends (put s2 x v) (put s1 x v).
  Proof. t. Qed.

  Lemma reverse_get_put_diff: forall m v1 v2 k,
      v1 <> v2 ->
      reverse_get (put m k v1) v2 = reverse_get m v2.
  Proof.
    (* might not hold for an efficient implementation which restructures the map on "put" *)
  Abort.

  Lemma reverse_get_put: forall m v1 v2 k1,
      let q := reverse_get (put m k1 v1) v2 in
      ((exists k2, reverse_get m v2 = Some k2) /\
       ((exists k2, q = Some k2) \/ (q = Some k1 /\ v1 = v2))) \/
      (reverse_get m v1 = None /\ (q = if (dec (v1 = v2)) then Some k1 else None)).
  Proof.
    (* might hold, but who wants to use that? *)
  Abort.

  Lemma bw_extends_put_same: forall m1 m2 k v,
      bw_extends m1 m2 ->
      bw_extends (put (remove_by_value m1 v) k v) (put (remove_by_value m2 v) k v).
  Proof.
    unfold bw_extends.
    intros.
    apply reverse_get_Some in H0.
    destruct (dec (k = k0)).
    - subst k0.
      rewrite get_put_same in H0. inversion H0. subst v0.
      admit.
    - rewrite get_put_diff in H0 by assumption.
      rewrite get_remove_by_value in H0.
      destruct (dec (get m2 k0 = Some v)); [discriminate|].
      assert (v <> v0) by congruence.
  Abort.

  Lemma only_differ_get_unchanged: forall s1 s2 x v d,
    get s1 x = v ->
    only_differ s1 d s2 ->
    ~ x \in d ->
    get s2 x = v.
  Proof. t. Qed.

  Lemma only_differ_put: forall s (d: vars) x v,
    x \in d ->
    only_differ s d (put s x v).
  Proof. t. Qed.

End Tests.
