Require Import Coq.micromega.Lia.
(*the library would generalize over 4, and have good enough automation to not require these specialized lemmas*)
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Z.Lia.
Require Znumtheory.

Lemma mod4_0_add: forall (x y: Z),
    x mod 4 = 0 ->
    y mod 4 = 0 ->
    (x + y) mod 4 = 0.
Proof.
  intros *. intros Hx Hy.
  rewrite Zplus_mod. rewrite Hx, Hy. reflexivity.
Qed.

Lemma mod4_0_sub: forall (x y: Z),
    x mod 4 = 0 ->
    y mod 4 = 0 ->
    (x - y) mod 4 = 0.
Proof.
  intros *. intros Hx Hy.
  rewrite Zminus_mod. rewrite Hx, Hy. reflexivity.
Qed.

Lemma mod4_mul4_l: forall (x: Z),
    (4 * x) mod 4 = 0.
Proof. intros. rewrite Z.mul_comm. rewrite Z.mod_mul; lia. Qed.

Lemma mod4_mul4_r: forall (x: Z),
    (x * 4) mod 4 = 0.
Proof. intros. rewrite Z.mod_mul; lia. Qed.

Lemma mod4_mul_l: forall (x y: Z),
    x mod 4 = 0 ->
    (x * y) mod 4 = 0.
Proof.
  intros.
  rewrite <- Z.mul_mod_idemp_l by lia.
  rewrite H.
  rewrite Z.mul_0_l.
  reflexivity.
Qed.

Lemma mod4_mul_r: forall (x y: Z),
    y mod 4 = 0 ->
    (x * y) mod 4 = 0.
Proof.
  intros.
  rewrite <- Z.mul_mod_idemp_r by lia.
  rewrite H.
  rewrite Z.mul_0_r.
  reflexivity.
Qed.

Lemma mod_pow2_mod4: forall x p,
    2 <= p ->
    (x mod 2 ^ p) mod 4 = x mod 4.
Proof.
  intros.
  rewrite <- Znumtheory.Zmod_div_mod.
  - reflexivity.
  - reflexivity.
  - apply Z.pow_pos_nonneg; lia.
  - unfold Z.divide.
    exists (2 ^ p / 2 ^ 2).
    rewrite <- Z.pow_sub_r by lia.
    change 4 with (2 ^ 2).
    rewrite <- Z.pow_add_r by lia.
    f_equal.
    lia.
Qed.

Lemma mod4_0_mod_pow2: forall (x p: Z),
    x mod 4 = 0 ->
    (x mod 2 ^ p) mod 4 = 0.
Proof.
  intros.
  assert (p < 0 \/ p = 0 \/ p = 1 \/ 2 <= p) as C by lia. destruct C as [C | [C | [C | C]]].
  - rewrite Z.pow_neg_r by assumption. now rewrite Zmod_0_r.
  - subst p. simpl. rewrite Z.mod_1_r. reflexivity.
  - subst p. change (2 ^ 1) with 2.
    rewrite Z.mod_eq in H by lia.
    replace x with (x / 4 * 2 * 2) by lia.
    rewrite Z.mod_mul by lia.
    reflexivity.
  - rewrite mod_pow2_mod4; assumption.
Qed.

Lemma mod4_0_4: 4 mod 4 = 0. Proof. reflexivity. Qed.

Lemma mod4_0_opp: forall z,
    z mod 4 = 0 ->
    - z mod 4 = 0.
Proof.
  intros. Z.div_mod_to_equations. lia.
Qed.

#[global] Hint Resolve
     mod4_0_mod_pow2
     mod4_0_add
     mod4_0_sub
     mod4_0_mod_pow2
     mod4_mul4_l
     mod4_mul4_r
     mod4_0_4
     mod4_mul_l
     mod4_mul_r
     mod4_0_opp
  : mod4_0_hints.

Ltac solve_mod4_0 := auto 30 with mod4_0_hints.
