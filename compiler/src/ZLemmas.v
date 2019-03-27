Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import coqutil.Z.BitOps.
Require Import coqutil.Z.bitblast.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma mod_mod_remove_outer: forall a m n,
    0 < m < n ->
    n mod m = 0 ->
    (a mod m) mod n = a mod m.
Proof.
  intros *. intros [A B] C. apply Z.mod_small.
  pose proof (Z.mod_pos_bound a m A). lia.
Qed.

Lemma mod_mod_remove_inner: forall a m n,
    0 < n < m ->
    m mod n = 0 ->
    (a mod m) mod n = a mod n.
Proof.
  intros. rewrite <- Znumtheory.Zmod_div_mod; try lia.
  unfold Z.divide.
  apply Zmod_divides in H0; [|lia].
  destruct H0. subst m.
  exists x. lia.
Qed.

Lemma div_mul_same: forall a b,
    b <> 0 ->
    a / b * b = a - a mod b.
Proof.
  intros.
  pose proof (Zmod_eq_full a b H).
  lia.
Qed.

Lemma sub_mod_exists_q: forall v m,
    0 < m ->
    exists q, v - v mod m = m * q.
Proof.
  intros.
  apply (Zmod_divides (v - v mod m) m); [lia|].
  rewrite <- Zminus_mod_idemp_l.
  rewrite Z.sub_diag.
  rewrite Z.mod_0_l; lia.
Qed.

Lemma shiftr_spec'': forall a n m : Z,
    Z.testbit (Z.shiftr a n) m = (0 <=? m) &&  Z.testbit a (m + n).
Proof.
  intros.
  destruct (Z.leb_spec 0 m).
  - apply Z.shiftr_spec. assumption.
  - rewrite Z.testbit_neg_r; trivial.
Qed.

Lemma shiftr_spec': forall a n m : Z,
    Z.testbit (Z.shiftr a n) m = negb (m <? 0) &&  Z.testbit a (m + n).
Proof.
  intros.
  destruct (Z.ltb_spec m 0).
  - rewrite Z.testbit_neg_r; trivial.
  - apply Z.shiftr_spec. assumption.
Qed.

Definition mask(x start eend: Z): Z :=
  (x - x mod 2 ^ start) mod 2 ^ eend.

Lemma mask_app_plus: forall v i j k,
    0 <= i ->
    i <= j ->
    j <= k ->
    mask v i j + mask v j k = mask v i k.
Proof.
  intros. unfold mask.
  do 2 rewrite <- div_mul_same by (apply Z.pow_nonzero; lia).
  rewrite <-! Z.land_ones by lia.
  rewrite <-! Z.shiftl_mul_pow2 by lia.
  rewrite <- or_to_plus; Z.bitblast.
Qed.

Ltac simpl_pow2_products :=
  repeat match goal with
         | |- context [ 2 ^ ?a * 2 ^ ?b ] =>
           match isZcst a with true => idtac end;
           match isZcst b with true => idtac end;
           let c := eval cbv in (a + b) in change (2 ^ a * 2 ^ b) with (2 ^ c)
         end.

Ltac simpl_Zcsts :=
  repeat match goal with
         | |- context [?op ?a ?b] =>
           match isZcst a with true => idtac end;
           match isZcst b with true => idtac end;
           match op with
           | Z.add => idtac
           | Z.sub => idtac
           | Z.mul => idtac
           end;
           let r := eval cbv in (op a b) in change (op a b) with r
         end.
