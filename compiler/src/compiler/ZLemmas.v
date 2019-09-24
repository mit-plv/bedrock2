Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Z.BitOps.
Require Import coqutil.Z.bitblast.

Local Open Scope Z_scope.
Local Open Scope bool_scope.

Lemma mod0_divisible_modulo: forall a m n,
    0 < n ->
    0 < m ->
    Z.divide n m ->
    a mod m = 0 ->
    a mod n = 0.
Proof.
  intros.
  unfold Z.divide in H1. destruct H1 as [z H1].
  assert (z < 0 \/ z = 0 \/ 0 < z) as C by blia. destruct C as [C | [ C | C] ].
  - exfalso. Lia.nia.
  - exfalso. Lia.nia.
  - rewrite Z.mul_comm in H1. subst m.
    rewrite Z.rem_mul_r in H2 by blia.
    assert (a mod n < 0 \/ a mod n = 0 \/ 0 < a mod n) as D by blia. destruct D as [D | [D | D ] ].
    + exfalso. pose proof (Z.mod_pos_bound a n H). blia.
    + assumption.
    + pose proof (Z.mod_pos_bound (a / n) z C). exfalso. Lia.nia.
Qed.

Lemma mod_mod_remove_outer: forall a m n,
    0 < m < n ->
    n mod m = 0 ->
    (a mod m) mod n = a mod m.
Proof.
  intros *. intros [A B] C. apply Z.mod_small.
  pose proof (Z.mod_pos_bound a m A). blia.
Qed.

Lemma mod_mod_remove_inner: forall a m n,
    0 < n < m ->
    m mod n = 0 ->
    (a mod m) mod n = a mod n.
Proof.
  intros. rewrite <- Znumtheory.Zmod_div_mod; try blia.
  unfold Z.divide.
  apply Zmod_divides in H0; [|blia].
  destruct H0. subst m.
  exists x. blia.
Qed.

Lemma div_mul_same: forall a b,
    b <> 0 ->
    a / b * b = a - a mod b.
Proof.
  intros.
  pose proof (Zmod_eq_full a b H).
  blia.
Qed.

Lemma sub_mod_exists_q: forall v m,
    0 < m ->
    exists q, v - v mod m = m * q.
Proof.
  intros.
  apply (Zmod_divides (v - v mod m) m); [blia|].
  rewrite <- Zminus_mod_idemp_l.
  rewrite Z.sub_diag.
  rewrite Z.mod_0_l; blia.
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
  do 2 rewrite <- div_mul_same by (apply Z.pow_nonzero; blia).
  rewrite <-! Z.land_ones by blia.
  rewrite <-! Z.shiftl_mul_pow2 by blia.
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
