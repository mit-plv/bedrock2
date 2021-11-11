(*! IP Checksum, from https://www.rfc-editor.org/rfc/rfc1071 !*)
Require Import ZArith.
From coqutil Require Export
     Datatypes.List
     Byte
     Word.LittleEndianList.

Open Scope Z_scope.

Definition onec_add16 (z1 z2: Z) :=
  let sum := z1 + z2 in
  (Z.land sum 0xffff + (Z.shiftr sum 16)).

Definition ip_checksum (bs: list byte) :=
  let chk := List.fold_left onec_add16 (List.map le_combine (chunk 2 bs)) 0xffff in
  Z.land (Z.lnot chk) 0xffff.

From Rupicola Require Import Core.

Section Properties.
  Lemma Z_shiftr_0_le z n:
    0 <= n ->
    0 <= z < 2 ^ n ->
    Z.shiftr z n = 0.
  Proof.
    intros; rewrite Z.shiftr_div_pow2 by lia.
    apply Z.div_small; lia.
  Qed.

  Lemma mod_sub_1 z n :
    0 <= n ->
    n <= z < 2 * n ->
    z mod n = z - n.
  Proof.
    intros Hn (Hnz, Hzn); rewrite Z.mod_eq by lia.
    Z.div_mod_to_equations; cut (q = 1); nia.
  Qed.

  Lemma Z_shiftr_add_carry m n z1 z2:
    0 <= m <= n ->
    0 <= z1 < 2 ^ n ->
    0 <= z2 < 2 ^ n ->
    0 <= Z.shiftr (z1 + z2) m < 2 ^ (n - m + 1).
  Proof.
    intros.
    pose proof Z.pow_pos_nonneg 2 m ltac:(lia) ltac:(lia).
    intros; rewrite Z.shiftr_div_pow2 by lia;
      split; [apply Z.div_le_lower_bound | apply Z.div_lt_upper_bound]; try lia; [].
    rewrite <- Z.pow_add_r by lia;
      replace (m + (n - m + 1)) with (n + 1) by lia;
      rewrite Z.pow_add_r by lia.
    lia.
  Qed.

  Lemma onec_add16_loose_bounds z1 z2:
    0 <= z1 < 2 ^ 16 ->
    0 <= z2 < 2 ^ 16 ->
    0 <= onec_add16 z1 z2 < 2 ^ 32.
  Proof.
    intros; unfold onec_add16.
    pose proof (Z_land_leq_right (z1 + z2) 0xffff).
    pose proof Z_shiftr_add_carry 16 16 z1 z2.
    lia.
  Qed.

  Lemma onec_add16_bounds z1 z2:
    0 <= z1 < 2 ^ 16 ->
    0 <= z2 < 2 ^ 16 ->
    0 <= onec_add16 z1 z2 < 2 ^ 16.
  Proof.
    intros; unfold onec_add16.
    assert (0 <= z1 + z2 < 2 ^ 16 \/ 2 ^ 16 <= z1 + z2 < 2 * 2 ^ 16) as [hle | hgt] by lia;
      change 65535 with (Z.ones 16); rewrite Z.land_ones by lia.
    - rewrite Z.mod_small, Z_shiftr_0_le; lia.
    - pose proof Z_shiftr_add_carry 16 16 z1 z2; rewrite mod_sub_1; lia.
  Qed.

  Lemma onec_add16_iter_bounds a0 l:
    0 <= a0 < 2 ^ 16 ->
    List.Forall (fun x => 0 <= x < 2 ^ 16) l ->
    0 <= fold_left onec_add16 l a0 < 2 ^ 16.
  Proof.
    intros Ha0 Hl; apply fold_left_inv.
    - lia.
    - intros * Hb%(Forall_In Hl) Ha.
      pose proof onec_add16_bounds a b; lia.
  Qed.

  Lemma onec_add16_iter_loose_bounds a0 l:
    0 <= a0 < 2 ^ 16 ->
    List.Forall (fun x => 0 <= x < 2 ^ 16) l ->
    0 <= fold_left onec_add16 l a0 < 2 ^ 32.
  Proof.
    intros; pose proof onec_add16_iter_bounds a0 l; intuition lia.
  Qed.

  Lemma ip_checksum_bounds bs :
    0 <= ip_checksum bs < 2 ^ 16.
  Proof.
    unfold ip_checksum.
    change 65535 with (Z.ones 16); rewrite Z.land_ones by lia.
    apply Z.mod_pos_bound; lia.
  Qed.
End Properties.
