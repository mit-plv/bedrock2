Require Import Rupicola.Lib.Api.
Require Export
        bedrock2.BasicC32Semantics.

Section BitOps.
  Lemma word_sru_div_2 z:
    0 <= z < 2 ^ 32 ->
    word.of_Z (z / 2) = word.sru (word := word) (word.of_Z z) (word.of_Z 1).
  Proof.
    intros; rewrite <- (Z.shiftr_div_pow2 _ 1), word.morph_shiftr; reflexivity || lia.
  Qed.

  Lemma dexpr_compile_div_2 {mem locals e z}:
    0 <= z < 2 ^ 32 ->
    WeakestPrecondition.dexpr
      mem locals e (word.sru (word := word) (word.of_Z z) (word.of_Z 1)) ->
    WeakestPrecondition.dexpr
      mem locals e (word.of_Z (z / 2)).
  Proof. intros; rewrite word_sru_div_2; eassumption. Qed.

  Lemma word_and_odd z:
    word.b2w (Z.odd z) = word.and (word := word) (word.of_Z z) (word.of_Z 1).
  Proof.
    rewrite <- word.morph_and.
    rewrite (Z.land_ones _ 1), Zmod_odd by lia.
    destruct Z.odd; reflexivity.
  Qed.

  Lemma dexpr_compile_odd {mem locals e z}:
    WeakestPrecondition.dexpr
      mem locals e (word.and (word := word) (word.of_Z z) (word.of_Z 1)) ->
    WeakestPrecondition.dexpr
      mem locals e (word.b2w (Z.odd z)).
  Proof. intros; rewrite word_and_odd; eassumption. Qed.

  Lemma word_not_xor (w: word):
    word.not w = word.xor w (word.of_Z (-1)).
  Proof.
    rewrite <- (word.of_Z_unsigned w).
    rewrite <- word.morph_not, <- word.morph_xor.
    rewrite Z.lxor_m1_r; reflexivity.
  Qed.

  Lemma dexpr_compile_not {mem locals e} (w w': word):
    WeakestPrecondition.dexpr
      mem locals e (word.and (word.xor w (word.of_Z (-1))) w') ->
    WeakestPrecondition.dexpr
      mem locals e (word.and (word.not w) w').
  Proof. intros; rewrite word_not_xor; eassumption. Qed.
End BitOps.

Lemma odd_sub_pos z:
  0 <= z -> Z.odd z = true -> 0 <= z - 1.
Proof. destruct (Z.eq_dec z 0) as [-> | ]; simpl; lia. Qed.
