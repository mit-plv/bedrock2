Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.BitOps.
Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.destr.
Require Import compiler.RiscvWordProperties.
Require Import compiler.ZLemmas.
Require Import processor.KamiWord.

Open Scope Z_scope.

Section KamiRiscvWord.
  Context {log2width: Z}.
  Context (log2width_nonneg: 0 <= log2width).

  Context (width_nonneg: 0 < 2 ^ log2width).

  Instance kami_word_ok: word.ok (KamiWord.word (2 ^ log2width)) := KamiWord.ok _ width_nonneg.

  Arguments Z.mul: simpl never.

  Lemma pow_pow_lt: 2 ^ log2width < 2 ^ 2 ^ log2width.
  Proof.
    apply Z.log2_lt_pow2; [blia|].
    rewrite Z.log2_pow2 by assumption.
    assert (Hc: log2width = 0 \/ 0 < log2width) by blia.
    destruct Hc; [subst; trivial|].
    apply Z.log2_lt_pow2; [assumption|].
    apply Z.log2_lt_lin; assumption.
  Qed.

  Lemma unsigned_of_Z_mod_idemp:
    forall z, word.unsigned (width:= 2 ^ log2width)
                            (word.of_Z (word.unsigned z mod 2 ^ log2width)) mod 2 ^ log2width =
              word.unsigned (width:= 2 ^ log2width) z mod 2 ^ log2width.
  Proof.
    intros.
    rewrite Z.mod_small.
    - rewrite word.unsigned_of_Z.
      cbv [word.wrap].
      rewrite Z.mod_small; [reflexivity|].
      split; [apply Z.mod_pos_bound; blia|].
      etransitivity; [apply Z.mod_pos_bound; blia|].
      apply pow_pow_lt.
    - rewrite word.unsigned_of_Z.
      cbv [word.wrap].
      rewrite Z.mod_small; [apply Z.mod_pos_bound; blia|].
      split; [apply Z.mod_pos_bound; blia|].
      etransitivity; [apply Z.mod_pos_bound; blia|].
      apply pow_pow_lt.
  Qed.

  Instance kami_word_riscv_ok: word.riscv_ok (KamiWord.word (2 ^ log2width)).
    constructor;
      intros;
      unfold word.sru, word.slu, word.srs, word.mulhuu, word.divu, word.modu, KamiWord.word.

    - pose proof (word.unsigned_range y) as R1.
      pose proof (word.unsigned_range z) as R2.
      rewrite Z.log2_pow2 by trivial.
      do 2 f_equal.
      change kunsigned with (word.unsigned (width:= 2 ^ log2width)).
      apply unsigned_of_Z_mod_idemp.

    - pose proof (word.unsigned_range y) as R1.
      pose proof (word.unsigned_range z) as R2.
      rewrite Z.log2_pow2 by trivial.
      do 2 f_equal.
      change kunsigned with (word.unsigned (width:= 2 ^ log2width)).
      apply unsigned_of_Z_mod_idemp.

    - pose proof (word.signed_range y) as R1.
      pose proof (word.unsigned_range z) as R2.
      rewrite Z.log2_pow2 by trivial.
      do 2 f_equal.
      change kunsigned with (word.unsigned (width:= 2 ^ log2width)).
      apply unsigned_of_Z_mod_idemp.

    - destruct (word.eqb _ _) eqn:Heq; [|reflexivity].
      apply word.eqb_true in Heq; subst z.
      cbv [riscvZdivu].
      match goal with
      | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
      end.
      + reflexivity.
      + change kunsigned with (word.unsigned (width:= 2 ^ log2width)) in n.
        rewrite word.unsigned_of_Z_0 in n.
        exfalso; auto.

    - destruct (word.eqb _ _) eqn:Heq; [|reflexivity].
      apply word.eqb_true in Heq; subst z.
      cbv [riscvZmodu].
      match goal with
      | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
      end.
      + change kunsigned with (word.unsigned (width:= 2 ^ log2width)).
        change kofZ with (word.of_Z (width:= 2 ^ log2width)).
        apply eq_sym, word.of_Z_unsigned.
      + change kunsigned with (word.unsigned (width:= 2 ^ log2width)) in n.
        rewrite word.unsigned_of_Z_0 in n.
        exfalso; auto.
  Qed.

End KamiRiscvWord.
