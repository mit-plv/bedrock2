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

  Instance kami_word_riscv_ok: word.riscv_ok (KamiWord.word (2 ^ log2width)).
    constructor;
      intros;
      unfold word.sru, word.slu, word.srs, word.mulhuu, word.divu, word.modu, KamiWord.word.

    - pose proof (word.unsigned_range y) as R1.
      pose proof (word.unsigned_range z) as R2.
      unfold word.unsigned in *. cbn in *.
      remember (kunsigned y) as a. remember (kunsigned z) as b. clear Heqa Heqb y z.
      change kunsigned with (@word.unsigned _ (KamiWord.word (2 ^ log2width))).
      change kofZ with (@word.of_Z _ (KamiWord.word (2 ^ log2width))) at 2.
      rewrite word.unsigned_of_Z. unfold word.wrap.
      rewrite Z.log2_pow2 by assumption.
      rewrite mod_mod_remove_inner.
      + rewrite Z.mod_mod. 1: reflexivity.
        apply Z.pow_nonzero. 1: congruence. assumption.
      + split; [assumption|].
        apply Z.pow_gt_lin_r; blia.
      + apply Z.mod_divide.
        * apply Z.pow_nonzero. 1: congruence. assumption.
        * unfold Z.divide.
          exists (2 ^ (2 ^ log2width - log2width)).
          rewrite <- Z.pow_add_r.
          { f_equal. blia. }
          { pose proof (Z.pow_gt_lin_r 2 log2width). blia. }
          { blia. }

    - pose proof (word.unsigned_range y) as R1.
      pose proof (word.unsigned_range z) as R2.
      unfold word.unsigned in *. cbn in *.
      remember (kunsigned y) as a. remember (kunsigned z) as b. clear Heqa Heqb y z.
      change kunsigned with (@word.unsigned _ (KamiWord.word (2 ^ log2width))).
      change kofZ with (@word.of_Z _ (KamiWord.word (2 ^ log2width))) at 2.
      rewrite word.unsigned_of_Z. unfold word.wrap.
      rewrite Z.log2_pow2 by assumption.
      rewrite mod_mod_remove_inner.
      + rewrite Z.mod_mod. 1: reflexivity.
        apply Z.pow_nonzero. 1: congruence. assumption.
      + split; [assumption|].
        apply Z.pow_gt_lin_r; blia.
      + apply Z.mod_divide.
        * apply Z.pow_nonzero. 1: congruence. assumption.
        * unfold Z.divide.
          exists (2 ^ (2 ^ log2width - log2width)).
          rewrite <- Z.pow_add_r.
          { f_equal. blia. }
          { pose proof (Z.pow_gt_lin_r 2 log2width). blia. }
          { blia. }

    - pose proof (word.signed_range y) as R1.
      pose proof (word.unsigned_range z) as R2.
      unfold word.signed, word.unsigned in *. cbn in *.
      remember (ksigned y) as a. remember (kunsigned z) as b. clear Heqa Heqb y z.
      change kunsigned with (@word.unsigned _ (KamiWord.word (2 ^ log2width))).
      change kofZ with (@word.of_Z _ (KamiWord.word (2 ^ log2width))) at 2.
      rewrite word.unsigned_of_Z. unfold word.wrap.
      rewrite Z.log2_pow2 by assumption.
      rewrite mod_mod_remove_inner.
      + rewrite Z.mod_mod. 1: reflexivity.
        apply Z.pow_nonzero. 1: congruence. assumption.
      + split; [assumption|].
        apply Z.pow_gt_lin_r; blia.
      + apply Z.mod_divide.
        * apply Z.pow_nonzero. 1: congruence. assumption.
        * unfold Z.divide.
          exists (2 ^ (2 ^ log2width - log2width)).
          rewrite <- Z.pow_add_r.
          { f_equal. blia. }
          { pose proof (Z.pow_gt_lin_r 2 log2width). blia. }
          { blia. }

    - change kofZ with (@word.of_Z _ (KamiWord.word (2 ^ log2width))).
      apply word.of_Z_inj_mod.
      rewrite bitSlice_alt; cycle 1. {
        pose proof (Z.pow_gt_lin_r 2 log2width). blia.
      }
      unfold bitSlice'.
      pose proof (word.unsigned_range y) as R1.
      pose proof (word.unsigned_range z) as R2.
      unfold word.unsigned in *. cbn in *.
      remember (kunsigned y) as a. remember (kunsigned z) as b. clear Heqa Heqb y z.
      ring_simplify (2 * 2 ^ log2width - 2 ^ log2width).
      rewrite Z.mod_mod; cycle 1. {
        apply Z.pow_nonzero; blia.
      }
      reflexivity.

    - unfold word.eqb.
      match goal with
      | |- context [ _ =? ?zero ] => replace zero with 0; cycle 1
      end. {
        unfold word.of_Z, kunsigned. cbn.
        rewrite Word.wordToN_wzero'.
        reflexivity.
      }
      unfold riscvZdivu.
      destr (kunsigned z =? 0); reflexivity.

    - unfold word.eqb.
      match goal with
      | |- context [ _ =? ?zero ] => replace zero with 0; cycle 1
      end. {
        unfold word.of_Z, kunsigned. cbn.
        rewrite Word.wordToN_wzero'.
        reflexivity.
      }
      unfold riscvZmodu.
      destr (kunsigned z =? 0). 2: reflexivity.
      rewrite <- (word.of_Z_unsigned y) at 1.
      reflexivity.
  Qed.

End KamiRiscvWord.
