Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.BitOps.
Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.destr.
Require Import compiler.RiscvWordProperties.
Require Import compiler.ZLemmas.
Require Import processor.KamiWord.

Open Scope Z_scope.
Local Axiom TODO_andres: False.

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
      rewrite Z.log2_pow2 by trivial.
      f_equal.
      f_equal.
      case TODO_andres.

    - pose proof (word.unsigned_range y) as R1.
      pose proof (word.unsigned_range z) as R2.
      rewrite Z.log2_pow2 by trivial.
      f_equal.
      f_equal.
      case TODO_andres.

    - pose proof (word.signed_range y) as R1.
      pose proof (word.unsigned_range z) as R2.
      rewrite Z.log2_pow2 by trivial.
      f_equal.
      f_equal.
      case TODO_andres.

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

      - case TODO_andres.
      - case TODO_andres.
  (*
    - unfold Word.weqb.
      match goal with
      | |- context [Word. _ =? ?zero ] => replace zero with 0; cycle 1
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
      *)

  Qed.

End KamiRiscvWord.
