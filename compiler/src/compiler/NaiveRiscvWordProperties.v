Require Import Coq.ZArith.ZArith.
From Stdlib Require Import Zmod.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.BitOps coqutil.Z.ZLib.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.destr.
Require Import compiler.RiscvWordProperties.
Require coqutil.Word.Naive.

Local Open Scope Z_scope.

Section NaiveRiscvWord.
  Context (log2width: nat).

  Instance word_ok: word.ok (Naive.word (2 ^ Z.of_nat log2width)).
    apply Naive.ok.
    apply Z.pow2_pos.
    apply Nat2Z.is_nonneg.
  Qed.

  Instance naive_word_riscv_ok: word.riscv_ok (Naive.word (2 ^ Z.of_nat log2width)).
    assert (width_bounds: 0 < 2 ^ Z.of_nat log2width < 2 ^ 2 ^ Z.of_nat log2width). {
      split. {
        apply Z.pow2_pos. lia.
      }
      apply Z.log2_lt_pow2; [lia|].
      rewrite Z.log2_pow2 by lia.
      assert (log2width = 0 \/ 0 < log2width)%nat as Hc by lia.
      destruct Hc; [subst; reflexivity|].
      apply Z.log2_lt_pow2. 1: lia.
      apply Z.log2_lt_lin. lia.
    }
    constructor; intros.

    (* The three shifts: both sides shift by the same amount. *)
    1-3: cbv [word.sru word.slu word.srs word.of_Z word.unsigned Naive.word Naive.gen_word];
      f_equal;
      pose proof (Zmod.unsigned_pos_bound z ltac:(lia)) as R1;
      pose proof (Z.mod_pos_bound (Zmod.unsigned z) (2 ^ Z.of_nat log2width) ltac:(lia)) as R2;
      rewrite Z.log2_pow2 by lia;
      rewrite Zmod.unsigned_of_Z, (Z.mod_small (_ mod _)) by lia;
      destr (Zmod.unsigned z <? 2 ^ Z.of_nat log2width);
      [ rewrite Z.mod_small by lia;
        destr (Zmod.unsigned z <? 2 ^ Z.of_nat log2width); [reflexivity | exfalso; lia]
      | destr (Zmod.unsigned z mod 2 ^ Z.of_nat log2width <? 2 ^ Z.of_nat log2width); [|exfalso; lia];
        cbv [Naive.adjust_too_big_shift_amount Naive.default_special_case_handlers];
        rewrite Z.log2_pow2 by lia; reflexivity ].

    - destr (word.eqb z (word.of_Z 0)); [|reflexivity].
      cbv [word.divu word.of_Z Naive.word Naive.gen_word].
      rewrite Zmod.of_Z_0, Zmod.udiv_0_r.
      apply Zmod.unsigned_inj.
      rewrite Zmod.unsigned_m1_pos, Zmod.unsigned_of_Z_small; lia.

    - destr (word.eqb z (word.of_Z 0)); [|reflexivity].
      cbv [word.modu word.of_Z Naive.word Naive.gen_word].
      rewrite Zmod.of_Z_0, Zmod.umod_0_r.
      reflexivity.
  Qed.
End NaiveRiscvWord.
