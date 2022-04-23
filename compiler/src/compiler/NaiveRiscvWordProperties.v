Require Import Coq.ZArith.ZArith.
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
    constructor;
      intros; cbn [word.sru  word.slu  word.srs  word.mulhuu  word.divu  word.modu
                   Naive.word Naive.gen_word].

    - pose proof (word.unsigned_range y) as R1.
      pose proof (word.unsigned_range z) as R2.
      pose proof (Z.mod_pos_bound (word.unsigned z) (2 ^ Z.of_nat log2width)) as R3.
      rewrite Z.log2_pow2 by lia.
      do 2 f_equal.
      change Naive.unsigned
        with (word.unsigned (word := (Naive.word (2 ^ Z.of_nat log2width)))).
      rewrite word.unsigned_of_Z_nowrap by lia.
      destr (word.unsigned z <? 2 ^ Z.of_nat log2width).
      + rewrite Z.mod_small by lia.
        destr (word.unsigned z <? 2 ^ Z.of_nat log2width).
        * reflexivity.
        * exfalso; lia.
      + destr (word.unsigned z mod 2 ^ Z.of_nat log2width <? 2 ^ Z.of_nat log2width).
        * cbn. rewrite Z.log2_pow2 by lia. reflexivity.
        * exfalso. lia.

    - pose proof (word.unsigned_range y) as R1.
      pose proof (word.unsigned_range z) as R2.
      pose proof (Z.mod_pos_bound (word.unsigned z) (2 ^ Z.of_nat log2width)) as R3.
      rewrite Z.log2_pow2 by lia.
      do 2 f_equal.
      change Naive.unsigned
        with (word.unsigned (word := (Naive.word (2 ^ Z.of_nat log2width)))).
      rewrite word.unsigned_of_Z_nowrap by lia.
      destr (word.unsigned z <? 2 ^ Z.of_nat log2width).
      + rewrite Z.mod_small by lia.
        destr (word.unsigned z <? 2 ^ Z.of_nat log2width).
        * reflexivity.
        * exfalso; lia.
      + destr (word.unsigned z mod 2 ^ Z.of_nat log2width <? 2 ^ Z.of_nat log2width).
        * cbn. rewrite Z.log2_pow2 by lia. reflexivity.
        * exfalso. lia.

    - pose proof (word.unsigned_range y) as R1.
      pose proof (word.unsigned_range z) as R2.
      pose proof (Z.mod_pos_bound (word.unsigned z) (2 ^ Z.of_nat log2width)) as R3.
      rewrite Z.log2_pow2 by lia.
      do 2 f_equal.
      change Naive.unsigned
        with (word.unsigned (word := (Naive.word (2 ^ Z.of_nat log2width)))).
      rewrite word.unsigned_of_Z_nowrap by lia.
      destr (word.unsigned z <? 2 ^ Z.of_nat log2width).
      + rewrite Z.mod_small by lia.
        destr (word.unsigned z <? 2 ^ Z.of_nat log2width).
        * reflexivity.
        * exfalso; lia.
      + destr (word.unsigned z mod 2 ^ Z.of_nat log2width <? 2 ^ Z.of_nat log2width).
        * cbn. rewrite Z.log2_pow2 by lia. reflexivity.
        * exfalso. lia.

    - destr (word.eqb z (word.of_Z 0)); [|reflexivity].
      change Naive.wrap with (word.of_Z (word := (Naive.word (2 ^ Z.of_nat log2width)))).
      match goal with
      | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
      end.
      + eapply word.of_Z_inj_mod. cbn.
        rewrite <- Zminus_mod_idemp_l.
        rewrite Z_mod_same_full.
        reflexivity.
      + cbn in *. exfalso. congruence.

    - destr (word.eqb z (word.of_Z 0)); [|reflexivity].
      change Naive.wrap with (word.of_Z (word := (Naive.word (2 ^ Z.of_nat log2width)))).
      match goal with
      | |- context [?x =? ?y] => destruct (Z.eqb_spec x y)
      end.
      + cbn. symmetry.
        eapply (word.of_Z_unsigned (word := (Naive.word (2 ^ Z.of_nat log2width))) y).
      + cbn in *. exfalso. congruence.
  Qed.
End NaiveRiscvWord.
