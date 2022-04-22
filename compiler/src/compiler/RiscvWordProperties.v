Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.BitOps coqutil.Z.ZLib.
Require Import coqutil.Tactics.destr.

Local Open Scope Z_scope.

Module word.

  Section RiscvWord.
    Context {width: Z} {word: word.word width}.
    Implicit Types x y z : word.

    (* TODO maybe we can put more fundamental axioms here, and turn the axioms below into lemmas *)
    Class riscv_ok: Prop := {
      sru_ignores_hibits: forall y z,
          word.sru y (word.of_Z (word.unsigned z mod 2 ^ Z.log2 width)) = word.sru y z;
      slu_ignores_hibits: forall y z,
          word.slu y (word.of_Z (word.unsigned z mod 2 ^ Z.log2 width)) = word.slu y z;
      srs_ignores_hibits: forall y z,
          word.srs y (word.of_Z (word.unsigned z mod 2 ^ Z.log2 width)) = word.srs y z;

      divu0_simpl: forall y z,
          (if word.eqb z (word.of_Z 0) then word.of_Z (2 ^ width - 1) else word.divu y z) =
          word.divu y z;
      modu0_simpl: forall y z,
          (if word.eqb z (word.of_Z 0) then y else word.modu y z) =
          word.modu y z;
    }.

    Lemma mulhuu_simpl{ok: word.ok word}{rok: riscv_ok}: forall y z,
        word.of_Z (bitSlice (word.unsigned y * word.unsigned z) width (2 * width)) =
        word.mulhuu y z.
    Proof.
      intros. unfold bitSlice.
      eapply word.unsigned_inj.
      rewrite word.unsigned_mulhuu. unfold word.wrap.
      replace (2 * width - width) with width by lia.
      pose proof word.width_pos.
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite (Z.mul_comm (-1)).
      rewrite <- Z.opp_eq_mul_m1.
      replace (Z.lnot (- 2 ^ width)) with (Z.pred (2 ^ width)). 2: {
        pose proof (Z.add_lnot_diag (- 2 ^ width)). lia.
      }
      rewrite <- Z.ones_equiv.
      rewrite Z.land_ones by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      apply word.unsigned_of_Z_nowrap.
      apply Z.mod_pos_bound.
      apply Z.pow2_pos.
      lia.
    Qed.

  End RiscvWord.

  Arguments riscv_ok {_} _.

End word.
