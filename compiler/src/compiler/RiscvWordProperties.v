Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Bitwidth coqutil.Word.Properties.
Require Import coqutil.Z.BitOps coqutil.Z.ZLib.
Require Import coqutil.Tactics.destr.

Local Open Scope Z_scope.

(* The RISC-V M extension (riscv-coq's Utility) and bedrock2's Semantics.interp_binop
   spell the same operations differently. *)
Module word.

  Section RiscvWord.
    Context {width: Z} {BW: Bitwidth width}.
    Local Notation word := (bits width).
    Implicit Types x y z : word.

    Lemma mulhuu_simpl: forall y z,
        bits.of_Z width (bitSlice (Zmod.unsigned y * Zmod.unsigned z) width (2 * width)) =
        bits.of_Z width (Zmod.unsigned y * Zmod.unsigned z / 2 ^ width).
    Proof.
      intros. unfold bitSlice.
      replace (2 * width - width) with width by lia.
      pose proof width_pos. pose proof modulus_pos.
      pose proof (bits.unsigned_range y width_nonneg).
      pose proof (bits.unsigned_range z width_nonneg).
      rewrite Z.shiftl_mul_pow2 by lia.
      rewrite (Z.mul_comm (-1)).
      rewrite <- Z.opp_eq_mul_m1.
      replace (Z.lnot (- 2 ^ width)) with (Z.pred (2 ^ width)). 2: {
        pose proof (Z.add_lnot_diag (- 2 ^ width)). lia.
      }
      rewrite <- Z.ones_equiv.
      rewrite Z.land_ones by lia.
      rewrite Z.shiftr_div_pow2 by lia.
      f_equal. apply Z.mod_small. split.
      - apply Z.div_pos; lia.
      - apply Z.div_lt_upper_bound; nia.
    Qed.

    Lemma divu0_simpl: forall y z,
        (if Zmod.eqb z (bits.of_Z width 0) then bits.of_Z width (2 ^ width - 1) else Zmod.udiv y z) =
        Zmod.udiv y z.
    Proof.
      intros. destr (Zmod.eqb z (bits.of_Z width 0)); trivial.
      subst. rewrite Zmod.of_Z_0, Zmod.udiv_0_r.
      apply Zmod.unsigned_inj. pose proof modulus_pos.
      rewrite bits.unsigned_of_Z_small, bits.unsigned_m1, Z.ones_equiv; lia.
    Qed.

    Lemma modu0_simpl: forall y z,
        (if Zmod.eqb z (bits.of_Z width 0) then y else Zmod.umod y z) =
        Zmod.umod y z.
    Proof.
      intros. destr (Zmod.eqb z (bits.of_Z width 0)); trivial.
      subst. rewrite Zmod.of_Z_0, Zmod.umod_0_r. reflexivity.
    Qed.

  End RiscvWord.

End word.
