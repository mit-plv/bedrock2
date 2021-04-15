Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface.
Require Import coqutil.Z.BitOps.

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

      mulhuu_simpl: forall y z,
          word.of_Z (bitSlice (word.unsigned y * word.unsigned z) width (2 * width)) =
          word.mulhuu y z;
      divu0_simpl: forall y z,
          (if word.eqb z (word.of_Z 0) then word.of_Z (2 ^ width - 1) else word.divu y z) =
          word.divu y z;
      modu0_simpl: forall y z,
          (if word.eqb z (word.of_Z 0) then y else word.modu y z) =
          word.modu y z;
    }.

  End RiscvWord.

  Arguments riscv_ok {_} _.

End word.
