Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface.

Module word.

  Section RiscvWord.
    Context {width: Z} {word: word.word width}.

    (* TODO maybe we can put more fundamental axioms here, and turn the axioms below into lemmas *)
    Class riscv_ok := {
      sru_ignores_hibits: forall y z,
          word.sru y (word.of_Z (word.unsigned z mod 2 ^ Z.log2 width)) = word.sru y z;
      slu_ignores_hibits: forall y z,
          word.slu y (word.of_Z (word.unsigned z mod 2 ^ Z.log2 width)) = word.slu y z;
      srs_ignores_hibits: forall y z,
          word.srs y (word.of_Z (word.unsigned z mod 2 ^ Z.log2 width)) = word.srs y z;
    }.

  End RiscvWord.

  Arguments riscv_ok {_} _.

End word.
