Require Import riscv.util.Word.
Require Import riscv.util.BitWidths.
Require Import riscv.Utility.
Require Import compiler.FlatToRiscvBitWidthSpecifics.
Require Import riscv.Memory.


Instance FlatToRiscv32Specifics{MW: MachineWidth (word 32)}{MF: MemoryFunctions (word 32)}
  : FlatToRiscvBitWidthSpecifics (word 32)  := {|

  BitWidth := BW32;

  loadWordwXLEN := loadWord;

  storeWordwXLEN := storeWord;

|}.
