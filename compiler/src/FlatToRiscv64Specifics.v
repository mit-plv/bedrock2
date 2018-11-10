Require Import riscv.util.Word.
Require Import riscv.util.BitWidths.
Require Import riscv.Utility.
Require Import compiler.FlatToRiscvBitWidthSpecifics.
Require Import riscv.Memory.


Instance FlatToRiscv64Specifics{MW: MachineWidth (word 64)}{MF: MemoryFunctions (word 64)}
  : FlatToRiscvBitWidthSpecifics (word 64)  := {|

  BitWidth := BW64;

  loadWordwXLEN := loadDouble;

  storeWordwXLEN := storeDouble;
|}.
