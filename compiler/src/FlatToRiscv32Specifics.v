Require Import riscv.util.Word.
Require Import riscv.util.BitWidths.
Require Import riscv.Utility.
Require Import compiler.FlatToRiscvBitWidthSpecifics.
Require Import riscv.Memory.


Instance FlatToRiscv32Specifics(mem: Set)
         {MW: MachineWidth (word 32)}{IsMem: Memory mem (word 32)}
  : FlatToRiscvBitWidthSpecifics (word 32) mem := {|

  BitWidth := BW32;

  loadWordwXLEN := loadWord;
  
  storeWordwXLEN := storeWord;
|}.
