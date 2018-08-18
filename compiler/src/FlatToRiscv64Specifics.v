Require Import riscv.util.Word.
Require Import riscv.util.BitWidths.
Require Import riscv.Utility.
Require Import compiler.FlatToRiscvBitWidthSpecifics.
Require Import riscv.Memory.


Instance FlatToRiscv64Specifics(mem: Set)
         {MW: MachineWidth (word 64)}{IsMem: Memory mem (word 64)}
  : FlatToRiscvBitWidthSpecifics (word 64) mem := {|

  BitWidth := BW64;

  loadWordwXLEN := loadDouble;
  
  storeWordwXLEN := storeDouble;
|}.
