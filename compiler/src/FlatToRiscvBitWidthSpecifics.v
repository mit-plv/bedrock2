Require Import coqutil.Map.Interface.
Require Import riscv.util.BitWidths.
Require Import riscv.Utility.
Require Import riscv.Memory.

Class FlatToRiscvBitWidthSpecifics(mword: Type){MW: MachineWidth mword}{Mem: map.map mword byte} := {
  BitWidth: BitWidths;
}.
