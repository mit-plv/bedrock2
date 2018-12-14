Require Import coqutil.Map.Interface.
Require Import riscv.util.BitWidths.
Require Import riscv.Memory.

Class FlatToRiscvBitWidthSpecifics{byte: Type}(mword: Type){Mem: map.map mword byte} := {
  BitWidth: BitWidths;
}.
