Require Import coqutil.Map.Interface.
Require Import riscv.util.BitWidths.
Require Import riscv.Memory.

Class FlatToRiscvBitWidthSpecifics{byte: Type}(word: Type){Mem: map.map word (option byte)} := {
  BitWidth: BitWidths;
}.
