Require Import coqutil.Map.Interface.
Require Import riscv.util.Word.
Require Import riscv.util.BitWidths.
Require Import riscv.Utility.
Require Import compiler.FlatToRiscvBitWidthSpecifics.
Require Import riscv.Memory.

Instance FlatToRiscv64Specifics{byte: word 8}{word64: word 64}{Mem: map.map word64 byte}
  : FlatToRiscvBitWidthSpecifics word64  := {|

  BitWidth := BW64;
|}.
