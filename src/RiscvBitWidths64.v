Require Import Coq.omega.Omega.
Require Import compiler.RiscvBitWidths.

Instance RiscvBitWidths64: RiscvBitWidths := {|
  wXLEN := 64;
  wInstr := 32;
  wimm := 12;
  wupper := 20;
|}.
  all: abstract omega.
Defined.
