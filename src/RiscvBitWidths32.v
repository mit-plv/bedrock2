Require Import Coq.omega.Omega.
Require Import compiler.RiscvBitWidths.

Instance RiscvBitWidths32: RiscvBitWidths := {|
  wXLEN := 32;
  wInstr := 32;
  wimm := 12;
  wupper := 20;
|}.
  all: abstract omega.
Defined.
