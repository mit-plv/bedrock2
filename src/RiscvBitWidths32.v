Require Import Coq.omega.Omega.
Require Import compiler.RiscvBitWidths.

Instance RiscvBitWidths32: RiscvBitWidths := {|
  wXLEN := 32;
  log2wXLEN := 5;
  wInstr := 32;
  wimm := 12;
  wupper := 20;
|}.
  all: try reflexivity.
  all: abstract omega.
Defined.
