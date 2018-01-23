(* Non-standard bitwidth useful for debugging.
   In particular, sometimes cbv takes forever because some definition (eg wlt_dec) is opaque,
   and on 32 bit, this runs out of memory, whereas on 8 bit we can hope to get a huge term
   in which the unreduced offending definition (eg wlt_dec) occurs over and over again. *)

Require Import Coq.omega.Omega.
Require Import compiler.RiscvBitWidths.

Instance RiscvBitWidths8: RiscvBitWidths := {|
  wXLEN := 8;
  log2wXLEN := 3;
  wInstr := 8;
  wimm := 3;
  wupper := 5;
|}.
  all: try reflexivity.
  all: abstract omega.
Defined.
