Require Import Coq.omega.Omega.
Require Import bbv.NatLib.

Class RiscvBitWidths := mkRiscvBitWidths {
  (* ``There are 31 general-purpose registers x1-x31, which hold integer values. Register x0 is
     hardwired to the constant 0. [...] This document uses the term XLEN to refer to the current
     width of an x register in bits (either 32 or 64).'' *)
  wXLEN: nat;

  log2wXLEN: nat;
  log2wXLEN_spec: pow2 log2wXLEN = wXLEN;

  (* Bit width of an instruction, will be 32 *)
  wInstr: nat;

  (* bit width of most immediates, will equal 12 *)
  wimm: nat;

  (* bit width of "upper" bits to complete 12-bit immediates, will equal 20 *)
  wupper: nat;

  w_eq: wimm + wupper = wInstr;

  wimm_nonzero: wimm <> 0;

  (* need to encode signed immediates: need at least 1 bit for sign, 1 bit for value *)
  wimm_lbound: wimm >= 2;

  (* we express statement size bounds with wimm, but JAL uses wupper, which is more *)
  wimm_wupper: wimm <= wupper;

  wupper_nonzero: wupper <> 0;

  wXLEN_lbound: wXLEN >= wInstr;

  (* This prevents 64bit. TODO remove this and make sure literal loading still works. *)
  wXLEN_wInstr: wXLEN = wInstr;
}.

Ltac bitwidth_omega :=
  match goal with
  | B: RiscvBitWidths |- _ => abstract (destruct B; simpl in *; omega)
  end.
