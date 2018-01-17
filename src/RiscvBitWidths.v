
Class RiscvBitWidths := mkRiscvBitWidths {
  (* ``There are 31 general-purpose registers x1-x31, which hold integer values. Register x0 is
     hardwired to the constant 0. [...] This document uses the term XLEN to refer to the current
     width of an x register in bits (either 32 or 64).'' *)
  wXLEN: nat;

  (* Bit width of an instruction, will be 32 *)
  wInstr: nat;

  (* bit width of most immediates, will equal 12 *)
  wimm: nat;

  (* bit width of "upper" bits to complete 12-bit immediates, will equal 20 *)
  wupper: nat;

  w_eq: wimm + wupper = wInstr;

  wimm_nonzero: wimm <> 0;

  wupper_nonzero: wupper <> 0;

  wXLEN_lbound: wXLEN >= wInstr;

}.
