Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.omega.Omega.
Require Import bbv.Word.
Require Import riscv.Decidable.
Require Import compiler.Tactics.
Require Import compiler.ListLib.


Section Memory.

  Variable w: nat. (* bit width of addresses, registers, and sizes ("size_t" in C), XLEN in RISC-V *)

  Class Memory(m: Type) := mkMemory {
    (* we don't use these load/store/Byte/Half/Word/Double, but they could be added here *)

    (* we only use these two, which are on 32 or 64 bits depending on XLEN: *)
    load_size_t: m -> word w -> word w;
    store_size_t: m -> word w -> word w -> m;
  }.

End Memory.

