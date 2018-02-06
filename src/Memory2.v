Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.omega.Omega.
Require Import bbv.Word.
Require Import riscv.Decidable.
Require Import compiler.Tactics.
Require Import compiler.ListLib.

(* monadic memory *)

Section Memory.

  Variable w: nat. (* bit width of addresses, registers, and sizes ("size_t" in C), XLEN in RISC-V *)

  Class Memory(M: Type -> Type) := mkMemory {
    (* we don't use these, they're just here for compatibility *)
    loadByte: word w -> M (word 8);
    loadHalf: word w -> M (word 16);
    loadWord: word w -> M (word 32);
    loadDouble: word w -> M (word 64);
    storeByte: word w -> word 8 -> M unit;
    storeHalf: word w -> word 16 -> M unit;
    storeWord: word w -> word 32 -> M unit;
    storeDouble: word w -> word 64 -> M unit;

    (* we only use these two, which are on 32 or 64 bits depending on XLEN: *)
    load_size_t: word w -> M (word w);
    store_size_t: word w -> word w -> M unit;
  }.

End Memory.

