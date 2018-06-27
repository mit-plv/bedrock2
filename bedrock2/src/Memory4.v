Require Import bbv.Word.

Section Memory.

  Variable w: nat. (* bit width of addresses and memory words *)

  Definition mem_access := word w -> bool.

  Definition mem_contents := word w -> option (word w).

  Definition memory(access: mem_access)(contents: mem_contents): Prop :=
    forall x, access x = false <-> contents x = None.

End Memory.

