Require Import compiler.FlatImp.
Require Import compiler.FlatToRiscvBitWidthSpecifics.
Require Import riscv.InstructionCoercions.
Require Import riscv.AxiomaticRiscv.
Require Import riscv.Memory.
Require Import compiler.util.Common.
Require Import riscv.Utility.

Local Open Scope ilist_scope.
Local Open Scope Z_scope.

Set Implicit Arguments.


Section Invariants.

  Context {mword: Set}.
  Context {MW: MachineWidth mword}.

  Add Ring mword_ring : (@regRing mword MW).

  Context {MF: Memory.MemoryFunctions mword}.
  Context {BWS: FlatToRiscvBitWidthSpecifics mword}.

  Definition containsMem(memL: Mem mword)(memH: compiler.Memory.mem): Prop := forall addr v,
      compiler.Memory.read_mem addr memH = Some v ->
      loadWordwXLEN memL addr = v /\ regToZ_unsigned addr + XLEN_in_bytes <= Memory.memSize memL.

End Invariants.
