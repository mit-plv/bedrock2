Require Import compiler.FlatImp.
Require Import compiler.FlatToRiscvBitWidthSpecifics.
Require Import compiler.FlatToRiscvInvariants.
Require Import riscv.InstructionCoercions.
Require Import riscv.AxiomaticRiscv.
Require Import compiler.util.Common.
Require Import riscv.Utility.

Local Open Scope Z_scope.


Section Proofs.

  Variable (mword: Set).
  Context {MW: MachineWidth mword}.

  Variable (mem: Set).
  Context {IsMem: Memory.Memory mem mword}.
  Context {BWS: FlatToRiscvBitWidthSpecifics mword mem}.

  Class FlatToRiscvBitWidthSpecificProofs := {
    
    containsMem_write: forall initialL initialH finalH a v,
      containsMem initialL initialH ->
      Memory.write_mem a v initialH = Some finalH ->
      containsMem (storeWordwXLEN initialL a v) finalH;
  }.


End Proofs.
