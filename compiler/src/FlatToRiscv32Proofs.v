Require Import compiler.FlatImp.
Require Import compiler.FlatToRiscvBitWidthSpecificProofs.
Require Import compiler.FlatToRiscvInvariants.
Require Import riscv.InstructionCoercions.
Require Import riscv.AxiomaticRiscv.
Require Import compiler.util.Common.
Require Import riscv.Utility.
Require Import riscv.MachineWidth32.
Require Import compiler.FlatToRiscv32Specifics.
Require Import compiler.FlatToRiscvBitWidthSpecifics.

Local Open Scope Z_scope.



Instance FlatToRiscv32Proofs{MF: Memory.MemoryFunctions (word 32)}
  : FlatToRiscvBitWidthSpecificProofs (word 32).
Proof.
  constructor.
  - intros.
    unfold containsMem, Memory.write_mem, Memory.read_mem, storeWordwXLEN,
      loadWordwXLEN, XLEN_in_bytes in *.
    intros. simpl in *.
    do 2 (destruct_one_match_hyp; [|discriminate]).
    inversions H0.
    destruct_one_match_hyp.
    + apply weqb_spec in E1. subst.
      inversions H1.
      specialize H with (1 := E0).
      destruct_one_match_hyp; [|discriminate].
      destruct H as [A B0].
      split.
      * apply Memory.loadStoreWord_eq; try reflexivity.
        unfold Memory.valid_addr. change (32 / 8) with 4 in *.
        rewrite Z.eqb_eq in E1.
        auto.
      * rewrite Memory.storeWord_preserves_memSize. assumption.
    + pose proof H as G.
      specialize H with (1 := E0). destruct H as [A B].
      specialize (G addr v0).
      rewrite E in G. rewrite H1 in G. specialize (G eq_refl). destruct G as [C D].
      subst.
      destruct_one_match_hyp; try discriminate.
      split.
      * apply weqb_false in E1. change (32 / 8) with 4 in *.
        rewrite Z.eqb_eq in *.
        apply @Memory.loadStoreWord_ne; try congruence; unfold Memory.valid_addr; auto.
      * rewrite Memory.storeWord_preserves_memSize. assumption.
Qed.
