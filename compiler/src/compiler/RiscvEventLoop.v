From Coq Require Import ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Platform.Run.
Require Import riscv.Spec.Execute.
Require Import riscv.Proofs.DecodeEncode.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.SeparationLogic.
Require Import bedrock2.ptsto_bytes.
Require Import bedrock2.Scalars.
Require Import riscv.Utility.Encode.
Require Import riscv.Proofs.EncodeBound.
Require Import coqutil.Decidable.
Require Import compiler.GoFlatToRiscv.
Require Import riscv.Utility.runsToNonDet.
Require Import riscv.Utility.InstructionCoercions.
Require Import compiler.ForeverSafe.
Require Import compiler.RunInstruction.
Require Import compiler.DivisibleBy4.
Require Import compiler.Simp.
Import Utility.

Section EventLoop.

  Context {W: Words}.
  Context {Registers: map.map Register word}.
  Context {mem: map.map word byte}.
  Context {mem_ok: map.ok mem}.

  Local Notation RiscvMachineL := MetricRiscvMachine.
  Local Notation trace := (list LogItem).

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {PR: MetricPrimitives PRParams}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  (* goodReadyState is the invariant which says that the machine is ready to execute
     the next iteration of the infinite event loop.
     It also gets the expected value of the PC, and has to check getPc and getNextPc. *)
  Variable goodReadyState: word -> RiscvMachineL -> Prop.

  Hypothesis goodReadyState_checks_PC: forall pc m,
      goodReadyState pc m -> m.(getPc) = pc.

  Variables pc_start pc_end: word.
  Hypothesis pc_start_aligned: (word.unsigned pc_start) mod 4 = 0.
  Hypothesis start_ne_end: pc_start <> pc_end.

  Hypothesis goodReadyState_preserved_by_jump_back:
    forall (state: RiscvMachineL) newMetrics,
      goodReadyState pc_end state ->
      goodReadyState pc_start (withPc pc_start
                              (withNextPc (word.add pc_start (word.of_Z 4))
                              (withMetrics newMetrics state))).

  Hypothesis goodReadyState_implies_valid_machine: forall pc m,
      goodReadyState pc m -> valid_machine m.

  Variable jump: Z.
  Hypothesis jump_bound: - 2 ^ 20 <= jump < 2 ^ 20.
  Hypothesis jump_aligned: jump mod 4 = 0.
  Hypothesis pc_end_def: pc_end = word.sub pc_start (word.of_Z jump).

  Hypothesis goodReadyState_implies_jump_back_instr: forall m,
      goodReadyState pc_end m ->
      (exists R, (ptsto_instr pc_end (Jal Register0 jump) * R)%sep m.(getMem)) /\
      subset (footpr (ptsto_instr pc_end (Jal Register0 jump)))
             (of_list m.(getXAddrs)).

  (* loop body: between pc_start and pc_end *)
  Hypothesis body_correct: forall (initial: RiscvMachineL),
      goodReadyState pc_start initial ->
      runsTo (mcomp_sat (run1 iset)) initial (goodReadyState pc_end).

  Definition runsToGood_Invariant(m: RiscvMachineL): Prop :=
    runsTo (mcomp_sat (run1 iset)) m (goodReadyState pc_start).

  (* "runs to a good state" is an invariant of the transition system
     (note that this does not depend on the definition of runN) *)
  Lemma runsToGood_is_Invariant: forall (st: RiscvMachineL),
      runsToGood_Invariant st -> mcomp_sat (run1 iset) st runsToGood_Invariant.
  Proof.
    eapply runsTo_safe1_inv; cycle 1.
    - intros. eapply body_correct; assumption.
    - intros.
      (* this is the loop verification code: *)
      eapply runsToStep. {
        specialize (goodReadyState_implies_jump_back_instr _ H).
        destruct goodReadyState_implies_jump_back_instr. simp.
        specialize (goodReadyState_checks_PC _ _ H). subst pc_end.
        eapply run_Jal0; try eauto.
        - unfold program, array.
          eapply rearrange_footpr_subset; [ eauto | solve [ ecancel ] ].
        - unfold program, array. ecancel_assumption.
      }
      simpl. intros. simp.
      destruct_RiscvMachine state.
      destruct_RiscvMachine mid.
      subst.
      apply runsToDone.
      ssplit; try assumption; cbn;
        ring_simplify (word.add (word.sub pc_start (word.of_Z jump)) (word.of_Z jump));
        try reflexivity.
      specialize (goodReadyState_checks_PC _ _ H). simpl in *. subst state_pc.
      eapply goodReadyState_preserved_by_jump_back in H.
      + simpl in H.
        match goal with
        | |- ?G => let T := type of H in replace G with T; [exact H|]
        end.
        repeat f_equal.
        all: solve_word_eq word_ok.
    - intros state [C1 C2].
      apply goodReadyState_checks_PC in C1.
      apply goodReadyState_checks_PC in C2.
      congruence.
  Qed.

End EventLoop.
