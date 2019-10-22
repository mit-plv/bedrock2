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
Require Import compiler.EmitsValid.
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
     the next iteration of the infinite event loop. It should not say anything about
     the pc, because it will be used both when the pc is at pc_start and when it is at
     pc_end *)
  Variable goodReadyState: RiscvMachineL -> Prop.

  Variables pc_start pc_end: word.
  Hypothesis pc_start_aligned: (word.unsigned pc_start) mod 4 = 0.
  Hypothesis start_ne_end: pc_start <> pc_end.

  Hypothesis goodReadyState_ignores:
    forall (state: RiscvMachineL) newMetrics,
      goodReadyState state ->
      state.(getPc) = pc_end ->
      goodReadyState (withPc pc_start
                     (withNextPc (word.add pc_start (word.of_Z 4))
                     (withMetrics newMetrics state))).

  Variable jump: Z.
  Hypothesis jump_bound: - 2 ^ 20 <= jump < 2 ^ 20.
  Hypothesis jump_aligned: jump mod 4 = 0.
  Hypothesis pc_end_def: pc_end = word.sub pc_start (word.of_Z jump).

  (* loop body: between pc_start and pc_end *)
  Hypothesis body_correct: forall (initial: RiscvMachineL),
      goodReadyState initial ->
      initial.(getPc) = pc_start ->
      valid_machine initial ->
      runsTo (mcomp_sat (run1 iset)) initial (fun final =>
          goodReadyState final /\
          final.(getPc) = pc_end /\
          (exists R, (ptsto_instr pc_end (Jal Register0 jump) * R)%sep final.(getMem)) /\
          valid_machine final).

  Definition runsToGood_Invariant(prefinalL: RiscvMachineL): Prop :=
    runsTo (mcomp_sat (run1 iset)) prefinalL (fun finalL =>
       goodReadyState finalL /\ finalL.(getPc) = pc_start /\ valid_machine finalL).

  (* "runs to a good state" is an invariant of the transition system
     (note that this does not depend on the definition of runN) *)
  Lemma runsToGood_is_Invariant: forall (st: RiscvMachineL),
      runsToGood_Invariant st -> mcomp_sat (run1 iset) st runsToGood_Invariant.
  Proof.
    eapply runsTo_safe1_inv; cycle 1.
    - intros state (? & ? & ?). eapply body_correct; assumption.
    - intros state (? & ? & (R & ?) & ?).
      (* this is the loop verification code: *)
      eapply runsToStep. {
        eapply run_Jal0; try eassumption.
        unfold program, array. rewrite H0. ecancel_assumption.
      }
      simpl. intros. simp.
      destruct_RiscvMachine state.
      destruct_RiscvMachine mid.
      subst.
      apply runsToDone.
      ssplit; try assumption; cbn;
        ring_simplify (word.add (word.sub pc_start (word.of_Z jump)) (word.of_Z jump));
        try reflexivity.
      eapply goodReadyState_ignores in H.
      + apply H.
      + reflexivity.
    - intros state C. simp. congruence.
  Qed.

  Variable startState: RiscvMachineL.

  (* initialization code: all the code before the loop body, loop body starts at pc_start *)
  Hypothesis init_correct:
      runsTo (mcomp_sat (run1 iset)) startState (fun final =>
          goodReadyState final /\ final.(getPc) = pc_start /\ valid_machine final).

End EventLoop.
