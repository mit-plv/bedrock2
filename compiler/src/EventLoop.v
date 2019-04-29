Require Import Coq.ZArith.BinInt.
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

Section EventLoop.

  Context {W: Words}.
  Context {Registers: map.map Register word}.
  Context {Action: Type}.
  Context {mem: map.map word byte}.
  Context {mem_ok: map.ok mem}.

  Local Notation RiscvMachineL := (MetricRiscvMachine Register Action).
  Local Notation trace := (list (LogItem Action)).

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M (MetricRiscvMachine Register Action)}.
  Context {PR: MetricPrimitives PRParams}.
  Variable iset: InstructionSet.

  (* goodReadyState is the invariant which says that the machine is ready to execute
     the next iteration of the infinite event loop. It should not say anything about
     the pc, because it will be used both when the pc is at pc_start and when it is at
     pc_end *)
  Variable goodReadyState: RiscvMachineL -> Prop.

  (* the trace invariant we want to prove *)
  Variable inv: trace -> Prop.

  Hypothesis goodReadyState_implies_inv: forall (state: RiscvMachineL),
      goodReadyState state -> inv state.(getLog).

  Hypothesis goodReadyState_ignores_Pc: forall (state1 state2: RiscvMachineL),
      state1.(getRegs) = state2.(getRegs) ->
      state1.(getMem) = state2.(getMem) ->
      state1.(getLog) = state2.(getLog) ->
      goodReadyState state1 ->
      goodReadyState state2.

  Variables pc_start pc_end: word.
  Hypothesis pc_start_aligned: (word.unsigned pc_start) mod 4 = 0.
  Hypothesis pc_end_aligned: (word.unsigned pc_end) mod 4 = 0.

  Variable jump: Z.
  Hypothesis jump_bound: - 2 ^ 11 <= jump < 2 ^ 11.
  Hypothesis jump_def: word.of_Z jump = word.sub pc_start pc_end.

  Hypothesis body_correct: forall (initial: RiscvMachineL),
      goodReadyState initial ->
      initial.(getPc) = pc_start ->
      runsTo (mcomp_sat (run1 iset)) initial (fun final =>
          final.(getPc) = pc_end /\
          (exists R, (ptsto_instr pc_end (Jal Register0 jump) * R)%sep final.(getMem)) /\
          goodReadyState final).

  (* forall n, after running for n steps, we're only "a runsTo away" from a good state *)
  Lemma eventLoop_sound: forall (initialL: RiscvMachineL),
      initialL.(getPc) = pc_start ->
      goodReadyState initialL ->
      forall n, mcomp_sat (runN iset n) initialL (fun prefinalL =>
                  runsTo (mcomp_sat (run1 iset)) prefinalL goodReadyState).
  Proof.
    intros initialL E G n. revert initialL E G. induction n; intros.
    - simpl. apply go_done. apply runsToDone. assumption.
    - simpl. eapply spec_Bind_unit.


  Abort.

  (* forall n, after running for n steps, we're only "a runsTo away" from a good state *)
  Lemma eventLoop_sound: forall (initialL: RiscvMachineL),
      initialL.(getPc) = pc_start ->
      goodReadyState initialL ->
      forall n, mcomp_sat (runN iset n) initialL (fun prefinalL =>
                  runsTo (mcomp_sat (run1 iset)) prefinalL (fun finalL => inv finalL.(getLog))).
  Abort.

  (* no matter for how many steps we run [initialL], [inv] always holds *)
  Definition traceInvHolds(initialL: RiscvMachineL)(inv: trace -> Prop): Prop :=
    forall n, mcomp_sat (runN iset n) initialL (fun finalL => inv finalL.(getLog)).

  Lemma eventLoop_sound: forall (initialL: RiscvMachineL),
      initialL.(getPc) = pc_start ->
      goodReadyState initialL ->
      traceInvHolds initialL inv.
  Proof.
    unfold traceInvHolds. intros initialL E G n. revert initialL E G. induction n; intros.
    - simpl. apply go_done. apply goodReadyState_implies_inv. assumption.
    - simpl. eapply spec_Bind_unit.

      (* induction needs to be on number of loop iterations, not on number of instructions *)

      (* might hold if each iteration only appends one event, but not otherwise, because
         in the middle of the loop body, traceInv will not hold, and there's no way we
         can communicate with runsTo to know that it's "on its way" to become valid again,
         this would require a "gurantee", or an application-specific ext_spec which makes
         the riscv machine crash whenever the ext_spec is violated *)
  Abort.

End EventLoop.
