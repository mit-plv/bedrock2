Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.Simulation.
Require Import compiler.Simp.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.util.Common.
Require Import compiler.util.ListLib.
Require Import compiler.Simp.
Require Import compiler.SeparationLogic.
Require Import compiler.SimplWordExpr.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.DivisibleBy4.
Require Import compiler.EmitsValid.
Require Import compiler.MetricsToRiscv.
Require Import compiler.FlatImp.
Require Import compiler.RunInstruction.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import bedrock2.MetricLogging.
Require Import compiler.RiscvEventLoop.
Require Import compiler.MemoryLayout.
Require Import compiler.ProgramSpec.
Require Import riscv.Utility.InstructionCoercions.

Local Open Scope ilist_scope.


Section Loop.
  Context {p: FlatToRiscv.parameters}.
  Context {h: FlatToRiscv.assumptions}.

  Definition sat_memlayout(ml: MemoryLayout Semantics.width): Semantics.mem -> Prop :=
    sep (mem_available ml.(code_start) ml.(code_pastend))
        (sep (mem_available ml.(heap_start) ml.(heap_pastend))
             (mem_available ml.(stack_start) ml.(stack_pastend))).

  Context (prog: Program stmt)
          (spec: ProgramSpec)
          (sat: ProgramSatisfiesSpec prog FlatImp.exec spec).

  Variable ml: MemoryLayout Semantics.width.
  Hypothesis ml_ok: MemoryLayoutOk ml.

  Definition goodReadyStateL: MetricRiscvMachine -> Prop :=
    fun finalL => exists tH mH lH g,
        spec.(isReady) tH mH lH /\
        spec.(goodTrace) tH /\
        goodMachine tH mH lH g finalL.

  Hypothesis ext_guarantee_ignores: forall newPc newMetrics st,
      FlatToRiscv.ext_guarantee st ->
      FlatToRiscv.ext_guarantee (withPc newPc
                                (withNextPc (word.add newPc (word.of_Z 4))
                                (withMetrics newMetrics st))).

  Hypothesis spec_and_layout_agree:
    spec.(datamem_start) = ml.(heap_start) /\ spec.(datamem_pastend) = ml.(heap_pastend).

  Lemma goodMachine_ignores: forall newPc newMetrics t m l g st,
      goodMachine t m l g st ->
      goodMachine t m l g (withPc newPc
                             (withNextPc (word.add newPc (word.of_Z 4))
                             (withMetrics newMetrics st))).
  Proof.
    unfold goodMachine. intros. destruct_RiscvMachine st. destruct g. simpl in *. simp.
    repeat split; eauto.
    match goal with
    | H: FlatToRiscv.ext_guarantee _ |- _ => eapply ext_guarantee_ignores in H; exact H
    end.
  Qed.

  Definition funpositions := build_fun_pos_env prog.(funimpls) 0 prog.(funnames).

  Definition init_insts: list Instruction :=
    compile_stmt_new funpositions 0 prog.(init_code).

  Definition loop_insts: list Instruction :=
    compile_stmt_new funpositions (4 * Z.of_nat (length init_insts)) prog.(loop_body).

  Definition loop_start_pc := word.add ml.(code_start)
                                       (word.of_Z (4 * Z.of_nat (length init_insts))).

  Axiom TODO: False.

  Lemma invariantProps: forall startState: MetricRiscvMachine,
      sat_memlayout ml startState.(getMem) ->
      regs_initialized startState.(getRegs) ->
      startState.(getPc) = ml.(code_start) ->
      startState.(getNextPc) = word.add startState.(getPc) (word.of_Z 4) ->
      startState.(getLog) = [] ->
      FlatToRiscv.ext_guarantee startState ->
      InvariantProps goodReadyStateL loop_start_pc startState spec.(goodTrace).
  Proof.
    intros.
    eapply RiscvEventLoop.invariantProps with (jump := - 4 * Z.of_nat (length loop_insts)).
    all: try reflexivity.
    - unfold goodReadyStateL. intros. simp.
      match goal with
      | H: _ |- _ => eapply goodMachine_ignores in H
      end.
      eauto 10.
    - unfold loop_start_pc. destruct ml_ok. solve_divisibleBy4.
    - case TODO. (* make sure insts is non-empty, short enough, in particular < 2^width/4 long *)
    - case TODO. (* somehow from stmt_not_too_big *)
    - solve_divisibleBy4.
    - (* correctness for loop body code *)
      intros. unfold goodReadyStateL in *. simp.
      eapply runsToNonDet.runsTo_weaken.
      + eapply compile_stmt_correct_new.
        * eapply sat.(loop_body_correct); eassumption.
        * case TODO.
        * case TODO.
        * case TODO.
        * case TODO.
        * case TODO.
        * case TODO.
        * case TODO.
        * case TODO.
        * case TODO.
        * case TODO.
      + case TODO.
    - (* correctness for init code *)
      unfold sat_memlayout, sep in *. simp.
      eapply runsToNonDet.runsTo_weaken.
      + eapply compile_stmt_correct_new with
            (g := {| insts := init_insts;
                     num_stackwords := word.unsigned
                                         (word.sub ml.(stack_pastend) ml.(stack_start)) / 4;
                     e_pos := funpositions;
                  |})
            (initialRegsH := map.empty).
        * eapply sat.(init_code_correct).
          rewrite (proj1 spec_and_layout_agree).
          rewrite (proj2 spec_and_layout_agree).
          eassumption.
        * reflexivity.
        * unfold exists_good_reduced_e_impl. simpl. exists (prog.(funimpls)).
          split; [|split].
          { intros x v A. assumption. }
          { case TODO. (* progagate fits_stack *) }
          { intros. case TODO. }
        * simpl. unfold init_insts. reflexivity.
        * case TODO.
        * case TODO.
        * reflexivity.
        * assumption.
        * simpl. rewrite add_0_r. eassumption.
        * simpl. rewrite add_0_r. reflexivity.
        * unfold goodMachine. simpl.
          repeat match goal with
                 | |- _ /\ _ => split
                 end.
          { intros x v A. rewrite map.get_empty in A. discriminate. }
          { instantiate (1 := ml.(stack_pastend)).
            case TODO. (* who sets the stackpointer initially? *) }
          { assumption. }
          { eexists.
            case TODO. (* define the bytes in memory derived from the instructions *) }
          { assumption. }
          { assumption. }
      + simpl. intros. simp. unfold goodReadyStateL, loop_start_pc.
        destruct_RiscvMachine startState. subst.
        eauto 10.
    - intros. unfold goodReadyStateL, goodMachine in *.
      destruct_RiscvMachine state. simp. assumption.

    Grab Existential Variables. all: case TODO.
  Qed.

End Loop.
