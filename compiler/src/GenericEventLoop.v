Require Import riscv.Utility.runsToNonDet.

(* This generic infinite loop can be used by any language whose semantics do not support infinite
   loops. So it can be used for ExprImp and FlatImp, but not for riscv. *)
Section InfLoop.
  Context {State: Type}
          (innerExec: State -> (State -> Prop) -> Prop).

  Definition execLoop: State -> (State -> Prop) -> Prop :=
    runsToNonDet.runsTo innerExec.

End InfLoop.


Require Import compiler.Simulation.

Section LiftSimulation.
  Context {State1 State2: Type}
          {Code1 Code2: Type}
          (innerExec1: State1 -> (State1 -> Prop) -> Prop)
          (innerExec2: State2 -> (State2 -> Prop) -> Prop)
          (innerRelated: State1 -> State2 -> Prop)
          (innerSim: simulation innerExec1 innerExec2 innerRelated).

  Lemma execLoopSim: simulation (execLoop innerExec1) (execLoop innerExec2) innerRelated.
  Proof.
    unfold simulation, execLoop in *.
    intros s1 s2 post1 iR R. revert iR. revert s2.
    induction R; intros.
    - apply runsToDone. eauto.
    - rename H1 into IH.
      specialize innerSim with (1 := iR) (2 := H).
      eapply runsToStep. 1: exact innerSim.
      simpl. intros mid2 (mid1 & ? & ?). eapply IH; eassumption.
  Qed.

End LiftSimulation.


Section Seq.
  Context {State: Type}
          (innerExecFst innerExecSnd: State -> (State -> Prop) -> Prop).

  Definition execSeq: State -> (State -> Prop) -> Prop :=
    fun initial post =>
      exists mid, innerExecFst initial mid /\
                  forall middle, mid middle -> innerExecSnd middle post.
End Seq.


Section LiftSimulation.
  Context {State1 State2: Type}
          (innerExecFirst1 innerExecSecond1: State1 -> (State1 -> Prop) -> Prop)
          (innerExecFirst2 innerExecSecond2: State2 -> (State2 -> Prop) -> Prop)
          (innerRelated: State1 -> State2 -> Prop)
          (innerSimFirst: simulation innerExecFirst1 innerExecFirst2 innerRelated)
          (innerSimSecond: simulation innerExecSecond1 innerExecSecond2 innerRelated).

  Lemma execSeqSim: simulation (execSeq innerExecFirst1 innerExecSecond1)
                               (execSeq innerExecFirst2 innerExecSecond2) innerRelated.
  Proof.
    unfold execSeq, simulation in *.
    intros *. intros iR (mid1 & E1 & E2).
    specialize innerSimFirst with (1 := iR) (2 := E1).
    eexists. split; [exact innerSimFirst|]. simpl.
    intros middle2 (middle1 & iR' & M).
    eapply innerSimSecond; eauto.
  Qed.

End LiftSimulation.


Section EventLoop.
  Context {State: Type}
          (execInitCode execLoopBody: State -> (State -> Prop) -> Prop).

  Definition execEventLoop: State -> (State -> Prop) -> Prop :=
    execSeq execInitCode (execLoop execLoopBody).

End EventLoop.


Section LiftSimulation.
  Context {State1 State2: Type}
          (execInitCode1 execLoopBody1: State1 -> (State1 -> Prop) -> Prop)
          (execInitCode2 execLoopBody2: State2 -> (State2 -> Prop) -> Prop)
          (innerRelated: State1 -> State2 -> Prop)
          (simInitCode: simulation execInitCode1 execInitCode2 innerRelated)
          (simLoopBody: simulation execLoopBody1 execLoopBody2 innerRelated).

  Lemma execEventLoopSim: simulation (execEventLoop execInitCode1 execLoopBody1)
                                     (execEventLoop execInitCode2 execLoopBody2) innerRelated.
  Proof.
    apply execSeqSim.
    - exact simInitCode.
    - apply execLoopSim. exact simLoopBody.
  Qed.

End LiftSimulation.
