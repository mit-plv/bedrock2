Require Import riscv.Utility.runsToNonDet.

(* This generic event loop can be used by any language whose semantics do not support infinite
   loops and which do not keep track themselves of the event loop state.
   So it can be used for ExprImp and FlatImp, but not for riscv. *)
Section EventLoop.
  Context {InnerState: Type} {Code: Type}
          (innerExec: Code * InnerState -> (Code * InnerState -> Prop) -> Prop).

  (* code to run infinitely, code to run next, inner state *)
  Definition State: Type := Code * (Code * InnerState).

  (* state machine step *)
  Inductive stm_step: State -> (State -> Prop) -> Prop :=
  | do_stm_step: forall run_next loop_body post si,
      innerExec (run_next, si) (fun '(_, si') => post (loop_body, (loop_body, si'))) ->
      stm_step (loop_body, (run_next, si)) post.

  Definition exec: State -> (State -> Prop) -> Prop :=
    runsToNonDet.runsTo stm_step.

End EventLoop.


Require Import compiler.Simulation.

Section LiftSimulation.
  Context {InnerState1 InnerState2: Type}
          {Code1 Code2: Type}
          (innerExec1: Code1 * InnerState1 -> (Code1 * InnerState1 -> Prop) -> Prop)
          (innerExec2: Code2 * InnerState2 -> (Code2 * InnerState2 -> Prop) -> Prop)
          (innerRelated: Code1 * InnerState1 -> Code2 * InnerState2 -> Prop)
          (innerSim: simulation innerExec1 innerExec2 innerRelated).

  Definition code_related(code1: Code1)(code2: Code2): Prop :=
    exists si1 si2, innerRelated (code1, si1) (code2, si2).

  Local Notation State1 := (@State InnerState1 Code1).
  Local Notation State2 := (@State InnerState2 Code2).

  Definition liftRelated: State1 -> State2 -> Prop :=
    fun '(loop_body1, (run_next1, si1)) '(loop_body2, (run_next2, si2)) =>
      innerRelated (run_next1, si1) (run_next2, si2) /\
      code_related loop_body1 loop_body2.

  Hypothesis weaken_innerExec2: weakening innerExec2.

  Lemma liftSim: simulation (exec innerExec1) (exec innerExec2) liftRelated.
  Proof.
    unfold simulation, exec in *.
    intros s1 s2 post1 LR R. revert LR.
    induction R; intros.
    - apply runsToDone. eauto.
    - inversion H. subst post initial. clear H.
      unfold liftRelated in LR.
      destruct s2 as (loop2 & next2 & si2).
      destruct LR as (RI & RC).
      specialize innerSim with (1 := RI) (2 := H2). simpl in innerSim.
      eapply runsToStep with
          (midset0 := (fun s2Mid : State2 => exists si1Mid : InnerState1,
                           liftRelated (loop_body, (loop_body, si1Mid)) s2Mid /\
                           midset (loop_body, (loop_body, si1Mid)))).
      + eapply do_stm_step.
        eapply weaken_innerExec2. 2: exact innerSim.
        simpl. intros (run_next2 & siMid2). intro A.
        destruct A as ((run_next1 & si1Mid) & RI' & M).
        eexists. split; [|exact M].
        split; [|exact RC].
        unfold code_related in RC.
        (* almost follows from RC except for exists/forall *)
        admit.
      + simpl. intros. destruct mid as (run_next2 & loop_body2 & si2Mid).
        destruct H as (si1Mid & (RImid & RCmid) & M).
        eapply runsTo_weaken.
        *
  Abort.

(*
  Definition liftRelated: State -> State -> Prop :=
    fun '(loop_body1, run_next1, si1) '(loop_body2, run_next2, si2) =>
      innerRelated (run_next1, si1) (run_next2, si2) /\
      (* roundabout way to say that "compile loop_body1 = loop_body2": *)
      exists post1 post2,
        innerExec1 (run_next1, si1) post1 /\
        innerExec2 (run_next2, si2) post2 /\
        forall s1' s2', post1 s1' -> post2 s2' ->
                        innerRelated (loop_body1, snd s1') (loop_body2, snd s2').

  (* would need to introduce "code_related" *)

  Lemma liftSim: simulation (exec innerExec1) (exec innerExec2) liftRelated.
  Abort.
*)

End LiftSimulation.
