Require Import coqutil.Map.Interface.
Require Import riscv.Utility.runsToNonDet.
Require Import bedrock2.Semantics.
Require Import bedrock2.MetricLogging.
Require Import compiler.ProgramSpec.


Inductive EventLoopState := Init | Ready | Done.

Section EventLoop.
  Context {p: Semantics.parameters}.

  Definition State: Type :=
    EventLoopState * env * Syntax.cmd * Syntax.cmd * trace * mem * locals * MetricLog.

  (* state machine step *)
  Inductive stm_step: State -> (State -> Prop) -> Prop :=
  | stm_init_to_ready: forall e init_code loop_body t m l mc (post: State -> Prop),
      Semantics.exec e init_code t m l mc
         (fun t' m' l' mc' => post (Ready, e, init_code, loop_body, t', m', l', mc')) ->
      stm_step (Init, e, init_code, loop_body, t, m, l, mc) post
  | stm_ready_to_done: forall e init_code loop_body t m l mc (post: State -> Prop),
      Semantics.exec e loop_body t m l mc
         (fun t' m' l' mc' => post (Done, e, init_code, loop_body, t', m', l', mc')) ->
      stm_step (Ready, e, init_code, loop_body, t, m, l, mc) post
  | stm_done_to_ready: forall e init_code loop_body t m l mc (post: State -> Prop),
      post (Ready, e, init_code, loop_body, t, m, l, mc) ->
      stm_step (Done, e, init_code, loop_body, t, m, l, mc) post.

  Definition exec: State -> (State -> Prop) -> Prop :=
    runsToNonDet.runsTo stm_step.

  Variable prog: Program Syntax.cmd.
  Variable spec: ProgramSpec.
  Hypothesis sat: ProgramSatisfiesSpec prog Semantics.exec spec.

  Definition hl_inv(s: State): Prop :=
    runsToNonDet.runsTo stm_step s (fun '(elState', e', init_code', loop_body', t', m', l', mc') =>
         elState' = Ready /\
         e' = prog.(funimpls) /\
         init_code' = prog.(init_code) /\
         loop_body' = prog.(loop_body) /\
         spec.(goodTrace) t' /\
         spec.(isReady) t' m' l').

  Lemma stm_step_preserves_hl_inv: forall s,
      hl_inv s -> stm_step s hl_inv.
  Proof.
    unfold hl_inv. intros.
    destruct H.
    - (* nothing in the runsTo, at beginning of loop, so we pack one loop body & one jump back
         into the runsTo we're creating for the invariant *)
      destruct s as (((((((elState' & e') & init') & body') & t') & m') & l') & mc').
      destruct H as (? & ? & ? & ? & ? & ?). subst.
      eapply stm_ready_to_done.
      eapply ExprImp.weaken_exec.
      + eapply sat.(loop_body_correct); eassumption.
      + simpl. intros *. intros (R & G).
        eapply runsToStep; cycle 1.
        * intros. eapply runsToDone. exact H.
        * eapply stm_done_to_ready. eauto 6.
    - rename H into RHead, H0 into RTail.
      (* at least one stm_step in the runsTo, let's see which step it was: *)
      inversion RHead.
      + (* stm_init_to_ready *)
        subst. eapply stm_init_to_ready.
        eapply ExprImp.weaken_exec. 1: exact H.
        simpl. intros. eapply RTail. eassumption.
      + (* stm_ready_to_done *)
        subst. eapply stm_ready_to_done.
        eapply ExprImp.weaken_exec. 1: exact H.
        simpl. intros. eapply RTail. eassumption.
      + (* stm_done_to_ready *)
        subst. eapply stm_done_to_ready.
        eapply RTail. eassumption.
  Qed.

End EventLoop.
