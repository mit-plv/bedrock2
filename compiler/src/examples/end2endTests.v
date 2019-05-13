Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.Utility.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.Machine.
Require riscv.Platform.Memory.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Proofs.EncodeBound.
Require Import riscv.Proofs.DecodeEncode.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Monads. Import MonadNotations.
Require Import riscv.Utility.runsToNonDet.
Require Import coqutil.Datatypes.PropSet.
Require Import riscv.Utility.MMIOTrace.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Spec.MetricPrimitives.
Require Import compiler.RunInstruction.
Require Import compiler.EventLoop.
Require Import compiler.ForeverSafe.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.Simp.

Local Open Scope Z_scope.

Section Test.

  Context {M: Type -> Type}.
  Context {W: Utility.Words}.

  Context {Registers: map.map Register word}
          {mem: map.map word byte}
          {mm: Monad M}
          {rvm: RiscvProgram M word}.

  Context (KamiMachine: Type).

  Context (instrMemSizeLg: Z).

  (* common event between riscv-coq and Kami *)
  Inductive Event: Type :=
  | MMInputEvent(addr v: word)
  | MMOutputEvent(addr v: word).

  Context (kamiStep: KamiMachine -> KamiMachine -> list Event -> Prop).

  Context (states_related: KamiMachine * list Event -> MetricRiscvMachine -> Prop).

  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {PR: MetricPrimitives PRParams}.

  Inductive star{S E: Type}(R: S -> S -> list E -> Prop): S -> S -> list E -> Prop :=
  | star_refl: forall (x: S),
      star R x x nil
  | star_step: forall (x y z: S) (t1 t2: list E),
      R x y t1 ->
      star R y z t2 ->
      star R x z (t2 ++ t1).

  (* something like this is being proved in processor/src/KamiRiscv.v *)
  Hypothesis kamiStep_sound: forall (m1 m2: KamiMachine) (m1': MetricRiscvMachine)
                                    (t t0: list Event) (post: MetricRiscvMachine -> Prop),
      kamiStep m1 m2 t ->
      states_related (m1, t0) m1' ->
      mcomp_sat (run1 iset) m1' post ->
      (* Either Kami doesn't proceed or riscv-coq simulates. *)
      ((m1 = m2 /\ t = nil) (* <-- "t = nil" added *) \/
       exists m2', states_related (m2, t ++ t0) m2' /\ post m2').

  Lemma Return_tt_nop: forall comp m post,
      mcomp_sat (comp;; Return tt) m post ->
      mcomp_sat comp m post.
  Proof.
    Close Scope monad_scope.
    intros. rewrite <- (right_identity comp).
    replace Return with (fun _ : unit => Return tt); [assumption|].
    extensionality x. destruct x. reflexivity.
  Qed.

  Lemma kamiMultiStep_sound: forall
    (* inv could (and probably has to) be something like "runs to a safe state" *)
    (inv: MetricRiscvMachine -> Prop)
    (* could be instantiated with compiler.ForeverSafe.runsTo_safe1_inv *)
    (inv_preserved: forall st, inv st -> mcomp_sat (run1 iset) st inv)
    (m1 m2: KamiMachine) (t: list Event),
      star kamiStep m1 m2 t ->
      forall (m1': MetricRiscvMachine) (t0: list Event),
      states_related (m1, t0) m1' ->
      inv m1' ->
      exists m2', states_related (m2, t ++ t0) m2' /\ inv m2'.
  Proof.
    intros ? ?.
    induction 1; intros.
    - exists m1'. split; assumption.
    - pose proof kamiStep_sound as P.
      specialize P with (1 := H) (2 := H1).
      edestruct P as [Q | Q]; clear P.
      + eapply inv_preserved. assumption.
      + destruct Q. subst. rewrite List.app_nil_r.
        eapply IHstar; eassumption.
      + destruct Q as (m2' & Rel & Inv).
        rewrite <- List.app_assoc.
        eapply IHstar; eassumption.
  Qed.

End Test.


Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import compiler.PipelineWithRename.

Section Connect.

  Context {p: PipelineWithRename.Pipeline.parameters}.
  Context {h: PipelineWithRename.Pipeline.assumptions}.

  Context (KamiMachine: Type).
  Context (kamiStep: KamiMachine -> KamiMachine -> list Event -> Prop).
  Context (states_related: KamiMachine * list Event -> MetricRiscvMachine -> Prop).

  Hypothesis kamiStep_sound:
    forall (m0 m3 : KamiMachine) (m1'0 : MetricRiscvMachine) (t1 t2 : list Event)
           (post : MetricRiscvMachine -> Prop),
      kamiStep m0 m3 t1 ->
      states_related (m0, t2) m1'0 ->
      mcomp_sat (run1 iset) m1'0 post ->
      m0 = m3 /\ t1 = [] \/
                 (exists m2' : MetricRiscvMachine, states_related (m3, t1 ++ t2) m2' /\ post m2').

  (* note: given-away and received memory has to be empty *)
  Inductive events_related: Event -> LogItem -> Prop :=
  | relate_MMInput: forall addr v,
      events_related (MMInputEvent addr v) ((map.empty, MMInput, [addr]), (map.empty, [v]))
  | relate_MMOutput: forall addr v,
      events_related (MMOutputEvent addr v) ((map.empty, MMOutput, [addr; v]), (map.empty, [])).

  Inductive traces_related: list Event -> list LogItem -> Prop :=
  | relate_nil:
      traces_related nil nil
  | relate_cons: forall e e' t t',
      events_related e e' ->
      traces_related t t' ->
      traces_related (e :: t) (e' :: t').

  Lemma hl_event_determines_ll_event: forall e' e1 e2,
      events_related e1 e' ->
      events_related e2 e' ->
      e1 = e2.
  Proof.
    intros. inversion H; inversion H0; subst; simp; congruence.
  Qed.

  Lemma hl_trace_determines_ll_trace: forall {t' t1 t2},
      traces_related t1 t' ->
      traces_related t2 t' ->
      t1 = t2.
  Proof.
    induction t'; intros.
    - inversion H. inversion H0. reflexivity.
    - inversion H. inversion H0. subst. f_equal.
      + eapply hl_event_determines_ll_event; eassumption.
      + eapply IHt'; eassumption.
  Qed.

  Lemma split_ll_trace: forall {t2' t1' t},
      traces_related t (t2' ++ t1') ->
      exists t1 t2, t = t2 ++ t1 /\ traces_related t1 t1' /\ traces_related t2 t2'.
  Proof.
    induction t2'; intros.
    - exists t, nil. simpl in *. repeat constructor. assumption.
    - simpl in H. simp. specialize IHt2' with (1 := H4).
      destruct IHt2' as (t1 & t2 & E & R1 & R2). subst.
      exists t1. exists (e :: t2). simpl. repeat constructor; assumption.
  Qed.

  (* should be just inversion *)
  Hypothesis states_related_to_traces_related: forall m m' t,
      states_related (m, t) m' -> traces_related t m'.(getLog).

  Variables init body: cmd.

  (* will have to be extended with a program logic proof at the top and with the kami refinement
     proof to the pipelined processor at the bottom: *)
  Lemma bedrock2Semantics_to_kamiSpecProcessor:
    forall (goodTrace: list Event -> Prop) (m1 m2: KamiMachine) (t t0: list Event)
           (m1': MetricRiscvMachine),
      (* TODO many more hypotheses will be needed *)
      states_related (m1, t0) m1' ->
      star kamiStep m1 m2 t ->
      exists suffix, goodTrace (suffix ++ t ++ t0).
  Proof.
    intros.

    pose proof compile_prog_correct as P.
    specialize P with (hl_inv := fun hlTrace =>
                                   exists llTrace, traces_related llTrace hlTrace /\
                                                   goodTrace llTrace).
    edestruct P as (ll_inv & establish_ll_inv & use_ll_inv); [admit..|].

    pose proof kamiMultiStep_sound as Q.
    specialize Q with (inv := ll_inv) (m1 := m1) (m2 := m2) (m1' := m1') (t := t) (t0 := t0).
    edestruct Q as (m2' & Rel & InvFinal).
    - eapply kamiStep_sound.
    - intros st HI. edestruct use_ll_inv as (U & _). 1: exact HI. exact U.
    - eassumption.
    - eassumption.
    - eapply establish_ll_inv. auto.
    - apply states_related_to_traces_related in Rel.
      edestruct use_ll_inv as (_ & U). 1: exact InvFinal.
      destruct U as (suffix & llTrace & Rel' & G).
      apply split_ll_trace in Rel'.
      destruct Rel' as (llTrace1 & llTrace2 & E & Rel1' & Rel2'). subst.
      pose proof (hl_trace_determines_ll_trace Rel Rel1'). subst.
      exists llTrace2. exact G.
  Admitted.

End Connect.
