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
