Require Import Coq.Lists.List.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Spec.MetricPrimitives.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Platform.Run.
Require Import compiler.GoFlatToRiscv.
Require Import riscv.Utility.runsToNonDet.
Require Import riscv.Platform.MetricSane.
Import ListNotations.


Section ForeverSafe.

  Context {width} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}.
  Context {Registers: map.map Z word}.
  Context {mem: map.map word byte}.

  Local Notation RiscvMachineL := MetricRiscvMachine.
  Local Notation trace := (list LogItem).

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {PR: MetricPrimitives PRParams}.
  Variable iset: Decode.InstructionSet.

  Lemma extend_runsTo_to_good_trace:
    forall (safe: RiscvMachineL -> Prop) (good_trace: trace -> Prop),
      (forall st, safe st -> good_trace st.(getLog)) ->
      forall (st : RiscvMachineL),
        valid_machine st ->
        runsTo (mcomp_sat (run1 iset)) st safe ->
        exists rest : trace, good_trace (rest ++ getLog st).
  Proof.
    intros ? ? safe2good st V R. induction R.
    - exists nil. rewrite List.app_nil_l. eauto.
    - rename P into safe1.
      pose proof (run1_sane _ _ _ V H) as N. destruct N as (_ & N).
      pose proof (run1_sane _ _ _ V N) as N'. cbv beta in *.
      destruct N' as ((_ & mid & A) & _).
      destruct A as (((Hmid & (diff1 & E1)) & Vmid) & _).
      specialize (H1 _ Hmid safe2good Vmid).
      destruct H1 as (diff2 & G).
      rewrite E1 in G.
      rewrite List.app_assoc in G.
      eexists. exact G.
  Qed.

  Variables safe1 safe2: RiscvMachineL -> Prop.

  Hypothesis exclusive: forall state, ~ (safe1 state /\ safe2 state).

  Hypothesis run_1_2: forall state,
      safe1 state -> runsTo (mcomp_sat (run1 iset)) state safe2.

  Hypothesis run_2_1: forall state,
      safe2 state -> runsTo (mcomp_sat (run1 iset)) state safe1.

  Lemma run_ping: forall state,
      runsTo (mcomp_sat (run1 iset)) state safe1 ->
      runsTo (mcomp_sat (run1 iset)) state safe2.
  Proof.
    induction 1; rename P into safe1.
    - eauto.
    - eapply runsToStep. 1: eassumption.
      intros.
      eapply H1; eauto.
  Qed.

  Lemma run_pong: forall state,
      runsTo (mcomp_sat (run1 iset)) state safe2 ->
      runsTo (mcomp_sat (run1 iset)) state safe1.
  Proof.
    induction 1; rename P into safe2.
    - eauto.
    - eapply runsToStep. 1: eassumption.
      intros.
      eapply H1; eauto.
  Qed.

  Lemma runsTo_safe1_inv: forall (st: RiscvMachineL),
      runsTo (mcomp_sat (run1 iset)) st safe1 ->
      mcomp_sat (run1 iset) st (fun st' => runsTo (mcomp_sat (run1 iset)) st' safe1).
  Proof.
    induction 1; rename P into safe1.
    - pose proof (run_1_2 _ H) as P. inversion P.
      + exfalso. eapply exclusive; eauto.
      + eapply mcomp_sat_weaken. 2: eassumption.
        intros. specialize (H1 _ H2).
        eapply run_pong. assumption.
    - eapply mcomp_sat_weaken. 2: eassumption.
      intros.
      eapply H0. assumption.
  Fail Qed. Abort. (* TODO report *)

  (* one step of invariant preservation: *)
  Lemma runsTo_safe1_inv: forall (st: RiscvMachineL),
      runsTo (mcomp_sat (run1 iset)) st safe1 ->
      mcomp_sat (run1 iset) st (fun st' => runsTo (mcomp_sat (run1 iset)) st' safe1).
  Proof.
    intros st R. destruct R.
    - pose proof (run_1_2 _ H) as P. inversion P.
      + exfalso. eapply exclusive; eauto.
      + eapply mcomp_sat_weaken. 2: eassumption.
        intros. specialize (H1 _ H2).
        eapply run_pong. assumption.
    - eapply mcomp_sat_weaken. 2: eassumption.
      intros. eapply H0. assumption.
  Qed.

  Fixpoint runN(n: nat): M unit :=
    match n with
    | O => Return tt
    | S m => Bind (run1 iset) (fun _ => runN m)
    end.

  (* forall n, after running for n steps, we're only "a runsTo away" from a good state.
     The precondition can either be trivially established using runsToDone if safe1 already
     holds, or it can be established by some initialization code which runs before the main
     event loop. *)
  Lemma safe_forever: forall (n: nat) (st: RiscvMachineL),
      runsTo (mcomp_sat (run1 iset)) st safe1 ->
      mcomp_sat (runN n) st
                (fun prefinalL => runsTo (mcomp_sat (run1 iset)) prefinalL safe1).
  Proof.
    induction n; intros.
    - simpl. apply go_done. assumption.
    - simpl. eapply spec_Bind_unit.
      + eapply runsTo_safe1_inv. eassumption.
      + simpl. intros. eapply IHn. assumption.
  Qed.

End ForeverSafe.
