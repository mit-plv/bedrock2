Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import riscv.Spec.Decode.
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


Section ForeverSafe.

  Context {W: Words}.
  Context {Registers: map.map Register word}.
  Context {Action: Type}.
  Context {mem: map.map word byte}.
  Context {mem_ok: map.ok mem}.

  Local Notation RiscvMachineL := MetricRiscvMachine.

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {PR: MetricPrimitives PRParams}.
  Variable iset: InstructionSet.

  Fixpoint runN(n: nat): M unit :=
    match n with
    | O => Return tt
    | S m => Bind (run1 iset) (fun _ => runN m)
    end.

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


  (* below: some failed attempts to go from runsTo to trace prefixes *)

  Local Notation trace := (list LogItem).
  Import Coq.Lists.List.
  Import ListNotations.

  Lemma strengthen_safe1: forall (good_trace: trace -> Prop),
      (forall st, safe1 st -> good_trace st.(getLog)) ->
      forall st,
        runsTo (mcomp_sat (run1 iset)) st safe1 ->
        runsTo (mcomp_sat (run1 iset)) st (fun final => safe1 final /\
                                           exists rest, good_trace (getLog st ++ rest)).
  Proof.
    intros ? safe2good st R. induction R.
    - eapply runsToDone. split; [assumption|].
      exists nil. rewrite List.app_nil_r. eapply safe2good. assumption.
    - eapply runsToStep. 1: eassumption.
      intros. eapply runsTo_weaken.
      + eapply H1; eassumption.
      + simpl.
        intros final [ Pf [rest Gt] ].
        split; [assumption|].
        assert (exists diff, getLog mid = getLog initial ++ diff) as E by admit.
        destruct E as [diff E]. rewrite E in Gt.
        rewrite <- List.app_assoc in Gt.
        exists (diff ++ rest).
        exact Gt.
    all: fail.
  Abort.

  Lemma strengthen_safe1: forall (good_trace: trace -> Prop),
      (forall st, safe1 st -> good_trace st.(getLog)) ->
      forall st,
        runsTo (mcomp_sat (run1 iset)) st safe1 ->
        runsTo (mcomp_sat (run1 iset)) st safe1 /\ exists rest, good_trace (getLog st ++ rest).
  Proof.
    intros ? safe2good st R. induction R.
    - split.
      + eapply runsToDone. assumption.
      + exists nil. rewrite List.app_nil_r. eapply safe2good. assumption.
    - (* too independent, we'd need "mid" given by runsTo also in rhs of /\ *)
  Abort.

  Lemma extract_indep_post: forall st (ipost: Prop) (dpost: RiscvMachineL -> Prop),
      (forall st, dpost st -> ipost) ->
      runsTo (mcomp_sat (run1 iset)) st dpost ->
      ipost.
  Proof.
    induction 2.
    - eauto.
    - eapply H2. 2: eassumption.
      (* Core problem in nicening the final statement:
         this does not hold if there are interactions which result in the empty set
         of outcomes ("overly friendly spec for compilers", not usually the case) *)
  Abort.

  Lemma use_strengthen_safe1: forall (good_trace: trace -> Prop),
      (forall st, safe1 st -> good_trace st.(getLog)) ->
      forall st,
        runsTo (mcomp_sat (run1 iset)) st safe1 ->
        runsTo (mcomp_sat (run1 iset)) st (fun final => safe1 final /\
                                           exists rest, good_trace (getLog st ++ rest)).
  Proof.
    intros.
  Abort.

  (* forall n, after running for n steps, we're only "a runsTo away" from a good state *)
  Lemma safe_forever_aux_prefix: forall (good_trace: trace -> Prop),
      (forall st, safe1 st -> good_trace st.(getLog)) ->
      forall (n: nat) (st: RiscvMachineL),
      runsTo (mcomp_sat (run1 iset)) st safe1 -> (* <-- follows from "safe1 st" using runsToDone *)
      mcomp_sat (runN n) st
                (fun prefinalL => runsTo (mcomp_sat (run1 iset)) prefinalL safe1 /\
                                  exists rest, good_trace (getLog st ++ rest)).
  Proof.
    induction n; intros.
    - simpl. apply go_done. split.
      + assumption.
      + exists nil. rewrite List.app_nil_r. eauto.
  Abort.

  Lemma extend_runsTo_to_good_trace: forall (good_trace: trace -> Prop),
      (forall st, safe1 st -> good_trace st.(getLog)) ->
      forall (st : RiscvMachineL),
        runsTo (mcomp_sat (run1 iset)) st safe1 ->
        exists rest : trace, good_trace (getLog st ++ rest).
  Proof.
    intros ? safe2good st R. induction R.
    - exists nil. rewrite List.app_nil_r. eauto.
    - (* does not hold if there are interactions which result in the empty set
         of outcomes ("overly friendly spec for compilers", not usually the case) *)
  Abort.

  Lemma trace_prefix_of_good: forall (good_trace: trace -> Prop),
      (forall st, safe1 st -> good_trace st.(getLog)) ->
      forall n st,
        safe1 st ->
        mcomp_sat (runN n) st
                  (fun st' => exists rest, good_trace (st'.(getLog) ++ rest)).
  Proof.
    intros.
    eapply mcomp_sat_weaken; cycle 1.
    - eapply safe_forever. apply runsToDone. assumption.
    - simpl. intros.
  Abort.

  Lemma trace_prefix_of_good: forall (good_trace: trace -> Prop),
      (forall st, safe1 st -> good_trace st.(getLog)) ->
      forall n st,
        runsTo (mcomp_sat (run1 iset)) st safe1 ->
        mcomp_sat (runN n) st
                  (fun st' => exists rest, good_trace (st'.(getLog) ++ rest)).
  Proof.
    induction n; intros.
    - simpl. apply go_done. exists nil. rewrite List.app_nil_r. eauto.
  Abort.

  Lemma trace_prefix_of_good: forall (good_trace: trace -> Prop),
      (forall st, safe1 st -> good_trace st.(getLog)) ->
      forall n st,
        safe1 st ->
        mcomp_sat (runN n) st
                  (fun st' => exists rest, good_trace (st'.(getLog) ++ rest)).
  Proof.
    induction n; intros.
    - simpl. apply go_done. exists nil. rewrite List.app_nil_r. eauto.
    - simpl. eapply spec_Bind_unit.
  Abort.

(*
  (* forall n, after running for n steps, we're only "a runsTo away" from a good state.
     That is, "runs to a good state" is an invariant of the system *)
  Lemma safe_forever_aux: forall (n m: nat) (initialL: RiscvMachineL),
      (m < n)%nat ->
      safe1 initialL \/ safe2 initialL ->
      mcomp_sat (runN m) initialL
                (fun prefinalL => runsTo (mcomp_sat (run1 iset)) prefinalL safe1).
  Proof.

  (* forall n, after running for n steps, we're only "a runsTo away" from a good state.
     That is, "runs to a good state" is an invariant of the system *)
  Lemma safe_forever_aux: forall (n m: nat) (initialL: RiscvMachineL),
      (m < n)%nat ->
      safe1 initialL \/ safe2 initialL ->
      mcomp_sat (runN m) initialL
                (fun prefinalL => runsTo (mcomp_sat (run1 iset)) prefinalL safe1).
  Proof.


  (* forall n, after running for n steps, we're only "a runsTo away" from a good state *)
  Lemma safe_forever_aux: forall (n m: nat) (initialL: RiscvMachineL),
      (m < n)%nat ->
      safe1 initialL \/ safe2 initialL ->
      mcomp_sat (runN m) initialL
                (fun prefinalL => runsTo (mcomp_sat (run1 iset)) prefinalL safe1).
  Proof.
    induction n; intros.
    - exfalso. blia.
    - simpl.
      destruct H0.
      + specialize (run_1_2 _ H0). revert run_1_2.
        (* here, figure out how to do parallel runsTo and mcomp_sat (runN m)) *)

        induction 1; rename P into safe2.
        * exfalso. eapply exclusive; eauto.
        * destruct m.
          -- simpl. apply go_done. apply runsToDone. assumption.
          -- simpl.
             eapply spec_Bind_unit. 1: eassumption.
             intros.
             rename H3 into IH.
             specialize (IH _ H4 exclusive).
             specialize (H2 _ H4).
             specialize (IH H2).
             specialize (IH run_2_1).
             specialize (IH IHn).



             apply Lt.lt_S_n in H. specialize IHn with (1 := H).

  (* forall n, after running for n steps, we're only "a runsTo away" from a good state *)
  Lemma safe_forever_aux: forall (n: nat) (initialL: RiscvMachineL),
      (safe1 initialL ->
       mcomp_sat (runN n) initialL
                 (fun prefinalL => runsTo (mcomp_sat (run1 iset)) prefinalL safe1)) /\
      (safe2 initialL ->
       mcomp_sat (runN n) initialL
                 (fun prefinalL => runsTo (mcomp_sat (run1 iset)) prefinalL safe2)).
  Proof.
    induction n; split; intros.
    - simpl. apply go_done.
      apply runsToDone. assumption.
    - simpl. apply go_done.
      apply runsToDone. assumption.
    - simpl.
      specialize (run_1_2 _ H). inversion run_1_2.
      + exfalso. eapply exclusive; eauto.
      + eapply spec_Bind_unit. 1: eassumption.
        intros.
        specialize (H1 _ H2).
        specialize (IHn middle).



  (* forall n, after running for n steps, we're only "a runsTo away" from a good state *)
  Lemma safe_forever_aux: forall (n: nat) (initialL: RiscvMachineL),
      safe1 initialL \/ safe2 initialL ->
      mcomp_sat (runN n) initialL
                (fun prefinalL => runsTo (mcomp_sat (run1 iset)) prefinalL safe1).
  Proof.
    induction n; intros.
    - simpl. apply go_done.
      destruct H.
      + apply runsToDone. assumption.
      + apply run_2_1. assumption.
    - simpl.
      destruct H.
      + specialize (run_1_2 _ H). inversion run_1_2.
        * exfalso. eapply exclusive; eauto.
        * eapply spec_Bind_unit. 1: eassumption.
          intros.
          specialize (H1 _ H2).
          eapply IHn.

      +
          mcomp_sat_weaken

      specialize (IHn _ H).

      +


  (* forall n, after running for n steps, we're only "a runsTo away" from a good state *)
  Lemma safe_forever: forall (n: nat) (initialL: RiscvMachineL),
      safe1 initialL ->
      mcomp_sat (runN n) initialL (fun prefinalL => runsTo (mcomp_sat (run1 iset)) prefinalL safe1).
  Proof.
    induction n; intros.
    - simpl. apply go_done. apply runsToDone. assumption.
    - simpl. eapply spec_Bind_unit.

  Abort.
*)

End ForeverSafe.
