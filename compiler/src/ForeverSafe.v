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

  Local Notation trace := (list LogItem).
  Import Coq.Lists.List.
  Import ListNotations.

  (* monadic computations used for specifying the behavior of RiscvMachines should be "sane"
     in the sense that we never step to the empty set (that's not absence of failure, since
     failure is modeled as "steps to no set at all"), and that the trace of events is
     append-only *)
  Definition mcomp_sane{A: Type}(comp: M A): Prop :=
    forall (st: RiscvMachineL) (post: A -> RiscvMachineL -> Prop),
      Primitives.mcomp_sat comp st post ->
      (exists a st', post a st') /\
      (forall a st', post a st' -> exists diff, st'.(getLog) = diff ++ st.(getLog)).

  Class PrimitivesSane := {
    getRegister_sane: forall r, mcomp_sane (getRegister r);
    setRegister_sane: forall r v, mcomp_sane (setRegister r v);
    loadByte_sane: forall kind addr, mcomp_sane (loadByte kind addr);
    loadHalf_sane: forall kind addr, mcomp_sane (loadHalf kind addr);
    loadWord_sane: forall kind addr, mcomp_sane (loadWord kind addr);
    loadDouble_sane: forall kind addr, mcomp_sane (loadDouble kind addr);
    storeByte_sane: forall kind addr v, mcomp_sane (storeByte kind addr v);
    storeHalf_sane: forall kind addr v, mcomp_sane (storeHalf kind addr v);
    storeWord_sane: forall kind addr v, mcomp_sane (storeWord kind addr v);
    storeDouble_sane: forall kind addr v, mcomp_sane (storeDouble kind addr v);
    getPC_sane: mcomp_sane getPC;
    setPC_sane: forall newPc, mcomp_sane (setPC newPc);
    step_sane: mcomp_sane step;
    raiseExceptionWithInfo_sane: forall A i1 i2 i3,
        mcomp_sane (raiseExceptionWithInfo (A := A) i1 i2 i3);
  }.

  Context {PrSane: PrimitivesSane}.

  Lemma Bind_sane: forall {A B: Type} (m: M A) (f: A -> M B),
      mcomp_sane m ->
      (forall a, mcomp_sane (f a)) ->
      mcomp_sane (Bind m f).
  Proof.
    intros *.
    intros S1 S2.
    unfold mcomp_sane in *.
    intros.
    eapply (proj2 (spec_Bind _ _ _ _)) in H.
    destruct H as (mid & C1 & C2).
    specialize S1 with (1 := C1). destruct S1 as ((a & middle & S1a) & S1b).
    specialize C2 with (1 := S1a).
    specialize S1b with (1 := S1a). destruct S1b as (diff1 & S1b).
    specialize S2 with (1 := C2). destruct S2 as ((b & final & S2a) & S2b).
    split.
    - eauto.
    - intros.
      specialize S2b with (1 := H). destruct S2b as (diff2 & S2b).
      rewrite S1b in S2b.
      rewrite List.app_assoc in S2b.
      eexists. exact S2b.
  Qed.

  Lemma Return_sane: forall {A: Type} (a: A),
      mcomp_sane (Return a).
  Proof.
    unfold mcomp_sane.
    intros.
    split.
    - eapply spec_Return in H. eauto.
    - assert (post = fun _ _ => True) by admit. subst post. intros.
      (* counterexample! *)
  Abort.

  Lemma execute_sane: forall inst,
      mcomp_sane (Execute.execute inst).
  Proof.
    intros.
    destruct inst as [inst | inst | inst | inst | inst | inst | inst | inst | inst | inst];
      simpl; try apply raiseExceptionWithInfo_sane;
      destruct inst; simpl;
    repeat first [ apply Bind_sane
                 | apply getRegister_sane
                 | apply setRegister_sane
                 | apply loadByte_sane
                 | apply loadHalf_sane
                 | apply loadWord_sane
                 | apply loadDouble_sane
                 | apply storeByte_sane
                 | apply storeHalf_sane
                 | apply storeWord_sane
                 | apply storeDouble_sane
                 | apply getPC_sane
                 | apply setPC_sane
                 | apply step_sane
                 | apply raiseExceptionWithInfo_sane
                 | progress intros ].

  Admitted.

  Lemma run1_sane: mcomp_sane (run1 iset).
  Proof.
    unfold run1.
    apply Bind_sane; [apply getPC_sane|intros].
    apply Bind_sane; [apply loadWord_sane|intros].
    apply Bind_sane; [apply execute_sane|intros].
    apply step_sane.
  Qed.

  (* does not hold if there are interactions which result in the empty set
     of outcomes ("overly friendly spec for compilers", not usually the case) *)
  Hypothesis run1_nonempty: forall initial final,
      mcomp_sat (run1 iset) initial final ->
      exists st, final st.

  Hypothesis run1_log_monotone: forall (initial: RiscvMachineL) (final: RiscvMachineL -> Prop),
      mcomp_sat (run1 iset) initial final ->
      forall st, final st -> exists diff, st.(getLog) = diff ++ initial.(getLog).

  Lemma extend_runsTo_to_good_trace: forall (good_trace: trace -> Prop),
      (forall st, safe1 st -> good_trace st.(getLog)) ->
      forall (st : RiscvMachineL),
        runsTo (mcomp_sat (run1 iset)) st safe1 ->
        exists rest : trace, good_trace (rest ++ getLog st).
  Proof.
    intros ? safe2good st R. induction R.
    - exists nil. rewrite List.app_nil_l. eauto.
    - rename P into safe1.
      pose proof (run1_nonempty _ _ H) as N. destruct N as (mid & Hmid).
      specialize (H1 _ Hmid exclusive run_1_2 run_2_1 safe2good).
      destruct H1 as (rest & H1).
      destruct (run1_log_monotone _ _ H mid Hmid) as (diff & E).
      rewrite E in H1.
      rewrite List.app_assoc in H1.
      eexists. exact H1.
  Qed.

  (* forall n, after running for n steps, we've output a prefix of a good trace.
     The precondition can either be trivially established using runsToDone if safe1 already
     holds, or it can be established by some initialization code which runs before the main
     event loop. *)
  Lemma prefix_of_good_inv: forall (good_trace: trace -> Prop),
      (forall st, safe1 st -> good_trace st.(getLog)) ->
      forall (n: nat) (st: RiscvMachineL),
      runsTo (mcomp_sat (run1 iset)) st safe1 ->
      mcomp_sat (runN n) st (fun st' => exists rest : trace, good_trace (rest ++ getLog st')).
  Proof.
    intros ? safe2good n st R.
    eapply mcomp_sat_weaken; cycle 1.
    - eapply safe_forever. assumption.
    - simpl. intros.
      eapply extend_runsTo_to_good_trace; eassumption.
  Qed.

End ForeverSafe.
