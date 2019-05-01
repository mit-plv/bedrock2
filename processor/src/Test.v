Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.Machine.
Require riscv.Platform.Memory.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Proofs.EncodeBound.
Require Import riscv.Proofs.DecodeEncode.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.runsToNonDet.
Require Import coqutil.Datatypes.PropSet.
Require Import riscv.Utility.MMIOTrace.
Require Import riscv.Platform.RiscvMachine.

Local Open Scope Z_scope.

Section Equiv.

  (* TODO not sure if we want to use ` or rather a parameter record *)
  Context `{Pr: Primitives}.
  Context {RVS: riscv.Spec.Machine.RiscvMachine M word}.

  Definition iset: InstructionSet := if width =? 32 then RV32IM else RV64IM.

  Definition NOP: w32 := LittleEndian.split 4 (encode (IInstruction Nop)).

  Record FakeProcessor := {
    counter: word;
    nextCounter: word;
  }.

  Definition fromFake_withLog(f: FakeProcessor)(t: list LogItem): RiscvMachine := {|
    getRegs := map.empty;
    getPc := f.(counter);
    getNextPc := f.(nextCounter);
    getMem := Memory.unchecked_store_bytes 4 map.empty f.(counter) NOP;
    getLog := t;
  |}.

  (* common event between riscv-coq and Kami *)
  Inductive Event: Type :=
  | MMInputEvent(addr v: word)
  | MMOutputEvent(addr v: word).

  (* note: memory can't change *)
  Inductive events_related: Event -> LogItem -> Prop :=
  | relate_MMInput: forall m addr v,
      events_related (MMInputEvent addr v) ((m, MMInput, [addr]), (m, [v]))
  | relate_MMOutput: forall m addr v,
      events_related (MMOutputEvent addr v) ((m, MMOutput, [addr; v]), (m, [])).

  (* given a kami trace, assert that there exists list of memories s.t zipped together,
     we get bedrock2 trace ? *)

  Inductive traces_related: list Event -> list LogItem -> Prop :=
  | relate_nil:
      traces_related nil nil
  | relate_cons: forall e e' t t',
      events_related e e' ->
      traces_related t t' ->
      traces_related (e :: t) (e' :: t').

  (* redefine mcomp_sat to simplify for the case where no answer is returned *)
  Definition mcomp_sat_unit(m: M unit)(initialL: RiscvMachine)(post: RiscvMachine -> Prop): Prop :=
    mcomp_sat m initialL (fun (_: unit) => post).

  (* list is kind of redundant (already in RiscvMachine.(getLog)))
     and should at most contain one event,
     but we still want it to appear in the signature so that we can easily talk about prefixes,
     and to match Kami's step signature *)
  Inductive riscvStep: RiscvMachine -> RiscvMachine -> list LogItem -> Prop :=
  | mk_riscvStep: forall initialL finalL t post,
      mcomp_sat_unit (run1 iset) initialL post ->
      post finalL ->
      finalL.(getLog) = t ++ initialL.(getLog) ->
      riscvStep initialL finalL t.

  Inductive star{S E: Type}(R: S -> S -> list E -> Prop): S -> S -> list E -> Prop :=
  | star_refl: forall (x: S),
      star R x x nil
  | star_step: forall (x y z: S) (t1 t2: list E),
      star R x y t1 ->
      R y z t2 ->
      star R x z (t2 ++ t1).

  (* temporal prefixes, new events are added in front of the head of the list *)
  Definition prefixes{E: Type}(traces: list E -> Prop): list E -> Prop :=
    fun prefix => exists rest, traces (rest ++ prefix).

  Definition riscvTraces(initial: RiscvMachine): list Event -> Prop :=
    fun t => exists final t', star riscvStep initial final t' /\ traces_related t t'.

  Definition post_to_traces(post: RiscvMachine -> Prop): list Event -> Prop :=
    fun t => exists final, post final /\ traces_related t final.(getLog).

  Definition runsTo: RiscvMachine -> (RiscvMachine -> Prop) -> Prop :=
    runsTo (mcomp_sat_unit (run1 iset)).

  Lemma bridge(init: RiscvMachine)(post: RiscvMachine -> Prop):
    runsTo init post ->
    subset (riscvTraces init) (prefixes (post_to_traces post)).
  Admitted.

  Axiom fakestep: FakeProcessor -> FakeProcessor -> list Event -> Prop.

  Lemma simulate_bw_step: forall (m1 m2: FakeProcessor) (t: list Event),
      fakestep m1 m2 t ->
      exists t', riscvStep (fromFake_withLog m1 nil) (fromFake_withLog m2 t') t' /\
                 traces_related t t'.
  Proof.
    intros.
  Admitted.

  Section Lift.
    Context {S1 S2 E1 E2: Type}.
    Context (step1: S1 -> S1 -> list E1 -> Prop).
    Context (step2: S2 -> S2 -> list E2 -> Prop).
    Context (convert_state: S1 -> S2) (convert_event: E1 -> E2).
    Hypothesis sim: forall s1 s1' t1,
        step1 s1 s1' t1 ->
        step2 (convert_state s1) (convert_state s1') (List.map convert_event t1).

    Lemma lift_star_simulation: forall s1 s1' t1,
        star step1 s1 s1' t1 ->
        star step2 (convert_state s1) (convert_state s1') (List.map convert_event t1).
    Proof.
      induction 1; [apply star_refl|].
      rewrite map_app.
      eapply star_step.
      - apply IHstar.
      - eapply sim. assumption.
    Qed.
  End Lift.

  Lemma simulate_bw_star: forall (m1 m2: FakeProcessor) (t: list Event),
      star fakestep m1 m2 t ->
      exists t', star riscvStep (fromFake_withLog m1 nil) (fromFake_withLog m2 t') t' /\
                 traces_related t t'.
  Proof.
    (* TODO
       apply lift_star_simulation
       doesn't work any more .
       apply simulate_bw_step. *)
  Admitted.

  Definition fakeTraces(init: FakeProcessor): list Event -> Prop :=
    fun t => exists final, star fakestep init final t.

  Lemma connection: forall (m: FakeProcessor),
      subset (fakeTraces m) (riscvTraces (fromFake_withLog m nil)).
  Proof.
    intros m t H. unfold fakeTraces, riscvTraces in *.
    destruct H as [m' H].
    apply simulate_bw_star in H. destruct H as (t' & H).
    do 2 eexists. exact H.
  Qed.

  (* assume this first converts the FakeProcessor from SpecProcessor to ImplProcessor state,
     and also converts from Kami trace to common trace *)
  Definition kamiImplTraces(init: FakeProcessor): list Event -> Prop. Admitted.

  Axiom kamiImplSoundness: forall (init: FakeProcessor),
      subset (kamiImplTraces init) (fakeTraces init).

  Lemma subset_trans{A: Type}(s1 s2 s3: A -> Prop):
    subset s1 s2 ->
    subset s2 s3 ->
    subset s1 s3.
  Proof. unfold subset. auto. Qed.

  Lemma subset_refl{A: Type}(s: A -> Prop): subset s s. Proof. unfold subset. auto. Qed.

  Lemma impl_to_end_of_compiler(init: FakeProcessor)(post: RiscvMachine -> Prop):
      runsTo (fromFake_withLog init nil) post -> (* <-- will be proved by bedrock2 program logic & compiler *)
      subset (kamiImplTraces init) (prefixes (post_to_traces post)).
  Proof.
    intro H.
    eapply subset_trans; [apply kamiImplSoundness|].
    eapply subset_trans; [|apply bridge; eassumption].
    eapply subset_trans; [apply connection|].
    apply subset_refl.
  Qed.

  (* TODO in bedrock2: differential memory in trace instead of whole memory ?

     or say: kami trace related to bedrock2 trace if memory doesn't change and IO matches
  *)

  (* note: only holds if the nondet machine never picks an arbitrary value of the empty set,
     which is the case for all riscv machines, but not for a more abstract runsTo,
     and also requires no memory-changing or invalid events *)
  Lemma pick_from_runsTo: forall init post,
      runsTo init post ->
      exists final, post final. (* /\ traces_related t final.(getLog).*) (* and steps there? *)
  Admitted.

  Lemma simulate_multistep: forall (init final: FakeProcessor) (t: list Event),
      star fakestep init final t ->
      forall (post: RiscvMachine -> Prop),
      (forall m, post m -> exists t, traces_related t m.(getLog)) -> (* no malformed traces *)
      runsTo (fromFake_withLog init nil) post ->
      exists (rest : list Event) (final : RiscvMachine),
        post final /\ traces_related (rest ++ t) final.(getLog).
  Proof.
    induction 1; intros post C R.
    - apply pick_from_runsTo in R. destruct R as (final & R).
      specialize (C final R). destruct C as [t C].
      exists t. exists final. rewrite app_nil_r. auto.
    - inversion R.
      + (* riscv-coq is done *)
        specialize (C (fromFake_withLog x nil) H1). destruct C as [t C].
        exists (firstn (length t - (length t2 + length t1)) t).
        exists (fromFake_withLog x nil). split; auto.
        replace (firstn (length t - (length t2 + length t1)) t ++ t2 ++ t1) with t by admit.
        exact C.

      (* what if the fake machine steps further than the riscv spec machine?
         Then it's supposed to be silent (creating no events).
         But where do we show that?
         -> Problem: from_Fake should take in trace to add  *)
  Abort.

  Lemma impl_to_end_of_compiler_in_one_go(init: FakeProcessor)(post: RiscvMachine -> Prop):
      runsTo (fromFake_withLog init nil) post -> (* <-- will be proved by bedrock2 program logic & compiler *)
      subset (fakeTraces init) (prefixes (post_to_traces post)).
  Proof.
    intros R t H. unfold fakeTraces in *.
    unfold prefixes, post_to_traces.
  Abort.

  (** -- old -- *)

  Definition fakeStep: FakeProcessor -> FakeProcessor :=
    fun '(Build_FakeProcessor c nc) => Build_FakeProcessor nc (word.add nc (word.of_Z 4)).

  Definition from_Fake(f: FakeProcessor): RiscvMachine := {|
    getRegs := map.empty;
    getPc := f.(counter);
    getNextPc := f.(nextCounter);
    getMem := Memory.unchecked_store_bytes 4 map.empty f.(counter) NOP;
    getLog := nil;
  |}.

  Definition to_Fake(m: RiscvMachine): FakeProcessor := {|
    counter := m.(getPc);
    nextCounter := m.(getNextPc);
  |}.

  Arguments Memory.unchecked_store_bytes: simpl never.

  Lemma combine_split: forall (n: nat) (z: Z),
      0 <= z < 2 ^ (Z.of_nat n * 8) ->
      combine n (split n z) = z.
  Proof.
    intros. rewrite LittleEndian.combine_split.
    apply Z.mod_small.
    assumption.
  Qed.

  Hypothesis assume_no_MMIO: forall n mach addr post,
      ~ mcomp_sat (nonmem_load n addr) mach post.

  Lemma simulate_step_fw: forall (initial: RiscvMachine)
                                 (post: RiscvMachine -> Prop),
      (* begin additional hypotheses which should be deleted in a real proof *)
      Memory.loadWord initial.(getMem) initial.(getPc) = Some NOP ->
      (forall machine1 machine2,
          post machine1 ->
          machine1.(getPc) = machine2.(getPc) ->
          machine1.(getNextPc) = machine2.(getNextPc) ->
          post machine2) ->
      (* end hypotheses to be deleted *)
      mcomp_sat (run1 iset) initial (fun _ => post) ->
      post (from_Fake (fakeStep (to_Fake initial))).
  Proof.
    intros *. intros AllNOPs postOnlyLooksAtPc H.
    destruct initial as [r pc npc m l].
    unfold to_Fake, fakeStep, from_Fake.
    simpl.
    unfold run1 in H.
    apply spec_Bind in H. destruct_products.
    apply spec_getPC in Hl. simpl in Hl.
    specialize Hr with (1 := Hl). clear Hl.
    apply spec_Bind in Hr. destruct_products.
    apply spec_loadWord in Hrl.
    destruct Hrl as [A | [_ A]]; [|exfalso; eapply assume_no_MMIO; exact A].
    destruct_products.
    simpl in Al, AllNOPs. rewrite AllNOPs in Al. inversion Al. subst v. clear Al.
    specialize Hrr with (1 := Ar). clear Ar.
    apply spec_Bind in Hrr. destruct_products.
    unfold NOP in Hrrl.
    rewrite combine_split in Hrrl by apply (encode_range (IInstruction Nop)).
    rewrite decode_encode in Hrrl by (cbv; clear; intuition congruence).
    simpl in Hrrl.
    apply spec_Bind in Hrrl. destruct_products.
    apply spec_getRegister in Hrrll.
    destruct Hrrll as [[[A _] _] | [_ A]]; [ cbv in A; discriminate A | ].
    specialize Hrrlr with (1 := A). clear A.
    apply spec_setRegister in Hrrlr.
    destruct Hrrlr as [[[A _] _] | [_ A]]; [ cbv in A; discriminate A | ].
    specialize Hrrr with (1 := A). clear A.
    apply spec_step in Hrrr. unfold withPc, withNextPc in Hrrr. simpl in Hrrr.
    eapply postOnlyLooksAtPc; [eassumption|reflexivity..].
  Qed.

  Ltac det_step :=
    match goal with
    | |- exists (_: ?A -> ?Mach -> Prop), _ =>
      let a := fresh "a" in evar (a: A);
      let m := fresh "m" in evar (m: Mach);
      exists (fun a0 m0 => a0 = a /\ m0 = m);
      subst a m
    end.

  Lemma loadWord_store_bytes_same: forall m w addr,
      Memory.loadWord (Memory.unchecked_store_bytes 4 m addr w) addr = Some w.
  Admitted. (* TODO once we have a good map solver and word solver, this should be easy *)

  Lemma to_Fake_from_Fake: forall (m: FakeProcessor),
      to_Fake (from_Fake m) = m.
  Proof.
    intros. destruct m. reflexivity.
  Qed.

  Lemma from_Fake_to_Fake: forall (m: RiscvMachine),
      from_Fake (to_Fake m) = m.
  Proof.
    intros. destruct m. unfold to_Fake, from_Fake. simpl.
    (* Doesn't hold for the fake processor! *)
  Admitted.

  Lemma simulate_step_bw: forall (m m': FakeProcessor),
      fakeStep m = m' ->
      mcomp_sat (run1 iset) (from_Fake m) (fun _ final => to_Fake final = m').
  Proof.
    intros. subst m'. destruct m. unfold from_Fake, to_Fake, fakeStep, run1.
    apply spec_Bind.
    det_step. split.
    { simpl. apply spec_getPC. simpl. split; reflexivity. }
    intros. destruct_products. subst.
    apply spec_Bind.
    det_step. split.
    { apply spec_loadWord.
      left.
      exists NOP.
      repeat split. (* also invokes reflexivity *)
      simpl.
      apply loadWord_store_bytes_same. }
    intros. destruct_products. subst.
    apply spec_Bind.
    det_step. split.
    { unfold NOP at 1.
      rewrite combine_split by apply (encode_range (IInstruction Nop)).
      rewrite decode_encode by (cbv; clear; intuition congruence).
      simpl.
      apply spec_Bind.
      det_step. split.
      { apply spec_getRegister.
        simpl.
        right.
        repeat split. }
      intros. destruct_products. subst.
      apply spec_setRegister.
      right.
      repeat split. }
    intros. destruct_products. subst.
    apply spec_step. simpl. reflexivity.
  Qed.

  Lemma step_equiv_too_weak: forall (m m': FakeProcessor),
      fakeStep m = m' <->
      mcomp_sat (run1 iset) (from_Fake m) (fun _ final => to_Fake final = m').
  Proof.
    intros. split.
    - apply simulate_step_bw.
    - intros.
      pose proof (simulate_step_fw (from_Fake m) (fun final => to_Fake final = m')) as P.
      simpl in P.
      rewrite to_Fake_from_Fake in P.
      unfold fakeStep. destruct m.
      apply P; clear P.
      + intros. apply loadWord_store_bytes_same.
      + intros. destruct machine1, machine2. unfold to_Fake in *; simpl in *. congruence.
      + assumption.
  Qed.

  Lemma weaken_mcomp_sat:
    forall A m initial (post1 post2: A -> RiscvMachine -> Prop),
      mcomp_sat m initial post1 ->
      (forall (a: A) final, post1 a final -> post2 a final) ->
      mcomp_sat m initial post2.
  Proof.
    intros.
    rewrite <- (right_identity m).
    apply spec_Bind.
    exists post1.
    split; [assumption|].
    intros.
    apply spec_Return.
    apply H0.
    assumption.
  Qed.

  Lemma step_equiv: forall (initial: RiscvMachine)
                           (post: RiscvMachine -> Prop),
      post (from_Fake (fakeStep (to_Fake initial))) <->
      mcomp_sat (run1 iset) initial (fun _ => post).
  Proof.
    intros. split; intros.
    - pose proof (simulate_step_bw (to_Fake initial)) as P.
      rewrite from_Fake_to_Fake in P.
      eapply weaken_mcomp_sat.
      + eapply P. reflexivity.
      + intros. destruct initial. simpl in *.
        rewrite <- H0 in H.
        rewrite from_Fake_to_Fake in H.
        exact H.
    - intros.
      eapply simulate_step_fw.
      3: exact H.
      (* the remaining two goals are assumptions which should be removed from simulate_step_fw,
         so once that's done, we'll be able to Qed this *)
  Abort.

End Equiv.
