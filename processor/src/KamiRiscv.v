Require Import Coq.ZArith.ZArith.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Kami.Lib.Word.
Require Import riscv.Decode.
Require Import riscv.Encode.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Utility.
Require Import riscv.Primitives.
Require Import riscv.RiscvMachine.
Require Import riscv.Program.
Require riscv.Memory.
Require Import riscv.PseudoInstructions.
Require Import riscv.proofs.EncodeBound.
Require Import riscv.proofs.DecodeEncode.
Require Import riscv.Run.
Require Import riscv.MkMachineWidth.
Require Import riscv.util.Monads.
Require Import riscv.runsToNonDet.
Require Import coqutil.Datatypes.PropSet.
Require Import riscv.MMIOTrace.
Require Import Kami.Ex.MemTypes.
Require Import Kami.Ex.SCMMTrace.
Require Import Kami.Ex.SC.
Require Import Kami.Semantics.

Local Open Scope Z_scope.

Definition kword(w: Z): Type := Kami.Lib.Word.word (Z.to_nat w).

Module KamiMachine.
  Record t(width: Z) := {
    pgm: kword width -> kword 32;
    rf: kword 5 -> kword width;
    pc: kword width;
    mem: kword width -> kword width
  }.
End KamiMachine.

Section Equiv.

  (* TODO not sure if we want to use ` or rather a parameter record *)
  Context {M: Type -> Type}.
  Context `{Pr: Primitives MMIOAction M}.
  Context {RVS: RiscvState M word}.
  Notation RiscvMachine := (RiscvMachine Register MMIOAction).

  Definition iset: InstructionSet := if width =? 32 then RV32IM else RV64IM.

  Definition NOP: w32 := LittleEndian.split 4 (encode (IInstruction Nop)).

  Definition KamiMachine := KamiMachine.t width.

  Definition KamiRegsToKamiMachine(k: RegsT): RiscvMachine. Admitted.

  Definition fromKami_withLog(k: KamiMachine)(t: list (LogItem MMIOAction)): RiscvMachine.
  Admitted.
(*
 := {|
    getRegs := map.empty;
    getPc := f.(counter);
    getNextPc := f.(nextCounter);
    getMem := Memory.unchecked_store_bytes 4 map.empty f.(counter) NOP;
    getLog := t;
  |}.
*)

(*
  Record FakeProcessor := {
    counter: word;
    nextCounter: word;
  }.

  Definition fromFake_withLog(f: FakeProcessor)(t: list (LogItem MMIOAction)): RiscvMachine := {|
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
  Inductive events_related: Event -> LogItem MMIOAction -> Prop :=
  | relate_MMInput: forall m addr v,
      events_related (MMInputEvent addr v) ((m, MMInput, [addr]), (m, [v]))
  | relate_MMOutput: forall m addr v,
      events_related (MMOutputEvent addr v) ((m, MMOutput, [addr; v]), (m, [])).

  (* given a kami trace, assert that there exists list of memories s.t zipped together,
     we get bedrock2 trace ? *)

  Inductive traces_related: list Event -> list (LogItem MMIOAction) -> Prop :=
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
  Inductive riscvStep: RiscvMachine -> RiscvMachine -> list (LogItem MMIOAction) -> Prop :=
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
*)
End Equiv.
