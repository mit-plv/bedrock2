Require Import String.
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
Require Import processor.KamiWord.
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
Require Import Kami.Syntax Kami.Semantics.
Require Import Kami.Tactics.

Local Open Scope Z_scope.

Definition kword(w: Z): Type := Kami.Lib.Word.word (Z.to_nat w).

Module KamiRecord.

  Section Width.
    Context {width: Z}.

    Record t :=
      { pgm: kword width -> kword 32;
        rf: kword 5 -> kword width;
        pc: kword width;
        mem: kword width -> kword width
      }.

    Local Definition nwidth := Z.to_nat width.

    Definition RegsToT (r: RegsT): option t :=
      (mlet pgmv: (Vector (Bit 32) nwidth) <- r |> "pgm" <| None;
         mlet rfv: (Vector (Bit nwidth) 5) <- r |> "rf" <| None;
         mlet pcv: (Bit nwidth) <- r |> "pc" <| None;
         mlet memv: (Vector (Bit nwidth) nwidth) <- r |> "mem" <| None;
         (Some {| pgm := pgmv;
                  rf := rfv;
                  pc := pcv;
                  mem := memv |}))%mapping.

  End Width.
  Arguments t: clear implicits.
End KamiRecord.

Section Equiv.

  (* TODO not sure if we want to use ` or rather a parameter record *)
  Context {M: Type -> Type}.
  Context {width : Z}.
  Context {width_cases : width = 32 \/ width = 64}.

  Instance W: Utility.Words := @KamiWord.WordsKami width width_cases.

  Context `{Pr: Primitives (W := W) MMIOAction M}.
  Context {RVS: RiscvState M word}.
  Notation RiscvMachine := (RiscvMachine Register MMIOAction).

  Definition iset: InstructionSet := if width =? 32 then RV32IM else RV64IM.

  Definition NOP: w32 := LittleEndian.split 4 (encode (IInstruction Nop)).

  Definition KamiMachine := RegsT.

  Definition convertRegs(rf: kword 5 -> kword width): Registers :=
    let kkeys := HList.tuple.unfoldn (wplus (natToWord 5 1)) 31 (natToWord 5 1) in
    let values := HList.tuple.map rf kkeys in
    let keys := HList.tuple.map (@wordToZ 5) kkeys in
    map.putmany_of_tuple keys values map.empty.

  (* kamiTODO: connect these two to Kami *)
  Definition instrMemSize: nat. Admitted.
  Definition dataMemSize: nat. Admitted.

  Definition instrMemStart: word := word.of_Z 0.
  Definition dataMemStart: word := word.of_Z (Z.of_nat (4 * instrMemSize)).

  Definition word32_to_4bytes(w: kword 32): HList.tuple byte 4 :=
    LittleEndian.split 4 (word.unsigned w).

  Definition convertInstrMem(instrMem: kword width -> kword 32): mem :=
    let keys := List.unfoldn (word.add (word.of_Z 4)) instrMemSize (word.of_Z 0) in
    let values := List.map (fun key => word32_to_4bytes (instrMem key)) keys in
    Memory.unchecked_store_byte_tuple_list instrMemStart values map.empty.

  Definition convertDataMem(dataMem: kword width -> kword width): mem :=
    let keys := List.unfoldn (word.add (word.of_Z (width / 8))) dataMemSize (word.of_Z 0) in
    let values := List.map (fun key => LittleEndian.split (Z.to_nat (width / 8))
                                                          (word.unsigned (dataMem key)))
                           keys in
    Memory.unchecked_store_byte_tuple_list dataMemStart values map.empty.

  Definition KamiRecord_to_RiscvMachine
             (k: KamiRecord.t width)(t: list (LogItem MMIOAction)): RiscvMachine :=
    {|
      getRegs := convertRegs (KamiRecord.rf k);
      getPc := KamiRecord.pc k;
      getNextPc := word.add (KamiRecord.pc k) (word.of_Z 4);
      getMem := map.putmany (convertInstrMem (KamiRecord.pgm k))
                            (convertDataMem (KamiRecord.mem k));
      getLog := t;
    |}.

  Definition fromKami_withLog(k: KamiMachine)(t: list (LogItem MMIOAction)): option RiscvMachine :=
    match KamiRecord.RegsToT k with
    | Some r => Some (KamiRecord_to_RiscvMachine r t)
    | None => None
    end.

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

  Definition kamiStep: KamiMachine -> KamiMachine -> list Event -> Prop. Admitted. (* TODO *)

  Lemma simulate_bw_step: forall (m1 m2: KamiMachine) (t: list Event),
      kamiStep m1 m2 t ->
      exists t' m1' m2',
        traces_related t t' /\
        fromKami_withLog m1 nil = Some m1' /\
        fromKami_withLog m2 t' = Some m2' /\
        riscvStep m1' m2' t'.
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

  Lemma simulate_bw_star: forall (m1 m2: KamiMachine) (t: list Event),
      star kamiStep m1 m2 t ->
      exists t' m1' m2',
        traces_related t t' /\
        fromKami_withLog m1 nil = Some m1' /\
        fromKami_withLog m2 t' = Some m2' /\
        star riscvStep m1' m2' t'.
  Proof.
    (* TODO
       apply lift_star_simulation
       doesn't work any more .
       apply simulate_bw_step. *)
  Admitted.

  Definition kamiTraces(init: KamiMachine): list Event -> Prop :=
    fun t => exists final, star kamiStep init final t.

  Lemma connection: forall (m: KamiMachine) (m': RiscvMachine),
      fromKami_withLog m nil = Some m' ->
      subset (kamiTraces m) (riscvTraces m').
  Proof.
    intros m1 m1' A t H. unfold kamiTraces, riscvTraces in *.
    destruct H as [m2 H].
    apply simulate_bw_star in H. destruct H as (t' & m1'' & m2' & R1 & R2 & R3 & R4).
    rewrite R2 in A. inversion A. clear A. subst m1''.
    eauto.
  Qed.

  (* assume this first converts the KamiMachine from SpecProcessor to ImplProcessor state,
     and also converts from Kami trace to common trace *)
  Definition kamiImplTraces(init: KamiMachine): list Event -> Prop. Admitted.

  Axiom kamiImplSoundness: forall (init: KamiMachine),
      subset (kamiImplTraces init) (kamiTraces init).

  Lemma subset_trans{A: Type}(s1 s2 s3: A -> Prop):
    subset s1 s2 ->
    subset s2 s3 ->
    subset s1 s3.
  Proof. unfold subset. auto. Qed.

  Lemma subset_refl{A: Type}(s: A -> Prop): subset s s. Proof. unfold subset. auto. Qed.

  Lemma impl_to_end_of_compiler
        (init: KamiMachine)(init': RiscvMachine)(post: RiscvMachine -> Prop):
      fromKami_withLog init nil = Some init' ->
      runsTo init' post -> (* <-- proved by bedrock2 *)
      subset (kamiImplTraces init) (prefixes (post_to_traces post)).
  Proof.
    intros E H.
    eapply subset_trans; [apply kamiImplSoundness|].
    eapply subset_trans; [|apply bridge; eassumption].
    eapply subset_trans; [apply connection; eassumption|].
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

  Lemma simulate_multistep: forall (init final: KamiMachine) (t: list Event),
      star kamiStep init final t ->
      forall (post: RiscvMachine -> Prop),
      (forall m, post m -> exists t, traces_related t m.(getLog)) -> (* no malformed traces *)
      forall (init': RiscvMachine),
      fromKami_withLog init nil = Some init' ->
      runsTo init' post ->
      exists (rest : list Event) (final : RiscvMachine),
        post final /\ traces_related (rest ++ t) final.(getLog).
  Proof.
    induction 1; intros post C init' E R.
    - apply pick_from_runsTo in R. destruct R as (final & R).
      specialize (C final R). destruct C as [t C].
      exists t. exists final. rewrite app_nil_r. auto.
    - inversion R.
      + (* riscv-coq is done *)
        edestruct C as [t D]; [eassumption|].
        exists (firstn (length t - (length t2 + length t1)) t).
        eexists; split; eauto.
        replace (firstn (length t - (length t2 + length t1)) t ++ t2 ++ t1) with t by admit.
        exact D.

      (* what if the fake machine steps further than the riscv spec machine?
         Then it's supposed to be silent (creating no events).
         But where do we show that?
         -> Problem: from_Fake should take in trace to add  *)
  Abort.

End Equiv.
