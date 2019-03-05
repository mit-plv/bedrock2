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
Require Import Kami.Syntax Kami.Semantics Kami.Tactics.
Require Import Kami.Ex.MemTypes Kami.Ex.SC Kami.Ex.SCMMInl.
Require Import Kami.Ex.IsaRv32.

Local Open Scope Z_scope.

Definition kword(w: Z): Type := Kami.Lib.Word.word (Z.to_nat w).

Definition width: Z := 32.
Definition width_cases: width = 32 \/ width = 64 := or_introl eq_refl.

Module KamiProc.

  Section Width.

    Local Definition nwidth := Z.to_nat width.

    Definition procInit: ProcInit nwidth rv32DataBytes rv32RfIdx :=
      {| pcInit := getDefaultConst _;
         rfInit := getDefaultConst _ |}.

    Definition isMMIO: IsMMIOT nwidth. Admitted.

    Definition proc: Kami.Syntax.Modules :=
      projT1 (@Kami.Ex.SCMMInl.scmmInl
                nwidth nwidth
                rv32InstBytes rv32DataBytes rv32RfIdx rv32GetOptype
                rv32GetLdDst (rv32GetLdAddr _) rv32GetLdSrc (rv32CalcLdAddr _)
                (rv32GetStAddr _) rv32GetStSrc (rv32CalcStAddr _) rv32GetStVSrc
                rv32GetSrc1 rv32GetSrc2 rv32GetDst (rv32Exec _)
                (rv32NextPc _) (rv32AlignPc _ _) (rv32AlignAddr _)
                isMMIO procInit).

    Record st :=
      mk { pc: kword width;
           rf: kword 5 -> kword width;
           pgm: kword width -> kword width;
           mem: kword width -> kword width
         }.

    Definition RegsToT (r: RegsT): option st :=
      (mlet pinit: Bool <- r |> "pinit" <| None;
         if pinit
         then (mlet pcv: (Bit nwidth) <- r |> "pc" <| None;
                 mlet rfv: (Vector (Bit nwidth) 5) <- r |> "rf" <| None;
                 mlet pinitOfs: (Bit nwidth) <- r |> "pinitOfs" <| None;
                 mlet pgmv: (Vector (Bit 32) nwidth) <- r |> "pgm" <| None;
                 mlet memv: (Vector (Bit nwidth) nwidth) <- r |> "mem" <| None;
                 (Some {| pc := pcv;
                          rf := rfv;
                          pgm := pgmv;
                          mem := memv |}))
         else None)%mapping.

  End Width.
  
  Arguments st: clear implicits.
  
End KamiProc.

Section Equiv.

  (* TODO not sure if we want to use ` or rather a parameter record *)
  Context {M: Type -> Type}.

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

  (** joonwonc: maybe below variables are related to the FIXME above. *)
  Variables instrMemSize dataMemSize: nat.

  Definition instrMemStart: word := word.of_Z 0.
  Definition dataMemStart: word := word.of_Z (Z.of_nat (4 * instrMemSize)).

  Definition word32_to_4bytes(w: kword 32): HList.tuple byte 4 :=
    LittleEndian.split 4 (word.unsigned w).

  Definition convertInstrMem(instrMem: kword width -> kword 32): mem :=
    let keys := List.unfoldn (word.add (word.of_Z 4)) instrMemSize instrMemStart in
    let values := List.map (fun key => word32_to_4bytes (instrMem key)) keys in
    Memory.unchecked_store_byte_tuple_list instrMemStart values map.empty.

  Definition convertDataMem(dataMem: kword width -> kword width): mem :=
    let keys := List.unfoldn (word.add (word.of_Z (width / 8))) dataMemSize dataMemStart in
    let values := List.map (fun key => LittleEndian.split (Z.to_nat (width / 8))
                                                          (word.unsigned (dataMem key)))
                           keys in
    Memory.unchecked_store_byte_tuple_list dataMemStart values map.empty.

  Definition KamiProc_st_to_RiscvMachine
             (k: KamiProc.st)(t: list (LogItem MMIOAction)): RiscvMachine :=
    {|
      getRegs := convertRegs (KamiProc.rf k);
      getPc := KamiProc.pc k;
      getNextPc := word.add (KamiProc.pc k) (word.of_Z 4);
      getMem := map.putmany (convertInstrMem (KamiProc.pgm k))
                            (convertDataMem (KamiProc.mem k));
      getLog := t;
    |}.

  Definition fromKami_withLog(k: KamiMachine)(t: list (LogItem MMIOAction)): option RiscvMachine :=
    match KamiProc.RegsToT k with
    | Some r => Some (KamiProc_st_to_RiscvMachine r t)
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

  (* "exists m', states_related (m, t) m'"
     might be simpler to use than
     "exists m' t', fromKami_withLog m t' = Some 2' /\ traces_related t t'"
     and require less unfolding/destructing *)
  Inductive states_related: KamiMachine * list Event -> RiscvMachine -> Prop :=
  | relate_states: forall t t' m pc rf instrMem dataMem,
      traces_related t t' ->
      KamiProc.RegsToT m = Some (KamiProc.mk pc rf instrMem dataMem) ->
      states_related (m, t) {| getRegs := convertRegs rf;
                               getPc := pc;
                               getNextPc := word.add pc (word.of_Z 4);
                               getMem := map.putmany (convertInstrMem instrMem)
                                                     (convertDataMem dataMem);
                               getLog := t'; |}.

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

  Definition KamiLabelR (klbl: Kami.Semantics.LabelT) (ev: list Event): Prop.
  Proof.
    refine (match FMap.M.find "mmioExec"%string klbl.(calls) with
            | Some sv => _
            | None => ev = nil
            end).
    destruct sv as [[argT retT] [argV retV]].
    destruct (decKind argT (Struct (RqFromProc (Z.to_nat width) rv32DataBytes)));
      [subst|exact False].
    destruct (decKind retT (Struct (RsToProc rv32DataBytes)));
      [subst|exact False].

    destruct (argV (Fin.FS Fin.F1)).
    - (* MMIO-store *)
      set (argV Fin.F1) as mmioAddr; simpl in mmioAddr.
      set (argV (Fin.FS (Fin.FS Fin.F1))) as mmioVal; simpl in mmioVal.
      exact (ev = [MMOutputEvent mmioAddr mmioVal]).
    - (* MMIO-load *)
      set (argV Fin.F1) as mmioAddr; simpl in mmioAddr.
      set (retV Fin.F1) as mmioVal; simpl in mmioVal.
      exact (ev = [MMInputEvent (argV Fin.F1) (retV Fin.F1)]).
  Defined.

  Definition kamiStep: KamiMachine -> KamiMachine -> list Event -> Prop :=
    fun km1 km2 tr =>
      exists kupd klbl,
        Step KamiProc.proc km1 kupd klbl /\
        km2 = FMap.M.union kupd km1  /\
        KamiLabelR klbl tr.

  Lemma invert_Kami_execNm:
    forall km1 kt1 kupd klbl,
      KamiProc.RegsToT km1 = Some kt1 ->
      Step KamiProc.proc km1 kupd klbl ->
      klbl.(annot) = Some (Some "execNm"%string) ->
      exists kt2,
        klbl.(calls) = FMap.M.empty _ /\
        KamiProc.RegsToT (FMap.M.union kupd km1) = Some kt2 /\
        exists curInst npc prf dst exec_val,
          curInst = (KamiProc.pgm kt1)
                      (evalExpr (rv32AlignPc _ _ type (KamiProc.pc kt1))) /\
          npc = evalExpr (rv32NextPc
                            _ _
                            (KamiProc.rf kt1) (KamiProc.pc kt1)
                            curInst) /\
          prf = KamiProc.rf kt1 /\
          dst = evalExpr (rv32GetDst _ curInst) /\
          exec_val = evalExpr
                       (rv32Exec
                          _ _
                          (KamiProc.rf kt1 (evalExpr (rv32GetSrc1 _ curInst)))
                          (KamiProc.rf kt1 (evalExpr (rv32GetSrc2 _ curInst)))
                          (KamiProc.pc kt1)
                          curInst) /\
          kt2 = {| KamiProc.pc := npc;
                   KamiProc.rf :=
                     evalExpr
                       (UpdateVector
                          (Var _ (SyntaxKind (Vector (Bit KamiProc.nwidth) rv32RfIdx)) prf)
                          (Var _ (SyntaxKind (Bit rv32RfIdx)) dst)
                          (Var _ (SyntaxKind (Bit KamiProc.nwidth)) exec_val));
                   KamiProc.pgm := KamiProc.pgm kt1;
                   KamiProc.mem := KamiProc.mem kt1 |}.
  Proof.
    intros.
    kinvert; try (repeat
                    match goal with
                    | [H: annot ?klbl = Some _ |- _] => rewrite H in *
                    | [H: (_ :: _)%struct = (_ :: _)%struct |- _] =>
                      inversion H; subst; clear H
                    end; discriminate).

    Opaque evalExpr.
    kinv_action_dest.
    unfold KamiProc.RegsToT in *.
    kregmap_red.
    destruct x1; try discriminate.
    destruct (FMap.M.find "mem"%string km1)
      as [[[kind|] memv]|]; try discriminate.
    destruct (decKind kind (Vector (Bit KamiProc.nwidth) KamiProc.nwidth));
      try discriminate.
    kregmap_red.
    inversion_clear H.
    eexists; split; [|split].
    - assumption.
    - reflexivity.
    - do 5 eexists.
      repeat (split; [reflexivity|]).
      reflexivity.
      Transparent evalExpr.
  Qed.

  Inductive PHide: Prop -> Prop :=
  | PHidden: forall P: Prop, P -> PHide P.

  Lemma simulate_bw_step:
    forall (m1 m2: KamiMachine) (t: list Event)
           (m1': RiscvMachine) (pt: list (LogItem MMIOAction)),
      fromKami_withLog m1 pt = Some m1' ->
      kamiStep m1 m2 t ->
      (* Either riscv-coq takes no steps, *)
      fromKami_withLog m2 pt = Some m1' \/
      (* or it takes a corresponding step. *)
      exists t' m2',
        traces_related t t' /\
        fromKami_withLog m2 (t' ++ pt) = Some m2' /\
        riscvStep m1' m2' t'.
  Proof.
    intros.
    destruct H0 as [kupd [klbl [? [? ?]]]]; subst.
    assert (PHide (Step KamiProc.proc m1 kupd klbl))
      by (constructor; assumption).
    kinvert.
    
    - (* [EmptyRule] step *)
      left; FMap.mred; assumption.
    - (* [EmptyMeth] step *)
      left; FMap.mred; assumption.
    - (* "pgmInit" *)
      exfalso.
      kinv_action_dest.
      kinv_red.
      unfold fromKami_withLog, KamiProc.RegsToT in H.
      kinv_regmap_red.
      discriminate.
    - (* "pgmInitEnd" *)
      exfalso.
      kinv_action_dest.
      kinv_red.
      unfold fromKami_withLog, KamiProc.RegsToT in H.
      kinv_regmap_red.
      discriminate.

    - (* "execLd" *) admit.
    - (* "execLdZ" *) admit.
    - (* "execSt" *) admit.
    - (* "execNm" *)
      inversion H4; subst; clear H4 HAction.
      inversion_clear H1.

      destruct klbl as [annot defs calls]; simpl in *; subst.
      destruct annot; [|discriminate].
      inversion H6; subst; clear H6.
      unfold fromKami_withLog in H.
      remember (KamiProc.RegsToT m1) as km1.
      apply eq_sym in Heqkm1.
      destruct km1 as [km1|]; [|discriminate].
      inversion H; subst; clear H.

      eapply invert_Kami_execNm in H3; eauto.
      destruct H3 as [km2 [? [? ?]]].
      simpl in H; subst.

      right.
      unfold fromKami_withLog.
      rewrite H0.
      inversion_clear H2.

      exists []; eexists; simpl.
      split; [|split]; [constructor|reflexivity|].
      
      econstructor.

      + (* forall post, *)
        (* KamiStep s s' -> *)
        (* RiscvStep s post -> *)
        (* post s'. *)
      


      admit.
      
    - (* "execNmZ" *) admit.

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

  (* TODO in bedrock2: differential memory in trace instead of whole memory ? *)

  Lemma kamiStep_sound: forall (m1 m2: KamiMachine) (m1': RiscvMachine) (t: list Event)
                               (post: RiscvMachine -> Prop),
      kamiStep m1 m2 t ->
      states_related (m1, nil) m1' ->
      mcomp_sat_unit (run1 iset) m1' post ->
      exists m2', states_related (m2, t) m2' /\ post m2'.
  Proof.
  Admitted.

  Lemma kamiMultiStep_sound: forall (m1 m2: KamiMachine) (m1': RiscvMachine) (t: list Event)
                               (post: RiscvMachine -> Prop),
      star kamiStep m1 m2 t ->
      states_related (m1, nil) m1' ->
      runsTo m1' post ->
      exists m2', states_related (m2, t) m2' /\ post m2'.
  Proof.
  Abort. (* doesn't hold because kami might step less or more than riscv *)

  Definition is_silence_invariant(post: RiscvMachine -> Prop): Prop :=
    forall m: RiscvMachine,
      post m ->
      mcomp_sat_unit (run1 iset) m (fun m' => post m' /\ m'.(getLog) = m.(getLog)).

  (* note: only holds if the nondet machine never picks an arbitrary value of the empty set,
     which is the case for all riscv machines, but not for a more abstract runsTo,
     and also requires no memory-changing or invalid events *)
  Lemma pick_from_runsTo: forall init post,
      runsTo init post ->
      exists final, post final. (* /\ traces_related t final.(getLog).*) (* and steps there? *)
  Admitted.

  (* Alternative approach to proving something from which impl_to_end_of_compiler would follow
     too, but without the intermediate lemmas. Can't see at the moment how this would work. *)
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
