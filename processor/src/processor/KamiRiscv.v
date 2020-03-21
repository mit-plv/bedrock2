Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Kami.Lib.Word.
Require Import Kami.Ex.IsaRv32 riscv.Spec.Decode.
Require Import riscv.Utility.Encode.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.rdelta.
Require Import processor.KamiWord.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
Require Import riscv.Spec.Machine.
Require riscv.Platform.Memory.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Proofs.EncodeBound.
Require Import riscv.Proofs.DecodeEncode.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Monads. Import MonadNotations.
Require Import coqutil.Datatypes.PropSet.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MinimalMMIO.
Require Import riscv.Platform.MetricMinimalMMIO.
Require Import riscv.Platform.FE310ExtSpec.

Require Import Kami.Syntax Kami.Semantics Kami.Tactics.
Require Import Kami.Ex.MemTypes Kami.Ex.SC Kami.Ex.SCMMInl Kami.Ex.SCMMInv.

Require Export processor.KamiProc.
Require Import processor.FetchOk processor.DecExecOk.
Require Import processor.KamiRiscvStep.

Local Axiom TODO_joonwon: False.
Local Axiom TODO_andres: False.

Section Equiv.
  Local Hint Resolve (@KamiWord.WordsKami width width_cases): typeclass_instances.

  Context {Registers: map.map Register word}
          {mem: map.map word byte}.

  Local Notation M := (free action result).
  Local Notation RiscvMachine := MetricRiscvMachine.
  Local Existing Instance MetricMinimalMMIO.IsRiscvMachine.
  Local Existing Instance MetricMinimalMMIOSatisfiesPrimitives.

  (** * Processor, software machine, and states *)

  Variable (instrMemSizeLg memSizeLg: Z).
  Hypotheses (Hinstr1: 3 <= instrMemSizeLg)
             (Hinstr2: instrMemSizeLg <= width - 2)
             (Hkmem1: 2 + instrMemSizeLg < memSizeLg)
             (Hkmem2: memSizeLg <= width)
             (* 16 used to be disjoint to MMIO addresses.
              * [Hkmem2] is meaningless assuming this [Hkmemdisj] 
              * but still having that in context ease some proofs. *)
             (Hkmemdisj: memSizeLg <= 16).
  Local Notation Hinstr := (conj Hinstr1 Hinstr2).

  Variable (memInit: Vec (ConstT (Bit BitsPerByte)) (Z.to_nat memSizeLg)).
  Definition kamiMemInit := ConstVector memInit.
  Local Definition kamiProc :=
    @KamiProc.proc instrMemSizeLg memSizeLg Hinstr kamiMemInit kami_FE310_AbsMMIO.

  Definition iset: InstructionSet := RV32IM.

  (* redefine mcomp_sat to simplify for the case where no answer is returned *)
  Local Notation mcomp_sat_unit m initialL post :=
    (mcomp_sat m initialL (fun (_: unit) => post)).

  Context (Registers_ok: map.ok Registers)
          (mem_ok: map.ok mem).

  Local Notation states_related :=
    (@states_related Registers mem instrMemSizeLg memSizeLg Hinstr1 Hinstr2).
  Local Notation kamiStep :=
    (@kamiStep _ _ Hinstr1 Hinstr2 memInit).
  
  (** * Multistep and Behavior soundness *)
  
  Inductive KamiLabelSeqR: Kami.Semantics.LabelSeqT -> list Event -> Prop :=
  | KamiSeqNil: KamiLabelSeqR nil nil
  | KamiSeqCons:
      forall klseq t,
        KamiLabelSeqR klseq t ->
        forall klbl nt,
          KamiLabelR klbl nt ->
          KamiLabelSeqR (klbl :: klseq) (nt ++ t).

  Lemma kamiMultiStep_sound:
    forall
      (* inv could (and probably has to) be something like "runs to a safe state" *)
      (inv: RiscvMachine -> Prop)
      (* could be instantiated with compiler.ForeverSafe.runsTo_safe1_inv *)
      (inv_preserved: forall st, inv st -> mcomp_sat_unit (run1 iset) st inv)
      (m1 m2: KamiMachine) (klseq: Kami.Semantics.LabelSeqT)
      (m1': RiscvMachine) (t0: list Event)
      (Hkreach: Kami.Semantics.reachable m1 kamiProc),
      Multistep kamiProc m1 m2 klseq ->
      states_related (m1, t0) m1' ->
      inv m1' ->
      exists m2' t,
        KamiLabelSeqR klseq t /\
        states_related (m2, t ++ t0) m2' /\ inv m2'.
  Proof.
    intros ? ?.
    induction 2; intros.
    - exists m1', nil.
      repeat split.
      + constructor.
      + subst; simpl; assumption.
      + assumption.
    - specialize (IHMultistep Hkreach H0 H1).
      destruct IHMultistep as (im2' & it & ? & ? & ?).
      pose proof kamiStep_sound as P.
      assert (kamiStep n (FMap.M.union u n) l) by (eexists; split; eauto).
      assert (mcomp_sat_unit (run1 iset) im2' inv) by (eapply inv_preserved; assumption).
      pose proof (Kami.SemFacts.reachable_multistep Hkreach H).
      specialize P with (1 := Hkmem1) (2 := Hkmem2) (3 := Hkmemdisj)
                        (4 := Registers_ok) (5 := mem_ok).
      specialize P with (1 := H7) (2 := H5) (3 := H3) (4 := H6).
      destruct P as [[? ?]|].
      + exists im2', it.
        repeat split.
        * change it with ([] ++ it).
          eapply KamiSeqCons; eauto.
          constructor; assumption.
        * assumption.
        * assumption.
      + destruct H8 as (m2' & t & ? & ? & ?).
        exists m2', (t ++ it).
        rewrite <- List.app_assoc.
        repeat split; [|assumption|assumption].
        constructor; assumption.
  Qed.

  Definition KamiImplMachine: Type := RegsT.

  (* When running the processor on an FPGA, this memory module will be implemented in some
     trusted Verilog code, and will forward requests either to a DRAM or to a source
     from which the program to run can be loaded at startup.
     This source could be a connection to a host computer, an SD card, a ROM, ...
     In any case, we model this in Kami as a huge register file.
     Therefore, a faithful Verilog implementation will have to make sure that all in-range
     addresses behave like memory, including the ones from which the program is loaded.
     One possible implementation would be this:
     For each address which is designated as a "program load address", also have DRAM for it,
     as well as an extra "initialized bit", which is set to false initially.
     Whenever such an address is loaded, if the initialized bit is set, the value from the
     DRAM is returned, otherwise the value from the program source is loaded, stored into
     DRAM, and the bit is set to 1.
     Whenever such an address is stored, the initialized bit is set, and the value is stored
     into DRAM.
     For the proofs, we model this component as a huge register file where the addresses
     designated as "program load adddresses" are initialized to [prog], and the other
     addresses are initialized to zero.
     We'll use the convention that "program load addresses" are from 0 to 4*2^instrMemSizeLg,
     and that the data memory goes from 4*2^instrMemSizeLg to dataMemSize
     because then we don't have to pass the base program load address to this definition,
     and to serve load/store requests in the Kami model, we can just ignore the upper bits
     and use the lower bits to index into the Vector.
   *)

  Definition mm: Modules := Kami.Ex.SC.mm
                              (existT _ rv32DataBytes eq_refl)
                              kamiMemInit kami_FE310_AbsMMIO.
  Definition p4mm: Modules := p4mm Hinstr kamiMemInit kami_FE310_AbsMMIO.

  Fixpoint setRegsInit (kinits: kword 5 -> kword width) (n: nat): Registers :=
    match n with
    | O => map.put map.empty 0 $0
    | S n' => map.put (setRegsInit kinits n') (Z.of_nat n) (kinits $n)
    end.
  
  Definition riscvRegsInit: Registers :=
    setRegsInit (evalConstT (rfInit procInit)) 31.
  Lemma regs_related_riscvRegsInit:
    regs_related (evalConstT (rfInit procInit)) riscvRegsInit.
  Proof.
    red; intros.

    clear -Registers_ok.
    pose proof (wordToN_bound w).
    change (NatLib.Npow2 (BinInt.Z.to_nat 5)) with 32%N in H.
    assert (wordToN w = 0 \/ wordToN w = 1 \/ wordToN w = 2 \/ wordToN w = 3 \/
            wordToN w = 4 \/ wordToN w = 5 \/ wordToN w = 6 \/ wordToN w = 7 \/
            wordToN w = 8 \/ wordToN w = 9 \/ wordToN w = 10 \/ wordToN w = 11 \/
            wordToN w = 12 \/ wordToN w = 13 \/ wordToN w = 14 \/ wordToN w = 15 \/
            wordToN w = 16 \/ wordToN w = 17 \/ wordToN w = 18 \/ wordToN w = 19 \/
            wordToN w = 20 \/ wordToN w = 21 \/ wordToN w = 22 \/ wordToN w = 23 \/
            wordToN w = 24 \/ wordToN w = 25 \/ wordToN w = 26 \/ wordToN w = 27 \/
            wordToN w = 28 \/ wordToN w = 29 \/ wordToN w = 30 \/ wordToN w = 31)%N
      by abstract blia.
    clear H.
    repeat match goal with
           | H: _ \/ _ |- _ => destruct H
           end.

    all: match goal with
         | H: wordToN _ = ?n |- _ =>
           change n with (wordToN (sz:= 5) $(N.to_nat n)) in H;
             apply wordToN_inj in H; subst; simpl
         end.
    all: cbv [riscvRegsInit setRegsInit].
    all: repeat rewrite map.get_put_diff by discriminate.
    all: rewrite map.get_put_same.
    all: reflexivity.
  Qed.

  Lemma riscvRegsInit_sound:
    forall reg, 0 < reg < 32 -> map.get riscvRegsInit reg <> None.
  Proof.
    intros.
    assert (reg = 1 \/ reg = 2 \/ reg = 3 \/
            reg = 4 \/ reg = 5 \/ reg = 6 \/ reg = 7 \/
            reg = 8 \/ reg = 9 \/ reg = 10 \/ reg = 11 \/
            reg = 12 \/ reg = 13 \/ reg = 14 \/ reg = 15 \/
            reg = 16 \/ reg = 17 \/ reg = 18 \/ reg = 19 \/
            reg = 20 \/ reg = 21 \/ reg = 22 \/ reg = 23 \/
            reg = 24 \/ reg = 25 \/ reg = 26 \/ reg = 27 \/
            reg = 28 \/ reg = 29 \/ reg = 30 \/ reg = 31)
      by abstract blia.
    clear H.
    repeat match goal with
           | H: _ \/ _ |- _ => destruct H
           end.

    all: subst.
    all: cbv [riscvRegsInit setRegsInit].
    all: repeat rewrite map.get_put_diff by discriminate.
    all: rewrite map.get_put_same.
    all: discriminate.
  Qed.

  Definition riscvMemInit := map.of_list (List.map
    (fun i : nat =>
      (word.of_Z (Z.of_nat i),
       byte.of_Z (uwordToZ (evalConstT kamiMemInit $i))))
    (seq 0 (2 ^ Z.to_nat memSizeLg))).
  Lemma mem_related_riscvMemInit : mem_related _ (evalConstT kamiMemInit) riscvMemInit.
  Proof.
    cbv [mem_related riscvMemInit].
    intros addr.
    case (kunsigned addr <? 2 ^ memSizeLg) eqn:?H.
    2: { case TODO_joonwon. }
    erewrite Properties.map.get_of_list_In_NoDup; trivial.
    1: eapply NoDup_nth_error; intros i j ?.
    2: eapply (nth_error_In _ (wordToNat addr)).

    { rewrite map_map; cbn; cbv [kofZ].
      (* erewrite 2map_nth_error. *)
      case TODO_andres. }
    { (* erewrite map_nth_error. *)
      case TODO_andres. }
  Qed.

  Lemma states_related_init:
    states_related
      (initRegs (getRegInits (proc Hinstr kamiMemInit kami_FE310_AbsMMIO)), [])
      {| getMachine :=
           {| RiscvMachine.getRegs := riscvRegsInit;
              RiscvMachine.getPc := word.of_Z 0;
              RiscvMachine.getNextPc := word.of_Z 4;
              RiscvMachine.getMem := riscvMemInit;
              RiscvMachine.getXAddrs := kamiXAddrs instrMemSizeLg;
              RiscvMachine.getLog := nil; (* <-- intended to be nil *) |};
         getMetrics := MetricLogging.EmptyMetricLog; |}.
  Proof.
    econstructor; try reflexivity.
    - econstructor.
    - eapply pRegsToT_init.
    - intros; discriminate.
    - split; reflexivity.
    - apply regs_related_riscvRegsInit.
    - apply mem_related_riscvMemInit.
  Qed.

  Lemma equivalentLabel_preserves_KamiLabelR:
    forall l1 l2,
      equivalentLabel (liftToMap1 (@idElementwise _)) l1 l2 ->
      forall l,
        KamiLabelR l2 l -> KamiLabelR l1 l.
  Proof.
    intros.
    destruct l1 as [ann1 ds1 cs1], l2 as [ann2 ds2 cs2].
    destruct H as [? [? ?]]; simpl in *.
    rewrite SemFacts.liftToMap1_idElementwise_id in H, H1; subst.
    inversion_clear H0; subst.
    - apply KamiSilent; assumption.
    - eapply KamiMMIO; eauto.
  Qed.

  Lemma equivalentLabelSeq_preserves_KamiLabelSeqR:
    forall t1 t2,
      equivalentLabelSeq (liftToMap1 (@idElementwise _)) t1 t2 ->
      forall t,
        KamiLabelSeqR t2 t ->
        KamiLabelSeqR t1 t.
  Proof.
    induction 1; intros; [assumption|].
    inversion_clear H1.
    constructor; auto.
    eapply equivalentLabel_preserves_KamiLabelR; eauto.
  Qed.

  Lemma riscv_to_kamiImplProcessor:
    forall (traceProp: list Event -> Prop)
           (* --- hypotheses which will be proven by the compiler --- *)
           (RvInv: RiscvMachine -> Prop)
           (establishRvInv:
              forall (m0RV: RiscvMachine),
                m0RV.(getMem) = riscvMemInit ->
                m0RV.(getPc) = word.of_Z 0 ->
                (forall reg, 0 < reg < 32 -> map.get m0RV.(getRegs) reg <> None) ->
                m0RV.(getLog) = nil ->
                RvInv m0RV)
           (preserveRvInv:
              forall (m: RiscvMachine), RvInv m -> mcomp_sat_unit (run1 iset) m RvInv)
           (useRvInv:
              forall (m: RiscvMachine),
                RvInv m -> exists t, traces_related t m.(getLog) /\
                                     traceProp t),
    (* --- final end to end theorem will start here --- *)
    forall (t: LabelSeqT) (mFinal: KamiImplMachine),
      Behavior p4mm mFinal t ->
      (* --- conclusion ---
         The trace produced by the kami implementation can be mapped to an MMIO trace
         (this guarantees that the only external behavior of the kami implementation is MMIO)
         and moreover, this MMIO trace satisfies some desirable property. *)
      exists (t': list Event), KamiLabelSeqR t t' /\ traceProp t'.
  Proof.
    intros.
    pose proof (@proc_correct instrMemSizeLg memSizeLg Hinstr kamiMemInit) as P.
    unfold traceRefines in P.
    specialize P with (1 := H).
    destruct P as (mFinal' & t' & B & E).
    inversion_clear B.
    pose proof kamiMultiStep_sound as P.
    specialize P with (1 := preserveRvInv).
    unfold kamiProc in P.

    specialize P with (1 := Kami.SemFacts.reachable_init _).
    specialize P with (1 := HMultistepBeh).
    specialize P with (t0 := nil).
    specialize (P _ states_related_init).
    destruct P as (mF & t'' & R & Rel & Inv).
    - eapply establishRvInv.
      + reflexivity.
      + reflexivity.
      + apply riscvRegsInit_sound.
      + reflexivity.
    - specialize (useRvInv _ Inv).
      inversion Rel. subst. clear Rel.
      simpl in useRvInv.
      destruct useRvInv as (t''' & R' & p).
      eexists. split; [|exact p].
      eapply equivalentLabelSeq_preserves_KamiLabelSeqR.
      1: eassumption.
      pose proof (traces_related_unique R' H2). subst t'''.
      rewrite app_nil_r.
      assumption.
  Qed.

End Equiv.
