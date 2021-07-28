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
Require Import riscv.Utility.runsToNonDet.
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
Require Import processor.Consistency.
Require Import processor.KamiRiscvStep.

Lemma get_of_list_not_In:
  forall (key: Type) (key_dec: forall k1 k2: key, {k1 = k2} + {k1 <> k2})
         (value: Type) (map: map.map key value),
    map.ok map ->
    forall (l: list (key * value)) k,
      ~ In k (List.map fst l) ->
      map.get (map.of_list l) k = None.
Proof.
  induction l as [|[k v] l]; simpl; intros;
    [rewrite map.get_empty; reflexivity|].
  destruct (key_dec k k0).
  - intuition idtac.
  - rewrite map.get_put_diff by auto.
    apply IHl; intuition idtac.
Qed.

Lemma alignedXAddrsRange_zero_bound_in:
  forall n a,
    (wordToN a < N.of_nat n)%N -> In a (alignedXAddrsRange 0 n).
Proof.
  induction n; [blia|].
  intros.
  assert (wordToN a = N.of_nat n \/ wordToN a < N.of_nat n)%N by blia.
  clear H; destruct H0.
  - unfold alignedXAddrsRange; fold alignedXAddrsRange.
    left; apply wordToN_inj.
    rewrite H.
    change (0 + n)%nat with n.
    pose proof (wordToN_bound a); rewrite H in H0.
    rewrite <-wordToN_NToWord_2 with (sz:= Z.to_nat width) (n:= N.of_nat n) by assumption.
    rewrite NToWord_nat, Nnat.Nat2N.id; reflexivity.
  - right; auto.
Qed.

Section Equiv.
  Context {Registers: map.map Z word}
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
    @KamiProc.proc instrMemSizeLg memSizeLg Hinstr kamiMemInit
                   (kami_AbsMMIO (Z.to_N memSizeLg)).

  (* redefine mcomp_sat to simplify for the case where no answer is returned *)
  Local Notation mcomp_sat_unit m initialL post :=
    (mcomp_sat m initialL (fun (_: unit) => post)).

  Context (Registers_ok: map.ok Registers)
          (mem_ok: map.ok mem).

  Local Notation states_related :=
    (@states_related Registers mem instrMemSizeLg memSizeLg Hinstr1 Hinstr2).
  Local Notation kamiStep :=
    (@kamiStep _ _ Hinstr1 Hinstr2 memInit).

  Arguments Z.add: simpl never.

  Lemma KamiLabelR_unique: forall {klbl t t'},
      KamiLabelR klbl t ->
      KamiLabelR klbl t' ->
      t = t'.
  Proof.
    intros. inversion H; inversion H0; clear H H0; subst.
    + reflexivity.
    + rewrite H4 in H1. exfalso. eapply FMap.M.add_empty_neq. eassumption.
    + rewrite H1 in H5. exfalso. eapply FMap.M.add_empty_neq. eassumption.
    + simpl in *. rewrite H1 in H5.
      apply (f_equal (FMap.M.find "mmioExec"%string)) in H5.
      do 2 rewrite FMap.M.find_add_1 in H5.
      apply Option.eq_of_eq_Some in H5.
      apply Eqdep.EqdepTheory.inj_pair2 in H5.
      inversion H5; subst; clear H5.
      reflexivity.
  Qed.

  Inductive KamiLabelSeqR: list LabelT -> list Event -> Prop :=
  | KamiSeqNil: KamiLabelSeqR nil nil
  | KamiSeqCons:
      forall klseq t,
        KamiLabelSeqR klseq t ->
        forall klbl nt,
          KamiLabelR klbl nt ->
          KamiLabelSeqR (klbl :: klseq) (nt ++ t).

  (** * Rephrasing single step soundness in a more readable way *)

  Definition KState: Type := KamiMachine * list LabelT.

  Inductive kstep1: KState -> KState -> Prop :=
  | KStep: forall (m1: KamiMachine) (t1: list LabelT) kupd klbl,
      Step kamiProc m1 kupd klbl ->
      kstep1 (m1, t1) (FMap.M.union kupd m1, klbl :: t1).

  Definition CState: Type := RiscvMachine.

  Definition cstep1(m1: CState)(P: CState -> Prop): Prop := mcomp_sat_unit (run1 iset) m1 P.

  Inductive related: KState -> CState -> Prop :=
  | Related: forall km kt eventTrace rm,
      Kami.Semantics.reachable km kamiProc ->
      states_related (km, eventTrace) rm ->
      KamiLabelSeqR kt eventTrace ->
      related (km, kt) rm.

  Theorem kstep1_sound: forall ks1 ks2 rs1 P,
      related ks1 rs1 ->
      kstep1 ks1 ks2 ->
      cstep1 rs1 P ->
      related ks2 rs1 \/
      exists rs2, related ks2 rs2 /\ P rs2.
  Proof.
    intros.
    pose proof (KamiRiscvStep.kamiStep_sound instrMemSizeLg memSizeLg Hinstr1 Hinstr2
      Hkmem1 Hkmem2 Hkmemdisj memInit Registers_ok mem_ok) as Q.
    unfold cstep1, kamiStep in *.
    inversion H. inversion H0. subst. inversion H8. subst. clear H H0 H8.
    specialize Q with (1 := H2) (3 := H3) (4 := H1).
    edestruct Q as [A | A]; clear Q.
    - eauto.
    - left. destruct A as [Q1 Q2]. econstructor.
      + unfold reachable in *.
        destruct H2 as [sigma H2]. inversion H2. subst; clear H2.
        eexists. constructor. eapply Multi; eassumption.
      + eassumption.
      + inversion H4; subst; clear H4.
        * change (KamiLabelSeqR [klbl] ([] ++ [])).
          eapply KamiSeqCons. 1: exact KamiSeqNil.
          eapply KamiSilent. assumption.
        * inversion Q1. clear Q1. subst.
          change (nt ++ t) with ([] ++ nt ++ t).
          repeat eapply KamiSeqCons; try assumption. constructor. assumption.
    - right. destruct A as [rs2 [tNew' [A [B C]]]].
      exists rs2. split. 2: exact C.
      econstructor. 2: exact B.
      + unfold reachable in *.
        destruct H2 as [sigma H2]. inversion H2. subst; clear H2.
        eexists. constructor. eapply Multi; eassumption.
      + eapply KamiSeqCons; eassumption.
  Qed.

  (** * Multistep and Behavior soundness *)

  Inductive ksteps: KState -> KState -> Prop :=
  | KSteps: forall m1 t1 m2 tNew,
      Multistep kamiProc m1 m2 tNew ->
      ksteps (m1, t1) (m2, tNew ++ t1).

  (* Can't use this one here because we're not doing a simulation from Kami to compiler *)
  Definition csteps: CState -> (CState -> Prop) -> Prop := runsTo cstep1.

  Definition calways{State: Type}(Step: State -> (State -> Prop) -> Prop)(s: State)(P: State -> Prop): Prop :=
    P s /\ forall s', P s' -> Step s' P.

  (* Can't use this one here because we don't really have a `kstep: KState -> KState -> Prop` that
     we lift with *, but Kami requires its own ksteps (its own "star") *)
  Definition kalways0{State: Type}(Step: State -> State -> Prop)(s: State)(P: State -> Prop): Prop :=
    P s /\ forall s1 s2, P s1 -> Step s1 s2 -> P s2.

  Definition kalways{State: Type}(Stepstar: State -> State -> Prop)(s: State)(P: State -> Prop): Prop :=
    forall s', Stepstar s s' -> P s'.

  Theorem ksteps_sound: forall (inv: CState -> Prop) ks1 rs1,
      related ks1 rs1 ->
      calways cstep1 rs1 inv ->
      kalways ksteps ks1 (fun ks2 => exists rs2, related ks2 rs2 /\ inv rs2).
  Proof.
    unfold calways, kalways.
    intros. destruct H0. inversion H1. subst. clear H1. revert H3 rs1 t1 H0 H.
    induction 1; intros.
    - subst. exists rs1. split; assumption.
    - specialize IHMultistep with (1 := H0) (2 := H).
      destruct IHMultistep as [rs2 [A B]].
      edestruct kstep1_sound.
      + exact A.
      + econstructor. eassumption.
      + eapply H2. exact B.
      + eauto.
      + eauto.
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
                              kamiMemInit (kami_AbsMMIO (Z.to_N memSizeLg)).
  Definition p4mm: Modules := p4mm Hinstr kamiMemInit (kami_AbsMMIO (Z.to_N memSizeLg)).

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

  Definition riscvMemInit : mem := map.of_list (List.map
    (fun i : nat =>
      (word.of_Z (Z.of_nat i),
       byte.of_Z (uwordToZ (evalConstT kamiMemInit $i))))
    (seq 0 (2 ^ Z.to_nat memSizeLg))).

  Instance kword32: coqutil.Word.Interface.word 32 := KamiWord.word 32.
  Instance kword32_ok: word.ok kword32. eapply KamiWord.ok. reflexivity. Qed.
  Lemma riscvMemInit_get_None:
    forall addr,
      (kunsigned addr <? 2 ^ memSizeLg) = false ->
      map.get riscvMemInit addr = None.
  Proof.
    intros.
    apply get_of_list_not_In; [exact (@weq (Z.to_nat width))|assumption|].

    intro Hx.
    apply in_map_iff in Hx; destruct Hx as [[addr' v] [? Hx]].
    simpl in H0; subst.
    apply in_map_iff in Hx; destruct Hx as [n [? ?]].
    inversion H0; subst; clear H0.
    apply in_seq in H1; destruct H1 as [_ ?]; simpl in H0.

    apply Nat2Z.inj_lt in H0.
    rewrite N_Z_nat_conversions.Nat2Z.inj_pow in H0.
    rewrite Z2Nat.id in H0 by blia.
    simpl in H0.

    match type of H with
    | (?x <? ?y) = false => destruct (Z.ltb_spec x y); [discriminate|clear H]
    end.
    change kunsigned with (word.unsigned (width:= width)) in H1.
    change kofZ with (word.of_Z (width:= width)) in H1.
    rewrite word.unsigned_of_Z in H1.
    cbv [word.wrap] in H1.
    rewrite Z.mod_small in H1
      by (split; [blia|];
          eapply Z.lt_le_trans; [eassumption|];
          apply Z.pow_le_mono_r; blia).
    blia.
  Qed.

  Lemma mem_related_riscvMemInit : mem_related _ (evalConstT kamiMemInit) riscvMemInit.
  Proof.
    cbv [mem_related riscvMemInit].
    intros addr.
    case (kunsigned addr <? 2 ^ memSizeLg) eqn:H.
    2: { apply riscvMemInit_get_None; assumption. }
    assert (#addr < 2 ^ Z.to_nat memSizeLg)%nat.
    { rewrite <-wordToN_to_nat.
      apply Nat2Z.inj_lt.
      rewrite N_nat_Z, N_Z_nat_conversions.Nat2Z.inj_pow.
      rewrite Z2Nat.id by blia.
      apply Z.ltb_lt; assumption.
    }
    erewrite Properties.map.get_of_list_In_NoDup; trivial.
    1: eapply NoDup_nth_error; intros i j ?.
    2: eapply (nth_error_In _ (wordToNat addr)).

    { rewrite map_map; cbn; cbv [kofZ].
      clear dependent addr.
      rewrite !map_length, seq_length in H1.
      rewrite (@map_nth_error _ _ _ _ _ i).
      2: etransitivity; [eapply nth_error_nth'|];
           rewrite ?seq_length, ?seq_nth; trivial.
      destruct (lt_dec j (2^Z.to_nat memSizeLg)).
      { rewrite (@map_nth_error _ _ _ _ _ j).
        2: etransitivity; [eapply nth_error_nth'|];
            rewrite ?seq_length, ?seq_nth; trivial.
        intros HX.
        injection HX; clear HX; intros HX.
        eapply (f_equal (@wordToZ _)) in HX.
        pose proof Z.pow_le_mono_r 2 memSizeLg 31 eq_refl ltac:(blia);
        pose proof N_Z_nat_conversions.Z2Nat.inj_pow 2 memSizeLg ltac:(blia) ltac:(blia);
        change (Z.to_nat 2) with 2%nat in *.
        rewrite 2wordToZ_ZToWord'' in HX; try split;
         change (BinInt.Z.of_nat (Pos.to_nat 32) - 1) with 31;
         blia. }
      { rewrite (proj2 (nth_error_None _ _)); try congruence.
        rewrite map_length, seq_length; blia. } }
    { replace (evalZeroExtendTrunc (BinInt.Z.to_nat memSizeLg) addr)
        with (natToWord (Z.to_nat memSizeLg) (wordToNat addr)).
      2: {
        cbv [evalZeroExtendTrunc].
        destruct (lt_dec _ _); [exfalso; apply Z2Nat.inj_lt in l; blia|].
        apply wordToNat_inj.
        rewrite wordToNat_natToWord_eqn.
        rewrite wordToNat_split1.
        cbv [eq_rec_r eq_rec]; rewrite wordToNat_eq_rect.
        reflexivity.
      }
      rewrite (@map_nth_error _ _ _ _ _ (wordToNat addr)).
      2: {
        etransitivity; [eapply nth_error_nth'|].
        all : rewrite ?seq_length, ?seq_nth; trivial.
      }
      do 2 f_equal.
      eapply word.unsigned_inj.
      rewrite word.unsigned_of_Z.
      cbv [word.wrap]; rewrite <-word.wrap_unsigned; f_equal.
      unfold word.unsigned, word, wordW, KamiWord.word, kword, kunsigned.
      rewrite wordToN_nat, nat_N_Z; reflexivity.
    }
    Unshelve. all: exact O.
  Qed.

  Lemma states_related_init:
    states_related
      (initRegs (getRegInits (proc Hinstr kamiMemInit (kami_AbsMMIO (Z.to_N memSizeLg)))), [])
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

  Lemma riscv_init_memory_undef_on_MMIO:
    map.undef_on riscvMemInit isMMIOAddr.
  Proof.
    cbv [map.undef_on map.agree_on]; intros.
    cbv [elem_of] in H.
    pose proof (mmio_mem_disjoint _ Hkmemdisj _ H); clear H.
    rewrite map.get_empty.
    apply riscvMemInit_get_None.
    destruct (Z.ltb_spec (kunsigned k) (2 ^ memSizeLg)); intuition idtac.
  Qed.

  Lemma mmio_init_xaddrs_disjoint:
    disjoint (of_list (kamiXAddrs instrMemSizeLg)) isMMIOAddr.
  Proof.
    cbv [disjoint of_list elem_of]; intros.
    pose proof (mmio_mem_disjoint _ Hkmemdisj x).
    destruct (Z.ltb_spec (kunsigned x) (2 ^ memSizeLg)).
    - right; intro Hx; auto.
    - left; intro Hx.
      apply kamiXAddrs_isXAddr1_bound in Hx.
      apply N2Z.inj_lt in Hx.
      rewrite NatLib.Z_of_N_Npow2 in Hx.
      assert (2 ^ BinInt.Z.of_nat (2 + Z.to_nat instrMemSizeLg) < 2 ^ memSizeLg)
        by (apply Z.pow_lt_mono_r; blia).
      cbv [kunsigned] in *.
      blia.
  Qed.

  Lemma riscv_to_kamiImplProcessor:
    forall (traceProp: list Event -> Prop)
           (* --- hypotheses which will be proven by the compiler --- *)
           (RvInv: RiscvMachine -> Prop)
           (establishRvInv:
              forall (m0RV: RiscvMachine),
                m0RV.(RiscvMachine.getMem) = riscvMemInit ->
                m0RV.(RiscvMachine.getPc) = word.of_Z 0 ->
                m0RV.(RiscvMachine.getNextPc) = word.of_Z 4 ->
                (forall a: word,
                    0 <= word.unsigned a < 2 ^ (2 + instrMemSizeLg) ->
                    In a m0RV.(RiscvMachine.getXAddrs)) ->
                disjoint (of_list m0RV.(RiscvMachine.getXAddrs)) isMMIOAddr ->
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
    forall (t: list LabelT) (mFinal: KamiImplMachine),
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
    edestruct ksteps_sound as (rs2 & Rel & Inv). 2: unfold calways; split.
    - econstructor.
      + eapply Kami.SemFacts.reachable_init.
      + eapply states_related_init.
      + eapply KamiSeqNil.
    - eapply establishRvInv; try reflexivity.
      all: cbv [getXAddrs getMachine]; intros.
      + apply alignedXAddrsRange_zero_bound_in.
        apply N2Z.inj_lt.
        rewrite nat_N_Z.
        cbv [instrMemSize].
        rewrite N_Z_nat_conversions.Nat2Z.inj_pow.
        rewrite Nat2Z.inj_add, Z2Nat.id by blia.
        apply H0.
      + apply mmio_init_xaddrs_disjoint.
      + apply riscvRegsInit_sound; assumption.
    - exact preserveRvInv.
    - econstructor. exact HMultistepBeh.
    - specialize (useRvInv _ Inv).
      inversion Rel. subst. clear Rel.
      simpl in useRvInv.
      destruct useRvInv as (t''' & R' & p).
      eexists. split; [|exact p].
      rewrite app_nil_r in H5.
      inversion H3. subst. clear H3.
      eapply equivalentLabelSeq_preserves_KamiLabelSeqR.
      1: eassumption.
      pose proof (traces_related_unique R' H4). subst t'''.
      assumption.
  Qed.

End Equiv.
