Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Kami.Lib.Word.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
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
Require Import Kami.Ex.IsaRv32.

Require Export processor.KamiProc.
Require Import processor.FetchOk processor.DecExecOk.

Local Open Scope Z_scope.

Lemma Npow2_le:
  forall n m,
    (n <= m)%nat -> (NatLib.Npow2 n <= NatLib.Npow2 m)%N.
Proof.
  induction m; simpl; intros.
  - assert (n = 0)%nat by blia.
    subst; simpl; blia.
  - assert (n = S m \/ n <= m)%nat by blia.
    destruct H0.
    + subst; reflexivity.
    + specialize (IHm H0).
      destruct (NatLib.Npow2 m); blia.
Qed.

Lemma bitSlice_range_ex:
  forall z n m,
    0 <= n <= m ->
    0 <= bitSlice z n m < 2 ^ (m - n).
Proof.
  intros.
  rewrite bitSlice_alt by blia.
  unfold bitSlice'.
  apply Z.mod_pos_bound.
  apply Z.pow_pos_nonneg; blia.
Qed.

Axiom TODO_joonwon: False.

Section Equiv.
  Local Hint Resolve (@KamiWord.WordsKami width width_cases): typeclass_instances.

  (* TODO not sure if we want to use ` or rather a parameter record *)
  Context {Registers: map.map Register word}
          {mem: map.map word byte}.

  Local Notation M := (free action result).
  Local Notation RiscvMachine := MetricRiscvMachine.
  Local Existing Instance MetricMinimalMMIO.IsRiscvMachine.
  Local Existing Instance MetricMinimalMMIOSatisfiesPrimitives.

  (** * Processor, software machine, and states *)

  Variable (instrMemSizeLg: Z).
  Hypotheses (Hinstr1: 3 <= instrMemSizeLg)
             (Hinstr2: instrMemSizeLg <= width - 2).
  Local Notation Hinstr := (conj Hinstr1 Hinstr2).

  Variable (memInit: Vec (ConstT (Bit BitsPerByte)) (Z.to_nat width)).
  Definition kamiMemInit := ConstVector memInit.
  Local Definition kamiProc :=
    @KamiProc.proc instrMemSizeLg Hinstr kamiMemInit kami_FE310_AbsMMIO.
  Local Definition kamiStMk := @KamiProc.mk (Z.to_nat width)
                                            (Z.to_nat instrMemSizeLg)
                                            rv32InstBytes rv32DataBytes rv32RfIdx.
  Local Notation kamiXAddrs := (kamiXAddrs instrMemSizeLg).
  Local Notation rv32Fetch :=
    (rv32Fetch (Z.to_nat width)
               (Z.to_nat instrMemSizeLg)
               (width_inst_valid Hinstr)).

  Definition iset: InstructionSet := RV32IM.

  (** * The Observable Behavior: MMIO events *)

  Definition signedByteTupleToReg{n: nat}(v: HList.tuple byte n): word :=
    word.of_Z (BitOps.signExtend (8 * Z.of_nat n) (LittleEndian.combine n v)).

  Definition mmioLoadEvent(m: mem)(addr: word)(n: nat)(v: HList.tuple byte n): LogItem :=
    ((m, "MMIOREAD"%string, [addr]), (m, [signedByteTupleToReg v])).

  Definition mmioStoreEvent(m: mem)(addr: word)(n: nat)(v: HList.tuple byte n): LogItem :=
    ((m, "MMIOWRITE"%string, [addr; signedByteTupleToReg v]), (m, [])).

  (* common event between riscv-coq and Kami *)
  Inductive Event: Type :=
  | MMInputEvent(addr v: word)
  | MMOutputEvent(addr v: word).

  (* note: given-away and received memory has to be empty *)
  Inductive events_related: Event -> LogItem -> Prop :=
  | relate_MMInput: forall addr v,
      events_related (MMInputEvent addr v) ((map.empty, "MMIOREAD"%string, [addr]), (map.empty, [v]))
  | relate_MMOutput: forall addr v,
      events_related (MMOutputEvent addr v) ((map.empty, "MMIOWRITE"%string, [addr; v]), (map.empty, [])).

  Inductive traces_related: list Event -> list LogItem -> Prop :=
  | relate_nil:
      traces_related nil nil
  | relate_cons: forall e e' t t',
      events_related e e' ->
      traces_related t t' ->
      traces_related (e :: t) (e' :: t').

  Definition pc_related_when_valid (xaddrs: XAddrs)
             (kpc : Word.word (2 + Z.to_nat instrMemSizeLg))
             (rpc : kword width) :=
    AddrAligned rpc /\
    (isXAddr4 rpc xaddrs -> pc_related _ kpc rpc).

  Inductive states_related: KamiMachine * list Event -> RiscvMachine -> Prop :=
  | relate_states:
      forall t t' m riscvXAddrs kpc krf rrf rpc nrpc pinit instrMem kdataMem rdataMem metrics,
        traces_related t t' ->
        KamiProc.RegsToT m = Some (kamiStMk kpc krf pinit instrMem kdataMem) ->
        (pinit = false -> riscvXAddrs = kamiXAddrs) ->
        (pinit = true -> RiscvXAddrsSafe instrMemSizeLg (* Hinstr *) instrMem kdataMem riscvXAddrs) ->
        pc_related_when_valid riscvXAddrs kpc rpc ->
        nrpc = word.add rpc (word.of_Z 4) ->
        regs_related krf rrf ->

        mem_related kdataMem rdataMem ->
        states_related
          (m, t) {| getMachine := {| RiscvMachine.getRegs := rrf;
                                     RiscvMachine.getPc := rpc;
                                     RiscvMachine.getNextPc := nrpc;
                                     RiscvMachine.getMem := rdataMem;
                                     RiscvMachine.getXAddrs := riscvXAddrs;
                                     RiscvMachine.getLog := t'; |};
                    getMetrics := metrics; |}.

  (* redefine mcomp_sat to simplify for the case where no answer is returned *)
  Local Notation mcomp_sat_unit m initialL post :=
    (mcomp_sat m initialL (fun (_: unit) => post)).

  Lemma events_related_unique: forall e' e1 e2,
      events_related e1 e' ->
      events_related e2 e' ->
      e1 = e2.
  Proof.
    intros. inversion H; inversion H0; subst; congruence.
  Qed.

  Lemma traces_related_unique: forall {t' t1 t2},
      traces_related t1 t' ->
      traces_related t2 t' ->
      t1 = t2.
  Proof.
    induction t'; intros.
    - inversion H. inversion H0. reflexivity.
    - inversion H. inversion H0. subst. f_equal.
      + eapply events_related_unique; eassumption.
      + eapply IHt'; eassumption.
  Qed.

  Inductive KamiLabelR: Kami.Semantics.LabelT -> list Event -> Prop :=
  | KamiSilent:
      forall klbl,
        klbl.(calls) = FMap.M.empty _ ->
        KamiLabelR klbl nil
  | KamiMMIO:
      forall klbl argV retV e,
        klbl.(calls) =
        FMap.M.add
          "mmioExec"%string
          (existT SignT {| arg := Struct (RqFromProc (Z.to_nat width) rv32DataBytes);
                           ret := Struct (RsToProc rv32DataBytes) |} (argV, retV))
          (FMap.M.empty _) ->
        e = (if argV (Fin.FS Fin.F1)
             then MMOutputEvent (argV Fin.F1) (argV (Fin.FS (Fin.FS Fin.F1)))
             else MMInputEvent (argV Fin.F1) (retV Fin.F1)) ->
        KamiLabelR klbl [e].

  Definition kamiStep (m1 : KamiMachine) (m2 : KamiMachine) (klbl : Kami.Semantics.LabelT) : Prop :=
    exists kupd, Step kamiProc m1 kupd klbl /\ m2 = FMap.M.union kupd m1.

  Ltac kami_step_case_empty :=
    left; FMap.mred; fail.

  Ltac eval_decode_in H :=
    cbv beta iota delta [decode] in H;
    repeat
      match goal with
      | [Hbs: bitSlice _ _ _ = _ |- _] => rewrite !Hbs in H; clear Hbs
      end;
    cbv [iset supportsM supportsA supportsF
              andb Z.eqb Pos.eqb
              opcode_LOAD opcode_OP opcode_SYSTEM opcode_MISC_MEM opcode_OP_IMM
              opcode_LUI opcode_AUIPC opcode_STORE opcode_BRANCH opcode_JALR
              opcode_JAL
              funct3_LW funct3_LH funct3_LB funct3_LBU funct3_LHU
              funct3_ADD
              funct3_MUL funct3_MULH funct3_MULHSU funct3_MULHU
              funct3_DIV funct3_DIVU funct3_REM funct3_REMU
              funct7_ADD funct7_MUL
              isValidI isValidM
              bitwidth isValidCSR
        ] in H;
    repeat rewrite app_nil_r in H.

  Inductive PHide: Prop -> Prop :=
  | PHidden: forall P: Prop, P -> PHide P.

  Lemma pgm_init_not_mmio:
    Kami.Ex.SCMMInv.PgmInitNotMMIO rv32Fetch kami_FE310_AbsMMIO.
  Proof.
    red; intros.
    cbv [isMMIO kami_FE310_AbsMMIO].
    unfold evalExpr; fold evalExpr.
    cbv [evalBinBool evalUniBool evalBinBitBool].
    apply Bool.andb_false_intro2.
    repeat apply Bool.orb_false_intro.
    all: case TODO_joonwon.
  Qed.

  Lemma kamiStep_sound_case_pgmInit:
    forall km1 t0 rm1 post kupd cs
           (Hkinv: scmm_inv rv32RfIdx rv32Fetch km1),
      states_related (km1, t0) rm1 ->
      mcomp_sat_unit (run1 iset) rm1 post ->
      Step kamiProc km1 kupd
           {| annot := Some (Some "pgmInit"%string);
              defs := FMap.M.empty _;
              calls := cs |} ->
      states_related (FMap.M.union kupd km1, t0) rm1 /\
      cs = FMap.M.empty _.
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply invert_Kami_pgmInit in H1; eauto;
      [|apply pgm_init_not_mmio].
    unfold kamiStMk in H1; simpl in H1.
    destruct H1 as (? & ? & km2 & ? & ? & ? & ? & ?); subst.
    clear H7.
    destruct km2 as [pc2 rf2 pinit2 pgm2 mem2]; simpl in *; subst.
    split; [|reflexivity].
    econstructor; eauto.
    intros; discriminate.
  Qed.

  Lemma kamiPgmInitFull_RiscvXAddrsSafe:
    forall pgmFull dataMem,
      KamiPgmInitFull rv32Fetch pgmFull dataMem ->
      RiscvXAddrsSafe instrMemSizeLg pgmFull dataMem kamiXAddrs.
  Proof.
    unfold KamiPgmInitFull; intros.
    red; intros.
    split; [assumption|].
    intros.
    rewrite H.
    cbv [alignInst rv32Fetch rv32AlignInst]; unfold evalExpr; fold evalExpr.
    f_equal.
    apply eq_sym, rv32AlignAddr_consistent; auto.
  Qed.

  Lemma kamiStep_sound_case_pgmInitEnd:
    forall km1 t0 rm1 post kupd cs
           (Hkinv: scmm_inv rv32RfIdx rv32Fetch km1),
      states_related (km1, t0) rm1 ->
      mcomp_sat_unit (run1 iset) rm1 post ->
      Step kamiProc km1 kupd
           {| annot := Some (Some "pgmInitEnd"%string);
              defs := FMap.M.empty _;
              calls := cs |} ->
      states_related (FMap.M.union kupd km1, t0) rm1 /\
      cs = FMap.M.empty _.
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply invert_Kami_pgmInitEnd in H1; eauto;
      [|apply pgm_init_not_mmio].
    unfold kamiStMk in H1; simpl in H1.
    destruct H1 as (? & ? & pgmFull & ? & ?); subst.
    clear H7.
    specialize (H6 eq_refl); subst.
    split; [|reflexivity].
    econstructor; eauto.
    intros _.
    apply kamiPgmInitFull_RiscvXAddrsSafe; auto.
  Qed.

  Ltac mcomp_step_in HR :=
    progress (
    let ucode := match type of HR with mcomp_sat ?u ?s ?p => u end in
    let state := match type of HR with mcomp_sat ?u ?s ?p => s end in
    let post := match type of HR with mcomp_sat ?u ?s ?p => p end in
    (let uc := fresh "uc" in set ucode as uc in HR; hnf in uc; subst uc);
    let ucode := match type of HR with mcomp_sat ?u ?s ?p => u end in
    change (mcomp_sat ucode state post) in HR;
    match ucode with
    | free.act ?a ?k =>
      let pf := constr:(HR : free.interp interp_action ucode state post) in
      (let HRR := fresh in pose proof pf as HRR; clear HR; rename HRR into HR);
      remember k as kV;
      (*
      Note:
      conversion is slow if we don't remember k.
      this might be because interp_fix needs to be unfolded once,
      but unfolding it as many times as possible would create a huge term
      *)
      let interp_action := eval cbv delta [interp_action MinimalMMIO.interp_action] in interp_action in
      let TR := eval cbn iota beta delta [
        fst snd
        getMetrics getMachine
        translate
        getRegs getPc getNextPc getMem getXAddrs getLog
        ]
      in (interp_action a state (fun x state' => mcomp_sat (kV x) state' post)) in
      change TR in HR;
      subst kV
    | free.ret ?v => change (post v state) in HR
    | _ => idtac
    end).

  Ltac destruct_if_by_contradiction :=
    let c := match goal with
    | H : context [if ?c then _ else _] |- _ => c
    | H := context [if ?c then _ else _] |- _ => c
    | |- if ?c then _ else _ => c
    end in
    destruct c; try (exfalso; contradiction); [].

  (* kitchen sink goal simplification? *)
  Ltac t  :=
    match goal with
    | H: let x := ?v in @?C x |- _ =>
        let x := fresh x in pose v as x;
        let C := eval cbv beta in (C x) in
        change C in H
    | H: mcomp_sat _ _ _ |- _ => mcomp_step_in H
    | H: exists _, _ |- _ => destruct H
    | H: _ /\ _ |- _ => destruct H
    | _ => destruct_if_by_contradiction
    | H: _ |- _ => progress
                     cbv beta delta [load store] in H;
                   cbn beta iota delta [
                         load store
                              fst snd
                              translate
     withMetrics
     updateMetrics
     getMachine
     getMetrics
     getRegs
     getPc
     getNextPc
     getMem
     getXAddrs
     getLog
     withRegs
     withPc
     withNextPc
     withMem
     withXAddrs
     withLog
     withLogItem
     withLogItems
     RiscvMachine.withRegs
     RiscvMachine.withPc
     RiscvMachine.withNextPc
     RiscvMachine.withMem
     RiscvMachine.withXAddrs
     RiscvMachine.withLog
     RiscvMachine.withLogItem
     RiscvMachine.withLogItems

                       ] in H
    | H: context CTX [@Memory.load_bytes ?a ?b ?c ?d ?e ?f ?g],
         G: context     [@Memory.load_bytes ?A ?B ?C ?D ?E ?F ?G]
      |- _ =>
      let HH := context CTX [@Memory.load_bytes A B C D E F G] in
      progress change HH in H
    end.

  Ltac prove_KamiLabelR :=
    split; [|split];
        [eapply KamiSilent; reflexivity
    |
    |eassumption].

  Context (Registers_ok : map.ok Registers).

  Ltac prove_states_related :=
    econstructor;
    [ solve [trivial]
    | clear; cbv [RegsToT pRegsToT]; kregmap_red; exact eq_refl
    | clear; intro; discriminate
    | solve [trivial]
    | cbv [RiscvMachine.getNextPc]; split;
    [ apply AddrAligned_plus4; assumption
    | (* intros; eapply pc_related_plus4. *) case TODO_joonwon ]
    | solve [trivial]
    | eapply regs_related_put;
        [ solve [trivial] | solve [trivial] | | ];
            erewrite ?regs_related_get,
            ?unsigned_split2_split1_as_bitSlice
            by eauto;
            trivial
    | solve [trivial]
        ].

  Lemma in_kamiXAddrs_aligned_plus4_bound:
    forall pc,
      isXAddr4 (word.add pc (word.of_Z 4)) kamiXAddrs ->
      (wordToN pc + 4 < NatLib.Npow2 (2 + Z.to_nat instrMemSizeLg))%N.
  Proof.
    case TODO_joonwon.
  Qed.

  Lemma pc_related_plus4:
    forall xaddrs,
      (forall a, isXAddr4 a xaddrs -> isXAddr4 a kamiXAddrs) ->
      forall kpc rpc,
        isXAddr4 rpc xaddrs ->
        pc_related_when_valid xaddrs kpc rpc ->
        pc_related_when_valid
          xaddrs (kpc ^+ ZToWord (S (S (BinInt.Z.to_nat instrMemSizeLg))) 4)
          (word.add rpc (word.of_Z 4)).
  Proof.
    cbv [pc_related_when_valid]; intros.
    destruct H1.
    split; [apply AddrAligned_plus4; assumption|].
    intros.
    specialize (H2 H0).
    apply H in H0.
    red in H2; red.
    cbv [word.add word WordsKami wordW KamiWord.word wplus].
    cbv [wordBin].

    match goal with |- context [(_ + ?t)%N] => replace t with 4%N end.
    2: {
      apply N2Z.inj.
      rewrite unsigned_wordToZ.
      apply eq_sym, Z.mod_small.
      do 2 rewrite Nat2Z.inj_succ.
      split; [blia|].
      simpl; rewrite Z2Nat.id by blia.
      do 2 (rewrite Z.pow_succ_r by blia).
      assert (1 < 2 ^ instrMemSizeLg) by (apply Z.pow_gt_1; blia).
      blia.
    }
    
    rewrite wordToN_NToWord_2
      by (rewrite H2; eapply in_kamiXAddrs_aligned_plus4_bound; eauto).
    rewrite wordToN_NToWord_2.
    2: {
      eapply N.lt_le_trans.
      { eapply in_kamiXAddrs_aligned_plus4_bound; eauto. }
      { apply Npow2_le.
        change 2%nat with (Z.to_nat 2).
        rewrite <-Z2Nat.inj_add by blia.
        apply Z2Nat.inj_le; blia.
      }
    }
    rewrite H2; reflexivity.
  Qed.

  Lemma kamiStep_sound_case_execLd:
    forall km1 t0 rm1 post kupd cs
           (Hkinv: scmm_inv rv32RfIdx rv32Fetch km1),
      states_related (km1, t0) rm1 ->
      mcomp_sat_unit (run1 iset) rm1 post ->
      Step kamiProc km1 kupd
           {| annot := Some (Some "execLd"%string);
              defs := FMap.M.empty _;
              calls := cs |} ->
      exists rm2 t,
        KamiLabelR
          {| annot := Some (Some "execLd"%string);
             defs := FMap.M.empty _;
             calls := cs |} t /\
        states_related (FMap.M.union kupd km1, t ++ t0) rm2 /\ post rm2.
  Proof.
    intros.
    inversion H; subst; clear H.
    eapply invert_Kami_execLd in H1; eauto.
    destruct H1 as (? & kinst & ldAddr & ? & ? & ? & ? & ? & ?).
    change (rv32InstBytes * BitsPerByte)%nat with (Z.to_nat width) in kinst.
    simpl in H; subst pinit.

    destruct (evalExpr (isMMIO type ldAddr)) eqn:Hmmio.
    - (** MMIO load case *)
      repeat match goal with
             | [H: true = true -> _ |- _] => specialize (H eq_refl)
             | [H: true = false -> _ |- _] => clear H
             end.
      destruct H11 as (kt2 & mmioLdRq & mmioLdRs & ? & ? & ? & ? & ?).
      simpl in H; subst cs.

      (* Invert a riscv-coq step *)
      (* -- fetch *)
      repeat t.
      specialize (H eq_refl).
      destruct H8; specialize (H15 H).
      eapply fetch_ok in H; [|eassumption..].
      destruct H as (rinst & ? & ?).
      rewrite H in H0.
      setoid_rewrite <-H1 in H16.
      repeat t.
      setoid_rewrite H16 in H0.

      (* -- decode *)
      assert (bitSlice (kunsigned kinst) 0 7 = opcode_LOAD) as Hkopc.
      { unfold getOptype, rv32Dec, rv32GetOptype in H2.
        unfold evalExpr in H2; fold evalExpr in H2.
        destruct (isEq _ _ _) in H2;
          [|destruct (isEq _ _ _) in H2; discriminate].
        revert e; intros e.
        cbn [evalExpr getOpcodeE evalUniBit] in e.
        apply (f_equal (fun x => Z.of_N (wordToN x))) in e.
        rewrite unsigned_split1_as_bitSlice in e.
        assumption.
      }

      pose proof (bitSlice_range_ex
                    (kunsigned kinst) 12 15 ltac:(abstract blia))
        as Hf3.
      change (2 ^ (15 - 12)) with 8 in Hf3.
      assert (let z := bitSlice (kunsigned kinst) 12 15 in
              z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/
              z = 4 \/ z = 5 \/ z = 6 \/ z = 7) by (abstract blia).
      clear Hf3.
      destruct H17 as [|[|[|[|[|[|[|]]]]]]].
      (* -- get rid of [InvalidInstruction] cases *)
      4, 7, 8: eval_decode_in H0; exfalso; auto; fail.

      + (** LB: load-byte *)
        eval_decode_in H0.
        repeat t.
        case TODO_joonwon.

      + (** LH: load-half *) case TODO_joonwon.
      + (** LW: load-word *) case TODO_joonwon.
      + (** LHU: load-half-unsigned *) case TODO_joonwon.
      + (** LBU: load-byte-unsigned *) case TODO_joonwon.

    - case TODO_joonwon.

  Qed.

  Axiom TODO_kamiStep_instruction : False.

  Ltac kinvert_pre :=
    repeat
      match goal with
      | [H: PHide (Step _ _ _ _) |- _] => inversion H; subst; clear H
      | [H: SemAction _ _ _ _ _ |- _] => clear H
      | [H: (_ :: _)%struct = (_ :: _)%struct |- _] => inversion H; subst; clear H
      | [H: context [annot ?klbl] |- _] =>
        let annot := fresh "annot" in
        let defs := fresh "defs" in
        let calls := fresh "calls" in
        destruct klbl as [annot defs calls];
        cbn [Semantics.annot Semantics.defs Semantics.calls] in *; subst;
        destruct annot; [|discriminate]
      | [H: Rle _ = Rle _ |- _] => inversion H; subst; clear H
      end.
  
  Ltac kinvert_more :=
    kinvert;
    try (repeat
           match goal with
           | [H: Semantics.annot ?klbl = Some _ |- _] => rewrite H in *
           | [H: (_ :: _)%struct = (_ :: _)%struct |- _] =>
             inversion H; subst; clear H
           end; discriminate).

  Ltac invertActionRep_nosimpl :=
    repeat
      match goal with
      | H:(_ :: _)%struct = (_ :: _)%struct |- _ => CommonTactics.inv H
      | H:SemAction _ _ _ _ _ |- _ =>
        apply inversionSemAction in H; CommonTactics.dest(* ; try subst *)
      | H:if ?c then SemAction _ _ _ _ _ /\ _ /\ _ /\ _ else SemAction _ _ _ _ _ /\ _ /\ _ /\ _
        |- _ =>
        repeat autounfold with MethDefs;
        match goal with
        | H:if ?c
            then SemAction _ _ _ _ _ /\ _ /\ _ /\ _
            else SemAction _ _ _ _ _ /\ _ /\ _ /\ _
          |- _ =>
          let ic := fresh "ic" in
          remember c as ic; destruct ic; CommonTactics.dest; subst
        end
      end.

  Ltac kinv_action_dest_nosimpl :=
    kinv_red; invertActionRep_nosimpl.

  Ltac block_subst vn :=
    match goal with
    | [H: vn = ?v |- _] =>
      assert (PHide (vn = v)) by (constructor; assumption); clear H
    end.

  Ltac red_regmap :=
    try match goal with
        | [H: scmm_inv _ _ _ |- _] => inversion H
        end;
    cbv [RegsToT pRegsToT] in *;
    kregmap_red; kinv_red.

  Ltac red_trivial_conds :=
    repeat
      match goal with
      | [H: evalExpr (Var type (SyntaxKind Bool) ?b) = _ |- _] => simpl in H; subst b
      end.

  Ltac cleanup_trivial :=
    cbv [Semantics.annot Semantics.defs Semantics.calls] in *;
    repeat
      match goal with
      | [H: FMap.M.empty _ = FMap.M.empty _ |- _] => clear H
      | [H: true = false -> _ |- _] => clear H
      | [H: false = true -> _ |- _] => clear H
      | [H: Some _ = Some _ |- _] => inversion H; subst; clear H
      | [H: {| pc := _ |} = kamiStMk _ _ _ _ _ |- _] => inversion H; subst; clear H
      | [H: true = true -> _ |- _] => specialize (H eq_refl)
      end.

  Ltac unblock_subst vn :=
    match goal with
    | [H: PHide (vn = _) |- _] => inversion_clear H
    end.

  Lemma kamiStep_sound:
    forall (m1 m2: KamiMachine) (klbl: Kami.Semantics.LabelT)
           (m1': RiscvMachine) (t0: list Event) (post: RiscvMachine -> Prop)
           (Hkreach: Kami.Semantics.reachable m1 kamiProc),
      kamiStep m1 m2 klbl ->
      states_related (m1, t0) m1' ->
      mcomp_sat_unit (run1 iset) m1' post ->
      (* Three cases for each Kami step:
       * 1) riscv-coq does not proceed or
       * 2) both Kami and riscv-coq proceed, preserving [states_related]. *)
      (states_related (m2, t0) m1' /\ klbl.(calls) = FMap.M.empty _) \/
      exists m2' t,
        KamiLabelR klbl t /\ states_related (m2, t ++ t0) m2' /\ post m2'.
  Proof.
    intros.
    destruct H as [kupd [? ?]]; subst.
    assert (PHide (Step kamiProc m1 kupd klbl)) by (constructor; assumption).
    apply scmm_inv_ok in Hkreach; [|reflexivity|apply pgm_init_not_mmio].

    (* Since the processor is inlined thus there are no defined methods,
     * the step cases generated by [kinvert] are by rules.
     *)
    kinvert.

    - kami_step_case_empty.
    - kami_step_case_empty.

    - (* case "pgmInit" *)
      kinvert_pre.
      left; eapply kamiStep_sound_case_pgmInit; eauto.

    - (* case "pgmInitEnd" *)
      kinvert_pre.
      left; eapply kamiStep_sound_case_pgmInitEnd; eauto.

    - (* case "execLd" *)
      kinvert_pre.
      right.
      case TODO_joonwon.

    - (* case "execLdZ" *) case TODO_joonwon.
    - (* case "execSt" *) case TODO_joonwon.
    - (* case "execNm" *)
      right.
      match goal with
      | [H: states_related _ _ |- _] => inversion H; subst; clear H
      end.

      kinvert_pre.
      kinvert_more.
      kinv_action_dest_nosimpl.
      block_subst kupd.
      red_regmap.
      red_trivial_conds.
      cleanup_trivial.
      unblock_subst kupd.

      (** Invert a riscv-coq step *)

      (* -- fetch *)
      repeat t.
      specialize (H1 eq_refl).
      destruct H11; specialize (H8 H1).
      eapply fetch_ok in H1; [|eassumption..].
      destruct H1 as (rinst & ? & ?).
      rewrite H1 in H5.
      repeat t.
      setoid_rewrite H9 in H5.

      (** Begin symbolic evaluation of kami code *)

      cbn [evalExpr evalUniBool evalBinBit evalConstT getDefaultConst isEq
           getNextPc doExec rv32NextPc rv32Exec rv32DoExec
           getFunct3E getFunct7E getOffsetUE getOpcodeE getOffsetShamtE getOffsetIE getRdE
           getSrc1 getSrc2 getDst rv32Dec rv32GetSrc1 rv32GetSrc2 rv32GetDst getRs1E getRs2E
           BitsPerByte
           Nat.add Nat.sub
           ] in *.

      (* COQBUG(rewrite pattern matching on if/match is broken due to "hidden branch types") *)
      repeat match goal with
      | H : context G [if ?x then ?a else ?b] |- _ =>
          let e := context G [@bool_rect (fun _ => _) a b x] in
          change e in H
      | H : context G [if ?x then ?a else ?b] |- _ =>
          let e := context G [@sumbool_rect _ _ (fun _ => _) (fun _ => a) (fun _ => b) x] in
          change e in H
      end.

      repeat match goal with H : _ |- _ =>
          progress repeat rewrite ?sumbool_rect_bool_weq, <-?unsigned_eqb in H
      end.

      progress
      repeat match goal with H: context G [Z.of_N (@wordToN ?n ?x)] |- _ =>
      let nn := eval cbv in (Z.of_nat n) in
      let e := context G [@kunsigned nn x] in
      change e in H
      end.
 
      progress
      repeat match goal with H: context G [kunsigned (@ZToWord ?n ?x)] |- _ =>
      let e := context G [x] in
      change e in H
      end.

      cbv [bool_rect] in *.

      (* Evaluation almost done, separate out cases of Kami execution *)
      progress
      repeat match goal with
      | H : context G [if Z.eqb ?x ?y then ?a else ?b] |- _ =>
          destruct (Z.eqb_spec x y) in *
      | H: ?x = ?a,
        G: ?x = ?b |- _ =>
        let aa := eval cbv delta [a] in a in
        let bb := eval cbv delta [b] in b in
        let t := isZcst aa in constr_eq t true;
        let t := isZcst bb in constr_eq t true;
        assert_fails (constr_eq aa bb);
        exfalso; remember x; clear -H G;
        cbv in H; cbv in G; rewrite H in G; inversion G
      | H: ?x = ?a,
        G: ?x <> ?b |- _ =>
        let aa := eval cbv delta [a] in a in
        let bb := eval cbv delta [b] in b in
        let t := isZcst aa in constr_eq t true;
        let t := isZcst bb in constr_eq t true;
        assert_fails (constr_eq aa bb);
        clear G
      end.


      (* More symbolic evaluation... *)
      (* TODO maybe we can do this earlier, but kami interpreter has bare proofs inside its definition, so maybe not *)
      24(*add*),34(*sub*):
        cbv [kunsigned evalUniBit] in *;
        repeat match goal with
        | H: _ |- _ => progress rewrite ?unsigned_split2_split1_as_bitSlice, ?unsigned_split1_as_bitSlice, ?unsigned_split2_as_bitSlice in H
        | H : context G [ Z.of_nat ?n ] |- _ =>
          let nn := eval cbv in (Z.of_nat n) in
          let e := context G [nn] in
          change e in H
        | H : context G [ Z.add ?x ?y ] |- _ =>
            let t := isZcst x in constr_eq t true;
            let t := isZcst y in constr_eq t true;
            let z := eval cbv in (Z.add x y) in
            let e := context G [z] in
            change e in H
        | H : context G [ Z.of_N (wordToN ?x) ] |- _ =>
            let e := context G [kunsigned x] in
            change e in H
        | H : negb ?x = true |- _ => eapply Bool.negb_true_iff in H

        | H : Z.eqb _ _ = true |- _ => eapply Z.eqb_eq in H
        | H : Z.eqb _ _ = false |- _ => eapply Z.eqb_neq in H
        
        end;
        repeat match goal with
        | [H: context [Z.of_N (@wordToN ?sz _)] |- _] =>
            progress change sz with 32%nat in H
        end;
        lazymatch goal with
        | H : context [decode _ _ ] |- _ => eval_decode_in H end;

        repeat t;
        do 2 eexists;
        prove_KamiLabelR;
        prove_states_related.

      38: { (* unknown opcode *)

      (* More symbolic evaluation... *)
      (* TODO maybe we can do this earlier, but kami interpreter has bare proofs inside its definition, so maybe not *)
      all: cbv [kunsigned evalUniBit] in *.
      all:
        repeat match goal with
        | H: _ |- _ => progress rewrite ?unsigned_split2_split1_as_bitSlice, ?unsigned_split1_as_bitSlice, ?unsigned_split2_as_bitSlice in H
        | H : context G [ Z.of_nat ?n ] |- _ =>
          let nn := eval cbv in (Z.of_nat n) in
          let e := context G [nn] in
          change e in H
        | H : context G [ Z.add ?x ?y ] |- _ =>
            let t := isZcst x in constr_eq t true;
            let t := isZcst y in constr_eq t true;
            let z := eval cbv in (Z.add x y) in
            let e := context G [z] in
            change e in H
        | H : context G [ Z.of_N (wordToN ?x) ] |- _ =>
            let e := context G [kunsigned x] in
            change e in H
        end.

      (* forward through riscv-coq... *)
       eapply Z.eqb_neq in n.
       eapply Z.eqb_neq in n0.
       eapply Z.eqb_neq in n1.
       eapply Z.eqb_neq in n2.
       eapply Z.eqb_neq in n3.
       eapply Z.eqb_neq in n4.
       eapply Z.eqb_neq in n5.
       remember (decode _ _) as instr in *.
       cbv beta iota delta [decode] in Heqinstr.
       repeat match goal with
       | H : ?A = let x := ?v in @?C x |- _ =>
           let x := fresh x in pose v as x;
           let C := eval cbv beta in (C x) in
           change (A = C) in H;
           pose proof (eq_refl : x = v); clearbody x
       end.
       subst opcode.
       repeat
         match goal with
         | [H: context [Z.of_N (@wordToN ?sz _)] |- _] =>
           progress change sz with 32%nat in H
         end.
       progress
       repeat match goal with
       | H : _ = false, G : _ |- _ => rewrite !H in G
       end.

       (* the hypotheses describe an unknown non-memory opcode *)
       (* what instruction decoding caused [execNm] to fire? *)
       (* where is the corresponding hypothesis? *)
       case TODO_joonwon.
      }
    1,2,3,4,5,6,7,8,9,10,11,12,13,14,15,16,17,18,19,20,21,22,23,24,25,26,27,28,29,30,31,32,33,34,35,36,37: case TODO_kamiStep_instruction.

    - (* case "execNmZ" *)
      right.
      match goal with
      | [H: states_related _ _ |- _] => inversion H; subst; clear H
      end.

      kinvert_pre.
      kinvert_more.
      kinv_action_dest_nosimpl.
      block_subst kupd.
      red_regmap.
      red_trivial_conds.
      cleanup_trivial.
      unblock_subst kupd.

      (** Invert a riscv-coq step *)

      (* -- fetch *)
      repeat t.
      specialize (H1 eq_refl).
      destruct H11; specialize (H8 H1).
      eapply fetch_ok in H1; [|eassumption..].
      destruct H1 as (rinst & ? & ?).
      rewrite H1 in H5.
      repeat t.
      setoid_rewrite H9 in H5.

      (** Begin symbolic evaluation of kami code *)

      cbn [evalExpr evalUniBool evalBinBit evalConstT getDefaultConst isEq Data
           getNextPc doExec rv32NextPc rv32Exec rv32DoExec
           getFunct3E getFunct7E getOffsetUE getOpcodeE getOffsetShamtE getOffsetIE getRdE
           getSrc1 getSrc2 getDst rv32Dec rv32GetSrc1 rv32GetSrc2 rv32GetDst getRs1E getRs2E getRs1ValueE getRs2ValueE getOffsetSBE
           BitsPerByte
           Nat.add Nat.sub
           ] in *.

      (* COQBUG(rewrite pattern matching on if/match is broken due to "hidden branch types") *)
      repeat match goal with
      | H : context G [if ?x then ?a else ?b] |- _ =>
          let e := context G [@bool_rect (fun _ => _) a b x] in
          change e in H
      | H : context G [if ?x then ?a else ?b] |- _ =>
          let e := context G [@sumbool_rect _ _ (fun _ => _) (fun _ => a) (fun _ => b) x] in
          change e in H
      end.

      repeat match goal with H : _ |- _ =>
          progress repeat rewrite ?sumbool_rect_bool_weq, <-?unsigned_eqb in H
      end.

      progress
      repeat match goal with H: context G [Z.of_N (@wordToN ?n ?x)] |- _ =>
      let nn := eval cbv in (Z.of_nat n) in
      let e := context G [@kunsigned nn x] in
      change e in H
      end.
 
      progress
      repeat match goal with H: context G [kunsigned (@ZToWord ?n ?x)] |- _ =>
      let e := context G [x] in
      change e in H
      end.

      cbv [bool_rect] in *.

      progress
      repeat match goal with
      | H : context G [if Z.eqb ?x ?y then ?a else ?b] |- _ =>
          destruct (Z.eqb_spec x y) in *
      | H: ?x = ?a,
        G: ?x = ?b |- _ =>
        let aa := eval cbv delta [a] in a in
        let bb := eval cbv delta [b] in b in
        let t := isZcst aa in constr_eq t true;
        let t := isZcst bb in constr_eq t true;
        assert_fails (constr_eq aa bb);
        exfalso; remember x; clear -H G;
        cbv in H; cbv in G; rewrite H in G; inversion G
      | H: ?x = ?a,
        G: ?x <> ?b |- _ =>
        let aa := eval cbv delta [a] in a in
        let bb := eval cbv delta [b] in b in
        let t := isZcst aa in constr_eq t true;
        let t := isZcst bb in constr_eq t true;
        assert_fails (constr_eq aa bb);
        clear G
      end.

      (* More symbolic evaluation... *)
      (* TODO maybe we can do this earlier, but kami interpreter has bare proofs inside its definition, so maybe not *)
      all: cbv [kunsigned evalUniBit] in *.
      all:
        repeat match goal with
        | H: _ |- _ => progress rewrite ?unsigned_split2_split1_as_bitSlice, ?unsigned_split1_as_bitSlice, ?unsigned_split2_as_bitSlice in H
        | H : context G [ Z.of_nat ?n ] |- _ =>
          let nn := eval cbv in (Z.of_nat n) in
          let e := context G [nn] in
          change e in H
        | H : context G [ Z.add ?x ?y ] |- _ =>
            let t := isZcst x in constr_eq t true;
            let t := isZcst y in constr_eq t true;
            let z := eval cbv in (Z.add x y) in
            let e := context G [z] in
            change e in H
        | H : context G [ Z.of_N (wordToN ?x) ] |- _ =>
            let e := context G [kunsigned x] in
            change e in H
        end.

      all : case TODO_kamiStep_instruction.

  Qed.

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

  Definition mm: Modules := Kami.Ex.SC.mm rv32DataBytes kamiMemInit kami_FE310_AbsMMIO.
  Definition p4mm: Modules := p4mm Hinstr kamiMemInit kami_FE310_AbsMMIO.

  Local Notation procInit := (procInit (instrMemSizeLg:= instrMemSizeLg)).

  Definition riscvRegsInit:
    {rrfi: Registers & regs_related (evalConstT (rfInit procInit)) rrfi}.
  Proof.
    case TODO_joonwon.
  Defined.

  Definition riscvMemInit:
    {rmemi: mem & mem_related (evalConstT kamiMemInit) rmemi}.
  Proof.
    case TODO_joonwon.
  Defined.

  Lemma states_related_init:
    states_related
      (initRegs (getRegInits (@proc instrMemSizeLg Hinstr kamiMemInit kami_FE310_AbsMMIO)), [])
      {| getMachine :=
           {| RiscvMachine.getRegs := projT1 riscvRegsInit;
              RiscvMachine.getPc := word.of_Z 0;
              RiscvMachine.getNextPc := word.of_Z 4;
              RiscvMachine.getMem := projT1 riscvMemInit;
              RiscvMachine.getXAddrs := kamiXAddrs;
              RiscvMachine.getLog := nil; (* <-- intended to be nil *) |};
         getMetrics := MetricLogging.EmptyMetricLog; |}.
  Proof.
    econstructor; try reflexivity.
    2: eapply pRegsToT_init.
    - econstructor.
    - intros; discriminate.
    - split; [reflexivity|].
      intros; apply wordToN_wzero.
    - apply (projT2 riscvRegsInit).
    - apply (projT2 riscvMemInit).
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
                m0RV.(getMem) = projT1 riscvMemInit ->
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
    pose proof (@proc_correct instrMemSizeLg Hinstr kamiMemInit) as P.
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
      + simpl.
        case TODO_joonwon.
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
