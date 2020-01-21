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

Lemma Npow2_lt:
  forall n m,
    (n < m)%nat -> (NatLib.Npow2 n < NatLib.Npow2 m)%N.
Proof.
  induction m; simpl; intros.
  - blia.
  - assert (n = m \/ n < m)%nat by blia.
    destruct H0.
    + subst.
      destruct (NatLib.Npow2 m) eqn:Hp.
      * exfalso; eapply NatLib.Npow2_not_zero; eauto.
      * blia.
    + specialize (IHm H0).
      destruct (NatLib.Npow2 m); blia.
Qed.

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

Lemma wordToN_wplus_distr:
  forall sz (w1 w2: Word.word sz),
    (wordToN w1 + wordToN w2 < NatLib.Npow2 sz)%N ->
    wordToN (w1 ^+ w2) = (wordToN w1 + wordToN w2)%N.
Proof.
  cbv [wplus wordBin]; intros.
  apply wordToN_NToWord_2; assumption.
Qed.

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
    cbv [
    iset
    andb

    Z.gtb Z.eqb Pos.eqb
    BinInt.Z.of_nat Pos.of_succ_nat
    BinInt.Z.compare Pos.compare Pos.compare_cont
    Datatypes.length nth

    (* grep Definition ./deps/riscv-coq/src/riscv/Spec/Decode.v | cut -d' ' -f2 | sort | uniq | tr '\n' ' ' ; echo *)
        bitwidth decode FPRegister funct12_EBREAK funct12_ECALL funct12_MRET funct12_SRET funct12_URET funct12_WFI funct2_FMADD_S funct3_ADD funct3_ADDI funct3_ADDIW funct3_ADDW funct3_AMOD funct3_AMOW funct3_AND funct3_ANDI funct3_BEQ funct3_BGE funct3_BGEU funct3_BLT funct3_BLTU funct3_BNE funct3_CSRRC funct3_CSRRCI funct3_CSRRS funct3_CSRRSI funct3_CSRRW funct3_CSRRWI funct3_DIV funct3_DIVU funct3_DIVUW funct3_DIVW funct3_FCLASS_S funct3_FENCE funct3_FENCE_I funct3_FEQ_S funct3_FLE_S funct3_FLT_S funct3_FLW funct3_FMAX_S funct3_FMIN_S funct3_FMV_X_W funct3_FSGNJN_S funct3_FSGNJ_S funct3_FSGNJX_S funct3_FSW funct3_LB funct3_LBU funct3_LD funct3_LH funct3_LHU funct3_LW funct3_LWU funct3_MUL funct3_MULH funct3_MULHSU funct3_MULHU funct3_MULW funct3_OR funct3_ORI funct3_PRIV funct3_REM funct3_REMU funct3_REMUW funct3_REMW funct3_SB funct3_SD funct3_SH funct3_SLL funct3_SLLI funct3_SLLIW funct3_SLLW funct3_SLT funct3_SLTI funct3_SLTIU funct3_SLTU funct3_SRA funct3_SRAI funct3_SRAIW funct3_SRAW funct3_SRL funct3_SRLI funct3_SRLIW funct3_SRLW funct3_SUB funct3_SUBW funct3_SW funct3_XOR funct3_XORI funct5_AMOADD funct5_AMOAND funct5_AMOMAX funct5_AMOMAXU funct5_AMOMIN funct5_AMOMINU funct5_AMOOR funct5_AMOSWAP funct5_AMOXOR funct5_LR funct5_SC funct6_SLLI funct6_SRAI funct6_SRLI funct7_ADD funct7_ADDW funct7_AND funct7_DIV funct7_DIVU funct7_DIVUW funct7_DIVW funct7_FADD_S funct7_FCLASS_S funct7_FCVT_S_W funct7_FCVT_W_S funct7_FDIV_S funct7_FEQ_S funct7_FMIN_S funct7_FMUL_S funct7_FMV_W_X funct7_FMV_X_W funct7_FSGNJ_S funct7_FSQRT_S funct7_FSUB_S funct7_MUL funct7_MULH funct7_MULHSU funct7_MULHU funct7_MULW funct7_OR funct7_REM funct7_REMU funct7_REMUW funct7_REMW funct7_SFENCE_VMA funct7_SLL funct7_SLLIW funct7_SLLW funct7_SLT funct7_SLTU funct7_SRA funct7_SRAIW funct7_SRAW funct7_SRL funct7_SRLIW funct7_SRLW funct7_SUB funct7_SUBW funct7_XOR isValidA isValidA64 isValidCSR isValidF isValidF64 isValidI isValidI64 isValidM isValidM64 Opcode opcode_AMO opcode_AUIPC opcode_BRANCH opcode_JAL opcode_JALR opcode_LOAD opcode_LOAD_FP opcode_LUI opcode_MADD opcode_MISC_MEM opcode_MSUB opcode_NMADD opcode_NMSUB opcode_OP opcode_OP_32 opcode_OP_FP opcode_OP_IMM opcode_OP_IMM_32 opcode_STORE opcode_STORE_FP opcode_SYSTEM Register RoundMode rs2_FCVT_L_S rs2_FCVT_LU_S rs2_FCVT_W_S rs2_FCVT_WU_S supportsA supportsF supportsM
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

From coqutil Require Import rdelta.

Ltac zcstP x :=
  let x := rdelta x in
  let t := isZcst x in
  constr_eq t true.
Ltac natcstP x :=
  let x := rdelta x in
  let t := isnatcst x in
  constr_eq t true.
Ltac boolcstP x :=
  let x := rdelta x in
  first [constr_eq x true | constr_eq x false].

Ltac eval2 op arg1P arg2P :=
  repeat match goal with
  | H : context G [op ?x ?y] |- _ =>
      arg1P x; arg2P y;
      let z := eval cbv in (op x y) in
      let e := context G [z] in
      change e in H
  | H := context G [op ?x ?y] |- _ =>
      arg1P x; arg2P y;
      let z := eval cbv in (op x y) in
      let e := context G [z] in
      change e in (value of H)
  | |- context G [op ?x ?y] =>
      arg1P x; arg2P y;
      let z := eval cbv in (op x y) in
      let e := context G [z] in
      change e
  end.

Ltac open_decode :=
  let H := lazymatch goal with H : context [decode _ _ ] |- _ => H end in
  let a := lazymatch type of H with context [decode ?a _ ] => a end in
  let b := lazymatch type of H with context [decode _ ?b ] => b end in
  let dec := fresh "dec" in
  let Hdec := fresh "Hdec" in
  remember (decode a b) as dec eqn:Hdec in H;
  cbv beta iota delta [decode] in Hdec;
  let H := Hdec in
  repeat
  match goal with
  | [Hbs: bitSlice _ _ _ = _ |- _] => rewrite !Hbs in H
  end.

  (* kitchen sink goal simplification? *)
  Ltac t  :=
    match goal with
    | H : ?LHS = let x := ?v in ?C |- _ =>
        change (let x := v in LHS = C) in H
    | H := let x := ?v in @?C x |- _ =>
        let x := fresh x in pose v as x;
        let C := eval cbv beta in (C x) in
        change C in (value of H)
    | H: let x := ?v in @?C x |- _ =>
        let x := fresh x in pose v as x;
        let C := eval cbv beta in (C x) in
        change C in H
    | |- let x := _ in _ => intro
    | x := ?y |- _ => first [is_var y|is_const y|is_ind y|is_constructor y]; subst x
    | H : context G [ Z.of_nat ?n ] |- _ =>
        natcstP n;
        let nn := eval cbv in (Z.of_nat n) in
        let e := context G [nn] in
        change e in H
    | _ => progress eval2 Z.add zcstP zcstP
    | _ => progress eval2 Z.eqb zcstP zcstP
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

  Local Lemma wordToN_ZToWord_four:
    forall sz, (3 <= sz)%nat -> wordToN (ZToWord sz 4) = 4%N.
  Proof.
    intros.
    apply N2Z.inj.
    rewrite unsigned_wordToZ.
    rewrite Z.mod_small.
    - reflexivity.
    - apply inj_le in H; simpl in H.
      split; [blia|].
      eapply Z.lt_le_trans; [|eapply Z.pow_le_mono_r with (b:= 3); blia].
      blia.
  Qed.

  Lemma pc_related_plus4:
    forall instrMem kdataMem xaddrs,
      (* (forall a, isXAddr4 a xaddrs -> isXAddr4 a kamiXAddrs) -> *)
      RiscvXAddrsSafe instrMemSizeLg instrMem kdataMem xaddrs ->
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
    cbv [word.add word WordsKami wordW KamiWord.word] in H3.
    cbv [word.add word WordsKami wordW KamiWord.word].

    assert (instrMemSizeLg = width - 2 \/ instrMemSizeLg < width - 2) by blia.
    destruct H4; [subst; apply wordToN_inj in H2; subst; reflexivity|].
    clear Hinstr2.
    rename H4 into Hinstr2.

    assert (wordToN rpc + 4 < NatLib.Npow2 (2 + Z.to_nat instrMemSizeLg))%N.
    { rewrite <-wordToN_ZToWord_four with (sz:= Z.to_nat width) by (simpl; blia).
      rewrite <-wordToN_wplus_distr.
      { apply kamiXAddrs_isXAddr4_bound.
        apply H; assumption.
      }
      { rewrite wordToN_ZToWord_four by (simpl; blia).
        rewrite <-H2.
        pose proof (wordToN_bound kpc).
        eapply N.lt_le_trans.
        { eapply N.add_lt_mono; [eassumption|].
          instantiate (1:= NatLib.Npow2 (2 + Z.to_nat instrMemSizeLg)).
          change 4%N with (NatLib.Npow2 2).
          apply Npow2_lt.
          apply Z2Nat.inj_le in Hinstr1; [|blia..].
          simpl; simpl in Hinstr1; blia.
        }
        { rewrite <-NatLib.Npow2_S.
          apply Npow2_le.
          apply Z2Nat.inj_lt in Hinstr2; [|blia..].
          simpl; simpl in Hinstr2; blia.
        }
      }
    }

    rewrite wordToN_wplus_distr.
    2: {
      rewrite H2.
      rewrite wordToN_ZToWord_four
        by (apply Z2Nat.inj_le in Hinstr1; simpl in Hinstr1; blia).
      assumption.
    }
    rewrite wordToN_ZToWord_four
      by (apply Z2Nat.inj_le in Hinstr1; simpl in Hinstr1; blia).
    cbv [word.of_Z kofZ].
    rewrite wordToN_wplus_distr.
    2: {
      rewrite wordToN_ZToWord_four by (simpl; blia).
      eapply N.lt_le_trans; [eassumption|].
      apply Npow2_le.
      apply Z2Nat.inj_lt in Hinstr2; simpl in Hinstr2; simpl; blia.
    }
    rewrite wordToN_ZToWord_four by (simpl; blia).
    congruence.
  Qed.

  Ltac prove_states_related :=
    econstructor;
    [ solve [trivial]
    | clear; cbv [RegsToT pRegsToT]; kregmap_red; exact eq_refl
    | clear; intro; discriminate
    | solve [trivial]
    | cbv [RiscvMachine.getNextPc]; split;
      [ try (apply AddrAligned_plus4; assumption)
      | try (intros; eapply pc_related_plus4; try eassumption; red; auto; fail)]
    | solve [trivial]
    | try (eapply regs_related_put;
           [ solve [trivial] | solve [trivial] | | ];
           erewrite ?regs_related_get,
           ?unsigned_split2_split1_as_bitSlice
             by eauto;
           trivial)
    | solve [trivial]
    ].

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
      pose proof H1 as Hxaddr.
      eapply fetch_ok in H1; [|eassumption..].
      destruct H1 as (rinst & ? & ?).
      rewrite H1 in H5.
      repeat t.
      setoid_rewrite H9 in H5.

      (** Begin symbolic evaluation of kami code *)

      cbn [evalExpr evalUniBool evalBinBit evalConstT getDefaultConst isEq Data
           BitsPerByte
           Nat.add Nat.sub

      (* grep -oP 'Definition \w+' ~/plv/bedrock2/deps/kami/Kami/Ex/{IsaRv32.v,SC.v} | cut -d' ' -f2 | sort | uniq | tr '\n' ' ' ; printf '\n' *)
           AlignAddrT AlignInstT DstE DstK DstT ExecT f3Lb f3Lbu f3Lh f3Lhu f3Lw getFunct3E getFunct7E getOffsetIE getOffsetSBE getOffsetSE getOffsetShamtE getOffsetUE getOffsetUJE getOpcodeE getRdE getRs1E getRs1ValueE getRs2E getRs2ValueE IsMMIOE IsMMIOT LdAddrCalcT LdAddrE LdAddrK LdAddrT LdDstE LdDstK LdDstT LdSrcE LdSrcK LdSrcT LdTypeE LdTypeK LdTypeT LdValCalcT MemInit memInst memOp mm mmioExec nextPc NextPcT OpcodeE OpcodeK OpcodeT opLd opNm opSt OptypeE OptypeK OptypeT Pc pinst procInitDefault procInst RqFromProc RsToProc rv32AlignAddr rv32AlignInst rv32CalcLdAddr rv32CalcLdVal rv32CalcStAddr rv32DataBytes rv32DoExec rv32GetDst rv32GetLdAddr rv32GetLdDst rv32GetLdSrc rv32GetLdType rv32GetOptype rv32GetSrc1 rv32GetSrc2 rv32GetStAddr rv32GetStSrc rv32GetStVSrc rv32InstBytes rv32NextPc rv32RfIdx scmm Src1E Src1K Src1T Src2E Src2K Src2T StAddrCalcT StAddrE StAddrK StAddrT StateE StateK StateT StSrcE StSrcK StSrcT StVSrcE StVSrcK StVSrcT
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

      set (kinst := instrMem (@evalUniBit (S (S (BinInt.Z.to_nat instrMemSizeLg))) (BinInt.Z.to_nat instrMemSizeLg) (TruncLsb 2 (BinInt.Z.to_nat instrMemSizeLg)) kpc)) in *;
      progress cbn [evalUniBit] in kinst.

  Timeout 300
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

  all: match goal with _ => idtac end; time (
    repeat match goal with
          | H: _ |- _ => rewrite !(match TODO_andres with end : forall a b x, evalUniBit (SignExtendTrunc a b) x = ZToWord b (wordToZ x)) in H
          | H: _ |- _ => rewrite !(match TODO_andres with end : forall a b x, evalUniBit (ZeroExtendTrunc a b) x = NToWord b (wordToN x)) in H
      end;
    cbv [evalUniBit] in *; (* would reveal proofs if not rewritten above *)
    cbv [kunsigned] in *;
    repeat match goal with
      | H: _ |- _ => progress rewrite ?unsigned_split2_split1_as_bitSlice, ?unsigned_split1_as_bitSlice, ?unsigned_split2_as_bitSlice in H
    end;
    repeat match goal with
      | H : context [ Z.of_nat ?n ] |- _ =>
          natcstP n;
          let nn := eval cbv in (Z.of_nat n) in
          change (Z.of_nat n) with nn in H
    end;
    repeat match goal with
      | H : context [ Z.add ?x ?y ] |- _ =>
          let t := isZcst x in constr_eq t true;
          let t := isZcst y in constr_eq t true;
          let z := eval cbv in (Z.add x y) in
          change (Z.add x y) with z in H
    end;
    repeat match goal with
      | H : context [ Z.of_N (@wordToN ?w ?x) ] |- _ =>
          change (Z.of_N (@wordToN w x)) with (@kunsigned 32 x) in H
    end;
    repeat match goal with
      | H : context [(?instrMem (split2 2 (Z.to_nat instrMemSizeLg) ?kpc))] |- _ => progress change (instrMem (split2 2 (Z.to_nat instrMemSizeLg) kpc)) with kinst in H
    end;

    let dec := fresh "dec" in
    let Hdec := fresh "Hdec" in
    match goal with
      H : context[decode ?a ?b] |- _ =>
          remember (decode a b) as dec eqn:Hdec in H
    end;
    cbv beta iota delta [decode] in Hdec;
    repeat
    match goal with
    | [Hbs: bitSlice _ _ _ = _ |- _] => rewrite !Hbs in Hdec
    end;

    repeat match goal with _ => progress
    cbn iota beta delta [
    iset
    andb

    Z.gtb Z.eqb Pos.eqb
    BinInt.Z.of_nat Pos.of_succ_nat
    BinInt.Z.compare Pos.compare Pos.compare_cont
    Datatypes.length nth

    (* grep Definition ./deps/riscv-coq/src/riscv/Spec/Decode.v | cut -d' ' -f2 | sort | uniq | tr '\n' ' ' ; echo *)
    bitwidth decode FPRegister funct12_EBREAK funct12_ECALL funct12_MRET funct12_SRET funct12_URET funct12_WFI funct2_FMADD_S funct3_ADD funct3_ADDI funct3_ADDIW funct3_ADDW funct3_AMOD funct3_AMOW funct3_AND funct3_ANDI funct3_BEQ funct3_BGE funct3_BGEU funct3_BLT funct3_BLTU funct3_BNE funct3_CSRRC funct3_CSRRCI funct3_CSRRS funct3_CSRRSI funct3_CSRRW funct3_CSRRWI funct3_DIV funct3_DIVU funct3_DIVUW funct3_DIVW funct3_FCLASS_S funct3_FENCE funct3_FENCE_I funct3_FEQ_S funct3_FLE_S funct3_FLT_S funct3_FLW funct3_FMAX_S funct3_FMIN_S funct3_FMV_X_W funct3_FSGNJN_S funct3_FSGNJ_S funct3_FSGNJX_S funct3_FSW funct3_LB funct3_LBU funct3_LD funct3_LH funct3_LHU funct3_LW funct3_LWU funct3_MUL funct3_MULH funct3_MULHSU funct3_MULHU funct3_MULW funct3_OR funct3_ORI funct3_PRIV funct3_REM funct3_REMU funct3_REMUW funct3_REMW funct3_SB funct3_SD funct3_SH funct3_SLL funct3_SLLI funct3_SLLIW funct3_SLLW funct3_SLT funct3_SLTI funct3_SLTIU funct3_SLTU funct3_SRA funct3_SRAI funct3_SRAIW funct3_SRAW funct3_SRL funct3_SRLI funct3_SRLIW funct3_SRLW funct3_SUB funct3_SUBW funct3_SW funct3_XOR funct3_XORI funct5_AMOADD funct5_AMOAND funct5_AMOMAX funct5_AMOMAXU funct5_AMOMIN funct5_AMOMINU funct5_AMOOR funct5_AMOSWAP funct5_AMOXOR funct5_LR funct5_SC funct6_SLLI funct6_SRAI funct6_SRLI funct7_ADD funct7_ADDW funct7_AND funct7_DIV funct7_DIVU funct7_DIVUW funct7_DIVW funct7_FADD_S funct7_FCLASS_S funct7_FCVT_S_W funct7_FCVT_W_S funct7_FDIV_S funct7_FEQ_S funct7_FMIN_S funct7_FMUL_S funct7_FMV_W_X funct7_FMV_X_W funct7_FSGNJ_S funct7_FSQRT_S funct7_FSUB_S funct7_MUL funct7_MULH funct7_MULHSU funct7_MULHU funct7_MULW funct7_OR funct7_REM funct7_REMU funct7_REMUW funct7_REMW funct7_SFENCE_VMA funct7_SLL funct7_SLLIW funct7_SLLW funct7_SLT funct7_SLTU funct7_SRA funct7_SRAIW funct7_SRAW funct7_SRL funct7_SRLIW funct7_SRLW funct7_SUB funct7_SUBW funct7_XOR isValidA isValidA64 isValidCSR isValidF isValidF64 isValidI isValidI64 isValidM isValidM64 Opcode opcode_AMO opcode_AUIPC opcode_BRANCH opcode_JAL opcode_JALR opcode_LOAD opcode_LOAD_FP opcode_LUI opcode_MADD opcode_MISC_MEM opcode_MSUB opcode_NMADD opcode_NMSUB opcode_OP opcode_OP_32 opcode_OP_FP opcode_OP_IMM opcode_OP_IMM_32 opcode_STORE opcode_STORE_FP opcode_SYSTEM Register RoundMode rs2_FCVT_L_S rs2_FCVT_LU_S rs2_FCVT_W_S rs2_FCVT_WU_S supportsA supportsF supportsM

    ] in *
    | x := @nil _ |- _ => subst x
    | _ => t
    end;

    repeat match goal with
    | H : ?x <> ?A |- _ =>
        match goal with
        | y := x |- _ =>
            match goal with
              _out := context[y =? A] |- _ =>
                  let RR := fresh "RR" in
                  destruct (Z.eqb_spec y A) as [RR|_] in *;
                      [ case (H RR) | ]
    end end end).

    (** known ISA compatibility/decoding issues... *)
    all : try match goal with
    (* kami confuses SRLI and SRAI because it ignores funct3 *)
    H: bitSlice (kunsigned ?kinst) 12 15 = funct3_SRLI
        |- _ => case TODO_joonwon |
    H: bitSlice (kunsigned ?kinst) 12 15 = funct3_SRAI
        |- _ => case TODO_joonwon |
    (* : kami decodes ausing funct7 only. this is may be a problem because iset=RV32IM but Kami ignores M instructions other than multiply. *)
    e : bitSlice (kunsigned ?kinst) 0 7 = opcode_OP,
    n5 : bitSlice (kunsigned ?kinst) 25 32 <> funct7_ADD,
    n6 : bitSlice (kunsigned ?kinst) 25 32 <> funct7_SUB,
    n7 : bitSlice (kunsigned ?kinst) 25 32 <> funct7_MUL
        |- _ => case TODO_joonwon |
    H: bitSlice (kunsigned ?kinst) 25 32 = funct7_ADD,
    G: bitSlice (kunsigned ?kinst) 12 15 <> funct3_ADD
        |- _ => case TODO_joonwon |
    H: bitSlice (kunsigned ?kinst) 25 32 = funct7_MUL,
    G: bitSlice (kunsigned ?kinst) 12 15 <> funct3_MUL
        |- _ => case TODO_joonwon |
    H: bitSlice (kunsigned ?kinst) 25 32 = funct7_SUB,
    G: bitSlice (kunsigned ?kinst) 12 15 <> funct3_SUB
        |- _ => case TODO_joonwon |
    (* why do we have opcode_LOAD/STORE in execNm? *)
    H: bitSlice (kunsigned ?kinst) 0 7 = opcode_LOAD
        |- _ => case TODO_joonwon |
    H: bitSlice (kunsigned ?kinst) 0 7 = opcode_STORE
        |- _ => case TODO_joonwon|
    (* kami supports fewer instructions than riscv-coq *)
    n : bitSlice (kunsigned ?kinst) 0 7 <> opcode_BRANCH,
    n0 : bitSlice (kunsigned ?kinst) 0 7 <> opcode_LUI,
    n1 : bitSlice (kunsigned ?kinst) 0 7 <> opcode_AUIPC,
    n2 : bitSlice (kunsigned ?kinst) 0 7 <> opcode_JAL,
    n3 : bitSlice (kunsigned ?kinst) 0 7 <> opcode_JALR,
    n4 : bitSlice (kunsigned ?kinst) 0 7 <> opcode_OP_IMM,
    n5 : bitSlice (kunsigned ?kinst) 0 7 <> opcode_OP,
    n6 : bitSlice (kunsigned ?kinst) 0 7 <> opcode_LOAD,
    n7 : bitSlice (kunsigned ?kinst) 0 7 <> opcode_STORE
        |- _ => case TODO_joonwon
    end.

    all : try match goal with
      shamtHi := bitSlice (kunsigned _) 25 26,
      shamtHiTest := ((?shamtHi =? 0) || false)%bool,
          decodeI := if ((?funct6 =? funct6_SLLI) && ?shamtHiTest)%bool
          then Slli ?rd ?rs1 ?shamt6
          else InvalidI |- _ =>
              destruct ((funct6 =? funct6_SLLI) && shamtHiTest)%bool eqn:? in *; [|subst dec; repeat t;contradiction]
    end.

    (* kami SLLI decoding relies on illegal instructions being undefined behavior and has dont-care logic *)

    (** decoding done *)
    all: subst dec; mcomp_step_in H5;
      repeat match goal with
      | H : False |- _ => case H
      | H : Z |- _ => clear H
      | H : list Instruction |- _ => clear H
      | H : Instruction |- _ => clear H
      end.

    (** known proof automation issues *)
    (* TODO: we should not blast cases of riscv-coq when hypotheses tell us
     * which case kami took *)
    Ltac x := match goal with
      | H5 : context G [let x := ?y in @?z x] |- _ =>
          let x' := fresh x in
          pose y as x';
          let zy := eval cbv beta in (z x') in
          let h' := context G [zy] in
          change h' in H5
      | _ => progress cbn iota beta delta [when free.bind] in *
      | H5 : mcomp_sat _ _ _ |- _ =>
          match type of H5 with
          | context G [when ?b _] =>
              destr b
          | context G [if ?b then _ else _] =>
              destr b
          end
    | H:False |- _ => case H
    | _ => t
      end.

    all : repeat (x || t).
    all : eexists _, _.
    all : prove_KamiLabelR.

    all:
      repeat match goal with
      | H : negb ?x = true |- _ => eapply Bool.negb_true_iff in H
      | H : Z.eqb _ _ = true |- _ => eapply Z.eqb_eq in H
      | H : Z.eqb _ _ = false |- _ => eapply Z.eqb_neq in H
      end;
      try (case (Z.eq_dec rd Register0) as [X|_];
          [match goal with H : bitSlice (kunsigned _) 7 12 <> _ |- _ => case (H X) end|]).
    all : try subst regs; try subst kupd.

    all: prove_states_related.

    all :
    try match goal with
    |- ?f ?x ?y = ?g ?a ?b
        => let X := fresh "arg1" in
        set (X := x); change a with X;
        clearbody X
    end;
    try match goal with
    |- ?f ?x ?y = ?g ?a ?b
        => let X := fresh "arg1" in
        set (X := y); change b with X;
        clearbody X
    end.

    all : try match goal with
    |- regs_related
      (fun w : Word.word rv32RfIdx =>
      if weq w (ZToWord rv32RfIdx 0) then wzero 32 else ?krf w) ?rrf
      => revert H13; case TODO_joonwon
      end.

    all : cbn [AddrAligned getNextPc RiscvMachine.withNextPc RiscvMachine.withRegs evalBinBitBool].
    all : try subst val.
    all : try (eapply f_equal2; trivial; []).
    all : cbv [ZToReg MachineWidth_XLEN].

    all : try match goal with
    | |-  AddrAligned _     => case TODO_joonwon
    | |-  isXAddr4 _ _ -> pc_related _ _ _ => case TODO_joonwon
    end.

    all : eapply (@word.unsigned_inj _ (@word (@WordsKami width width_cases)) _).

    all: rewrite <-?ZToWord_Z_of_N.
    all : change (ZToWord 32) with (@word.of_Z 32 (@word (@WordsKami width width_cases))).
    all : rewrite ?word.unsigned_of_Z.

    1: { (* lui *)
      clear.
      match goal with
      | |- context[@word.unsigned ?a ?b ?x] =>
      change (@word.unsigned a b x) with (Z.of_N (wordToN x))
      end.
      rewrite wordToN_combine.
      change (wordToN (ZToWord 12 0) ) with 0%N.
      rewrite N.add_0_l.
      cbv [word.wrap].
      cbv [imm20].
      rewrite N2Z.inj_mul.
      change (Z.of_N (NatLib.Npow2 12)) with (2^12)%Z.
      rewrite unsigned_split2_as_bitSlice.
      t.
      change ((Z.of_nat 12)) with 12%Z.
      rewrite Z.shiftl_mul_pow2 by blia.
      cbv [kunsigned].
      change (12 + 20)%nat with 32%nat.
      change (Z.to_nat 32) with 32%nat.
      set (x := bitSlice (Z.of_N (@wordToN 32 kinst)) 12 32).
      change Utility.width with 32.
      cbv [signExtend].
      change (2 ^ (32 - 1)) with (2^31).
      rewrite Zminus_mod_idemp_l.
      replace (x * 2 ^ 12 + 2 ^ 31 - 2 ^ 31) with (x * 2 ^ 12) by blia.
      rewrite Z.mod_small; try ring.
      pose proof bitSlice_range_ex (Z.of_N (@wordToN 32 kinst)) 12 32.
      (* TODO remove once we advance to Coq 8.10 *)
      let t := (fun x => let r := eval cbv in x in change x with r in * ) in
      t (2 ^ (32 - 12)); t (2 ^ 32); t (2 ^ 12).
      blia. }

    1: { (* auipc *)
      cbv [pc_related] in H8.
      setoid_rewrite H8.
      clear.
      eapply f_equal.
      rewrite wplus_comm; eapply f_equal2.
      2:change (word.of_Z (@word.unsigned 32 (@word (@WordsKami width width_cases)) rpc) = rpc).
      2:eapply word.of_Z_unsigned.
      subst oimm20.
      rewrite (match TODO_andres with end :
        forall sz word x, @word.of_Z sz word (signExtend sz x) = @word.of_Z sz word x).
      eapply (@word.unsigned_inj _ (@word (@WordsKami width width_cases)) _).
      match goal with
      | |- context[@word.unsigned ?a ?b ?x] =>
      change (@word.unsigned a b x) with (Z.of_N (wordToN x))
      end.
      rewrite Z_of_wordToN_combine_alt.
      change (Z.of_N (wordToN (ZToWord 12 0))) with 0%Z.
      rewrite Z.lor_0_l.
      rewrite unsigned_split2_as_bitSlice.
      t.
      change (Z.of_nat 12) with 12.
      change (Z.of_N (N.of_nat 12)) with 12.
      rewrite word.unsigned_of_Z; cbv [word.wrap]; symmetry; eapply Z.mod_small.
      pose proof bitSlice_range_ex (Z.of_N (@wordToN 32 kinst)) 12 32 ltac:(blia).
      rewrite Z.shiftl_mul_pow2 by blia.
      change Utility.width with 32.
      change (12 + 20)%nat with 32%nat.
      change (2^32) with (2^(32-12) * 2^12).
      blia. }

    3: { (* addi *)
      subst imm12.
      clear.
      rewrite (match TODO_andres with end :
        forall sz x, @wordToZ sz x = signExtend (Z.of_nat sz) (Z.of_N (wordToN x))).
      rewrite unsigned_split2_as_bitSlice.
      change (Z.of_nat 20 + Z.of_nat 12) with 32.
      cbv [kunsigned].
      change (Z.of_nat 20) with 20.
      change (Z.of_nat 12) with 12.
      cbv [word.unsigned word WordsKami wordW KamiWord.word kunsigned].
      rewrite unsigned_wordToZ.
      trivial.
    }

    5: {
      subst imm12.
      clear.
      rewrite (match TODO_andres with end :
        forall sz x, @wordToZ sz x = signExtend (Z.of_nat sz) (Z.of_N (wordToN x))).
      rewrite unsigned_split2_as_bitSlice.
      change (Z.of_nat 20 + Z.of_nat 12) with 32.
      cbv [kunsigned].
      change (Z.of_nat 20) with 20.
      change (Z.of_nat 12) with 12.
      cbv [word.unsigned word WordsKami wordW KamiWord.word kunsigned].
      rewrite unsigned_wordToZ.
      trivial.
    }

    5: {
      subst imm12.
      clear.
      rewrite (match TODO_andres with end :
        forall sz x, @wordToZ sz x = signExtend (Z.of_nat sz) (Z.of_N (wordToN x))).
      rewrite unsigned_split2_as_bitSlice.
      change (Z.of_nat 20 + Z.of_nat 12) with 32.
      cbv [kunsigned].
      change (Z.of_nat 20) with 20.
      change (Z.of_nat 12) with 12.
      cbv [word.unsigned word WordsKami wordW KamiWord.word kunsigned].
      rewrite unsigned_wordToZ.
      trivial.
    }

    5: {
      subst imm12.
      clear.
      rewrite (match TODO_andres with end :
        forall sz x, @wordToZ sz x = signExtend (Z.of_nat sz) (Z.of_N (wordToN x))).
      rewrite unsigned_split2_as_bitSlice.
      change (Z.of_nat 20 + Z.of_nat 12) with 32.
      cbv [kunsigned].
      change (Z.of_nat 20) with 20.
      change (Z.of_nat 12) with 12.
      cbv [word.unsigned word WordsKami wordW KamiWord.word kunsigned].
      rewrite unsigned_wordToZ.
      trivial.
    }

    5: (* sll, difficult *)
      subst shamt6;  cbv [sll word.slu word WordsKami wordW KamiWord.word kunsigned].
    (*
word.unsigned (wlshift arg1 #(split2 20 5 (split1 (20 + 5) 7 kinst))) =
word.unsigned
  (kofZ
     (BinInt.Z.shiftl (BinInt.Z.of_N (wordToN arg1))
        (BinInt.Z.of_N
           (wordToN
              (word.of_Z
                 (machineIntToShamt
                    (bitSlice (BinInt.Z.of_N (wordToN kinst)) 20 26))))
         mod width)))
         *)
    all : clear H5.

    3: { (* slti *)
      clear H0 H2 H3 H4.
      match goal with |- context[wlt_dec ?w _] =>  change w with v end.
      refine (f_equal (fun b:bool => word.unsigned (if b then _ else _)) _).
      cbv [signed_less_than word.lts word WordsKami wordW KamiWord.word ksigned].
      rewrite (match TODO_andres with end : forall x y, (if wlt_dec x y then true else false)
        = Z.ltb (wordToZ x) (wordToZ y)); repeat f_equal.
      subst imm12.
      (* wordToZ (split2 20 12 kinst) = signExtend 12 (bitSlice (kunsigned kinst) 20 32) *)
      case TODO_kamiStep_instruction.
    }
    3: { (* sltiu *)
      clear H0 H2 H3 H4.
      match goal with |- context[wlt_dec ?w _] =>  change w with v end.
      refine (f_equal (fun b:bool => word.unsigned (if b then _ else _)) _).
      cbv [ltu word.ltu word WordsKami wordW KamiWord.word ksigned].
      case TODO_joonwon (*sign-extend imm12, but use unsigned comparision*).
    }

    all: case TODO_kamiStep_instruction.

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

    Unshelve.
    all : case TODO_kamiStep_instruction.

  (*A lot of*) Time Qed.

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
