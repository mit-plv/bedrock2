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

Local Axiom TODO_joonwon: False.
Local Axiom TODO_andres: False.

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

  Variable (instrMemSizeLg memSizeLg: Z).
  Hypotheses (Hinstr1: 3 <= instrMemSizeLg)
             (Hinstr2: instrMemSizeLg <= width - 2)
             (Hkmem1: 2 + instrMemSizeLg < memSizeLg)
             (Hkmem2: memSizeLg <= width).
  Local Notation Hinstr := (conj Hinstr1 Hinstr2).

  Variable (memInit: Vec (ConstT (Bit BitsPerByte)) (Z.to_nat memSizeLg)).
  Definition kamiMemInit := ConstVector memInit.
  Local Definition kamiProc :=
    @KamiProc.proc instrMemSizeLg memSizeLg Hinstr kamiMemInit kami_FE310_AbsMMIO.
  Local Definition kamiStMk := @KamiProc.mk (Z.to_nat width)
                                            (Z.to_nat memSizeLg)
                                            (Z.to_nat instrMemSizeLg)
                                            rv32InstBytes rv32DataBytes rv32RfIdx.
  Local Notation kamiXAddrs := (kamiXAddrs instrMemSizeLg).
  Local Notation rv32Fetch :=
    (rv32Fetch (Z.to_nat width)
               (Z.to_nat instrMemSizeLg)
               (width_inst_valid Hinstr)).
  Local Notation RiscvXAddrsSafe :=
    (RiscvXAddrsSafe instrMemSizeLg memSizeLg (conj Hinstr1 Hinstr2)).

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

  Definition pc_related_and_valid (kpc rpc: kword width) :=
    AddrAligned rpc /\ pc_related kpc rpc.

  Inductive states_related: KamiMachine * list Event -> RiscvMachine -> Prop :=
  | relate_states:
      forall t t' m riscvXAddrs kpc krf rrf rpc nrpc pinit instrMem kdataMem rdataMem metrics,
        traces_related t t' ->
        KamiProc.RegsToT m = Some (kamiStMk kpc krf pinit instrMem kdataMem) ->
        (pinit = false -> riscvXAddrs = kamiXAddrs) ->
        (pinit = true -> RiscvXAddrsSafe instrMem kdataMem riscvXAddrs) ->
        pc_related_and_valid kpc rpc ->
        nrpc = word.add rpc (word.of_Z 4) ->
        regs_related krf rrf ->
        mem_related _ kdataMem rdataMem ->
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
             then MMOutputEvent (argV Fin.F1) (argV (Fin.FS (Fin.FS (Fin.FS Fin.F1))))
             else MMInputEvent (argV Fin.F1) (retV Fin.F1)) ->
        KamiLabelR klbl [e].

  Definition kamiStep (m1 m2: KamiMachine) (klbl: Kami.Semantics.LabelT): Prop :=
    exists kupd, Step kamiProc m1 kupd klbl /\ m2 = FMap.M.union kupd m1.

  Ltac kami_step_case_empty :=
    left; FMap.mred; fail.

  Ltac eval_decode_in H :=
    cbv beta iota delta [decode] in H;
    repeat match goal with
           | [Hbs: bitSlice _ _ _ = _ |- _] => rewrite !Hbs in H; clear Hbs
           end;
    cbv [iset andb Z.gtb Z.eqb Pos.eqb BinInt.Z.of_nat Pos.of_succ_nat BinInt.Z.compare Pos.compare Pos.compare_cont Datatypes.length nth
         (* grep Definition ./deps/riscv-coq/src/riscv/Spec/Decode.v | cut -d' ' -f2 | sort | uniq | tr '\n' ' ' ; echo *)
         bitwidth decode FPRegister funct12_EBREAK funct12_ECALL funct12_MRET funct12_SRET funct12_URET funct12_WFI funct2_FMADD_S funct3_ADD funct3_ADDI funct3_ADDIW funct3_ADDW funct3_AMOD funct3_AMOW funct3_AND funct3_ANDI funct3_BEQ funct3_BGE funct3_BGEU funct3_BLT funct3_BLTU funct3_BNE funct3_CSRRC funct3_CSRRCI funct3_CSRRS funct3_CSRRSI funct3_CSRRW funct3_CSRRWI funct3_DIV funct3_DIVU funct3_DIVUW funct3_DIVW funct3_FCLASS_S funct3_FENCE funct3_FENCE_I funct3_FEQ_S funct3_FLE_S funct3_FLT_S funct3_FLW funct3_FMAX_S funct3_FMIN_S funct3_FMV_X_W funct3_FSGNJN_S funct3_FSGNJ_S funct3_FSGNJX_S funct3_FSW funct3_LB funct3_LBU funct3_LD funct3_LH funct3_LHU funct3_LW funct3_LWU funct3_MUL funct3_MULH funct3_MULHSU funct3_MULHU funct3_MULW funct3_OR funct3_ORI funct3_PRIV funct3_REM funct3_REMU funct3_REMUW funct3_REMW funct3_SB funct3_SD funct3_SH funct3_SLL funct3_SLLI funct3_SLLIW funct3_SLLW funct3_SLT funct3_SLTI funct3_SLTIU funct3_SLTU funct3_SRA funct3_SRAI funct3_SRAIW funct3_SRAW funct3_SRL funct3_SRLI funct3_SRLIW funct3_SRLW funct3_SUB funct3_SUBW funct3_SW funct3_XOR funct3_XORI funct5_AMOADD funct5_AMOAND funct5_AMOMAX funct5_AMOMAXU funct5_AMOMIN funct5_AMOMINU funct5_AMOOR funct5_AMOSWAP funct5_AMOXOR funct5_LR funct5_SC funct6_SLLI funct6_SRAI funct6_SRLI funct7_ADD funct7_ADDW funct7_AND funct7_DIV funct7_DIVU funct7_DIVUW funct7_DIVW funct7_FADD_S funct7_FCLASS_S funct7_FCVT_S_W funct7_FCVT_W_S funct7_FDIV_S funct7_FEQ_S funct7_FMIN_S funct7_FMUL_S funct7_FMV_W_X funct7_FMV_X_W funct7_FSGNJ_S funct7_FSQRT_S funct7_FSUB_S funct7_MUL funct7_MULH funct7_MULHSU funct7_MULHU funct7_MULW funct7_OR funct7_REM funct7_REMU funct7_REMUW funct7_REMW funct7_SFENCE_VMA funct7_SLL funct7_SLLIW funct7_SLLW funct7_SLT funct7_SLTU funct7_SRA funct7_SRAIW funct7_SRAW funct7_SRL funct7_SRLIW funct7_SRLW funct7_SUB funct7_SUBW funct7_XOR isValidA isValidA64 isValidCSR isValidF isValidF64 isValidI isValidI64 isValidM isValidM64 Opcode opcode_AMO opcode_AUIPC opcode_BRANCH opcode_JAL opcode_JALR opcode_LOAD opcode_LOAD_FP opcode_LUI opcode_MADD opcode_MISC_MEM opcode_MSUB opcode_NMADD opcode_NMSUB opcode_OP opcode_OP_32 opcode_OP_FP opcode_OP_IMM opcode_OP_IMM_32 opcode_STORE opcode_STORE_FP opcode_SYSTEM Register RoundMode rs2_FCVT_L_S rs2_FCVT_LU_S rs2_FCVT_W_S rs2_FCVT_WU_S supportsA supportsF supportsM] in H;
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
           (Hkinv: scmm_inv (Z.to_nat memSizeLg) rv32RfIdx rv32Fetch km1),
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
      RiscvXAddrsSafe pgmFull dataMem kamiXAddrs.
  Proof.
    unfold KamiPgmInitFull; intros.
    red; intros.
    split; [assumption|].
    intros.
    red in H2; subst kpc.
    rewrite H.
    cbv [alignInst rv32Fetch rv32AlignInst toAddr]; unfold evalExpr; fold evalExpr.
    f_equal.
    apply kamiXAddrs_isXAddr4_bound in H0.
    apply rv32ToAddr_rv32ToIAddr_consistent; assumption.
  Qed.

  Lemma kamiStep_sound_case_pgmInitEnd:
    forall km1 t0 rm1 post kupd cs
           (Hkinv: scmm_inv (Z.to_nat memSizeLg) rv32RfIdx rv32Fetch km1),
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
    progress
      (let ucode := match type of HR with mcomp_sat ?u ?s ?p => u end in
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
         (* Note:
            conversion is slow if we don't remember k.
            this might be because interp_fix needs to be unfolded once,
            but unfolding it as many times as possible would create a huge term
          *)
         let interp_action := eval cbv delta [interp_action MinimalMMIO.interp_action] in
         interp_action in
         let TR := eval cbn iota beta delta [
                     fst snd
                     getMetrics getMachine
                     translate
                     getRegs getPc getNextPc getMem getXAddrs getLog]
         in (interp_action a state (fun x state' => mcomp_sat (kV x) state' post)) in
             change TR in HR; subst kV
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
    | H: _ |- _ =>
      progress
        (cbv beta delta [load store] in H;
         cbn beta iota delta [
           load store fst snd translate
           withMetrics updateMetrics getMachine getMetrics getRegs getPc getNextPc getMem getXAddrs getLog withRegs withPc withNextPc withMem withXAddrs withLog withLogItem withLogItems
           RiscvMachine.withRegs RiscvMachine.withPc RiscvMachine.withNextPc RiscvMachine.withMem RiscvMachine.withXAddrs RiscvMachine.withLog RiscvMachine.withLogItem RiscvMachine.withLogItems] in H)
    | H: context CTX [@Memory.load_bytes ?a ?b ?c ?d ?e ?f ?g],
      G: context     [@Memory.load_bytes ?A ?B ?C ?D ?E ?F ?G] |- _ =>
      let HH := context CTX [@Memory.load_bytes A B C D E F G] in
      progress change HH in H
    end.

  Ltac prove_KamiLabelR :=
    split; [|split];
    [eapply KamiSilent; reflexivity| |eassumption].

  Context (Registers_ok : map.ok Registers).

  Lemma pc_related_plus4:
    forall kpc rpc,
      pc_related_and_valid kpc rpc ->
      pc_related_and_valid (kpc ^+ $4) (word.add rpc (word.of_Z 4)).
  Proof.
    cbv [pc_related_and_valid]; intros.
    destruct H; split.
    - apply AddrAligned_plus4; assumption.
    - red in H0; subst kpc.
      reflexivity.
  Qed.

  Lemma nat_power_of_two_boundary_shrink:
    forall n z,
      - BinInt.Z.of_nat (Nat.pow 2 n) <= z < BinInt.Z.of_nat (Nat.pow 2 n) ->
      forall m,
        (n < m)%nat ->
        - BinInt.Z.of_nat (Nat.pow 2 m) <= z < BinInt.Z.of_nat (Nat.pow 2 m).
  Proof.
    intros.
    destruct H; split.
    - etransitivity; [|eassumption].
      rewrite <-Z.opp_le_mono.
      apply inj_le.
      apply Nat.pow_le_mono_r; blia.
    - etransitivity; [eassumption|].
      apply inj_lt.
      apply Nat.pow_lt_mono_r; blia.
  Qed.

  Lemma AddrAligned_consistent:
    forall a,
      negb (reg_eqb (MachineWidth:= MachineWidth_XLEN)
                    (remu a (ZToReg 4)) (ZToReg 0)) = false ->
      AddrAligned a.
  Proof.
    intros.
    apply Bool.negb_false_iff in H.
    cbv [reg_eqb MachineWidth_XLEN word.eqb word WordsKami wordW KamiWord.word] in H.
    apply weqb_sound in H.
    cbv [remu word.modu riscvZmodu kofZ kunsigned] in H.
    simpl in H; cbn in H.
    change (Pos.to_nat 32) with 32%nat in H.
    match type of H with
    | _ = ?rhs =>
      change rhs with (wzero 32) in H;
        rewrite <-ZToWord_zero in H
    end.
    apply f_equal with (f:= @wordToZ _) in H.

    rewrite wordToZ_ZToWord in H.
    2: {
      apply nat_power_of_two_boundary_shrink with (n:= 3%nat); [simpl|blia].
      match goal with
      | |- _ <= ?z mod 4 < _ =>
        pose proof (Z.mod_bound_or z 4 ltac:(discriminate)); blia
      end.
    }
    rewrite wordToZ_ZToWord in H
      by (apply nat_power_of_two_boundary_shrink with (n:= 3%nat); simpl; blia).

    cbv [AddrAligned].
    apply wordToN_inj.
    apply N2Z.inj_iff.
    rewrite unsigned_split1_as_bitSlice.
    match goal with
    | |- context [@wordToN ?sz _] => change sz with 32%nat
    end.
    rewrite bitSlice_alt by blia.
    cbv [bitSlice']; cbn.
    rewrite Z.div_1_r.
    assumption.
  Qed.

  Lemma kami_evalZeroExtendTrunc_32:
    forall w, evalZeroExtendTrunc 32 w = w.
  Proof.
    intros; cbv [evalZeroExtendTrunc].
    destruct (lt_dec _ _); [Lia.lia|].
    apply split1_0.
  Qed.
    
  Lemma kami_evalSignExtendTrunc_32:
    forall w, evalSignExtendTrunc 32 w = w.
  Proof.
    intros; cbv [evalSignExtendTrunc].
    destruct (lt_dec _ _); [Lia.lia|].
    apply split1_0.
  Qed.

  Lemma kami_evalSignExtendTrunc:
    forall {a} (w: Word.word a) b,
      (a < b)%nat ->
      evalSignExtendTrunc b w =
      ZToWord b (signExtend (Z.of_nat a) (Z.of_N (wordToN w))).
  Proof.
    intros.
    cbv [evalSignExtendTrunc].
    destruct (lt_dec _ _); [|exfalso; auto].
    apply wordToZ_inj.
    rewrite wordToZ_eq_rect.
    rewrite sext_wordToZ.
    case TODO_joonwon.
  Qed.

  Ltac regs_get_red_goal :=
    repeat
      (try (erewrite <-regs_related_get
              with (w:= split2 15 5 (split1 (15 + 5) 12 _));
            [|eauto; fail|eassumption|eapply unsigned_split2_split1_as_bitSlice; fail]);
       try (erewrite <-regs_related_get
              with (w:= split2 20 5 (split1 (20 + 5) 7 _));
            [|eauto; fail|eassumption|eapply unsigned_split2_split1_as_bitSlice; fail])).

  Ltac regs_get_red H :=
    repeat
      (try (erewrite <-regs_related_get
              with (w:= split2 15 5 (split1 (15 + 5) 12 _)) in H;
            [|eauto; fail|eassumption|eapply unsigned_split2_split1_as_bitSlice; fail]);
       try (erewrite <-regs_related_get
              with (w:= split2 20 5 (split1 (20 + 5) 7 _)) in H;
            [|eauto; fail|eassumption|eapply unsigned_split2_split1_as_bitSlice; fail])).
  
  Ltac prove_states_related :=
    econstructor;
    [ solve [trivial]
    | clear; cbv [RegsToT pRegsToT]; kregmap_red; exact eq_refl
    | clear; intro; discriminate
    | solve [trivial]
    | cbv [RiscvMachine.getNextPc];
      try (eapply pc_related_plus4; try eassumption; red; eauto; fail)
    | solve [trivial]
    | try (eapply regs_related_put;
           [ solve [trivial] | solve [trivial] | | ];
           erewrite ?regs_related_get,
           ?unsigned_split2_split1_as_bitSlice
             by eauto;
           trivial)
    | solve [trivial]
    ].

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
        | [H: scmm_inv _ _ _ _ |- _] => inversion H
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

  Ltac kami_cbn_all :=
    cbn [evalExpr evalUniBool evalBinBool evalBinBit
                  evalConstT getDefaultConst isEq Data BitsPerByte Nat.add Nat.sub
                  AlignInstT DstE DstK DstT ExecT f3Lb f3Lbu f3Lh f3Lhu f3Lw getFunct3E getFunct6E getFunct7E getOffsetIE getOffsetSBE getOffsetSE getOffsetShamtE getHiShamtE getOffsetUE getOffsetUJE getOpcodeE getRdE getRs1E getRs1ValueE getRs2E getRs2ValueE IsMMIOE IsMMIOT LdAddrCalcT LdAddrE LdAddrK LdAddrT LdDstE LdDstK LdDstT LdSrcE LdSrcK LdSrcT LdTypeE LdTypeK LdTypeT LdValCalcT MemInit memInst memOp mm mmioExec nextPc NextPcT OpcodeE OpcodeK OpcodeT opLd opNm opSt OptypeE OptypeK OptypeT Pc pinst procInitDefault procInst RqFromProc RsToProc rv32AlignInst rv32CalcLdAddr rv32CalcLdVal rv32CalcStAddr rv32CalcStByteEn rv32DataBytes rv32GetDst rv32GetLdAddr rv32GetLdDst rv32GetLdSrc rv32GetLdType rv32GetOptype rv32GetSrc1 rv32GetSrc2 rv32GetStAddr rv32GetStSrc rv32GetStVSrc rv32InstBytes rv32RfIdx scmm Src1E Src1K Src1T Src2E Src2K Src2T StAddrCalcT StByteEnCalcT StAddrE StAddrK StAddrT StateE StateK StateT StSrcE StSrcK StSrcT StVSrcE StVSrcK StVSrcT] in *.
  
  Ltac kami_cbn_hint H func :=
    let t := type of H in
    let tc :=
      eval cbn [evalExpr evalUniBool evalBinBool evalBinBit
                evalConstT getDefaultConst isEq Data BitsPerByte Nat.add Nat.sub
                func
                (* grep -oP 'Definition \w+' ~/plv/bedrock2/deps/kami/Kami/Ex/{IsaRv32.v,SC.v} | cut -d' ' -f2 | sort | uniq | tr '\n' ' ' ; printf '\n' *)
                AlignInstT DstE DstK DstT ExecT f3Lb f3Lbu f3Lh f3Lhu f3Lw getFunct3E getFunct6E getFunct7E getOffsetIE getOffsetSBE getOffsetSE getOffsetShamtE getHiShamtE getOffsetUE getOffsetUJE getOpcodeE getRdE getRs1E getRs1ValueE getRs2E getRs2ValueE IsMMIOE IsMMIOT LdAddrCalcT LdAddrE LdAddrK LdAddrT LdDstE LdDstK LdDstT LdSrcE LdSrcK LdSrcT LdTypeE LdTypeK LdTypeT LdValCalcT MemInit memInst memOp mm mmioExec nextPc NextPcT OpcodeE OpcodeK OpcodeT opLd opNm opSt OptypeE OptypeK OptypeT Pc pinst procInitDefault procInst RqFromProc RsToProc rv32AlignInst rv32CalcLdAddr rv32CalcLdVal rv32CalcStAddr rv32CalcStByteEn rv32DataBytes rv32GetDst rv32GetLdAddr rv32GetLdDst rv32GetLdSrc rv32GetLdType rv32GetOptype rv32GetSrc1 rv32GetSrc2 rv32GetStAddr rv32GetStSrc rv32GetStVSrc rv32InstBytes rv32RfIdx scmm Src1E Src1K Src1T Src2E Src2K Src2T StAddrCalcT StByteEnCalcT StAddrE StAddrK StAddrT StateE StateK StateT StSrcE StSrcK StSrcT StVSrcE StVSrcK StVSrcT]
    in t in
    let Ht := fresh "H" in
    assert (Ht: t = tc) by reflexivity;
    rewrite Ht in H; clear Ht.

  Lemma kamiStep_sound_case_execLd:
    forall km1 t0 rm1 post kupd cs
           (Hkinv: scmm_inv (Z.to_nat memSizeLg) rv32RfIdx rv32Fetch km1),
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
    rewrite <-H3 in *.

    destruct (evalExpr (isMMIO type ldAddr)) eqn:Hmmio.
    - (** MMIO load case *)
      repeat match goal with
             | [H: true = true -> _ |- _] => specialize (H eq_refl)
             | [H: true = false -> _ |- _] => clear H
             end.
      destruct H11 as (kt2 & mmioLdRq & mmioLdRs & ? & ? & ? & ? & ?).
      simpl in H; subst cs.

      (** Invert a riscv-coq step *)

      (* -- fetch *)
      repeat t.
      specialize (H eq_refl).
      destruct H8.
      pose proof H as Hxaddr.
      eapply fetch_ok in H; try eassumption; [|Lia.lia].
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

      { (** LB: load-byte *)
        eval_decode_in H0.
        repeat t.
        case TODO_joonwon.
      }

      { (** LH: load-half *)
        case TODO_joonwon.
      }
      
      { (** LW: load-word *)
        case TODO_joonwon.
      }

      { (** LHU: load-half-unsigned *)
        case TODO_joonwon.
      }
      
      { (** LBU: load-byte-unsigned *)
        case TODO_joonwon.
      }

    - case TODO_joonwon.

  Qed.

  Local Axiom TODO_word : False.

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
      destruct H11.
      pose proof H1 as Hxaddr.
      eapply fetch_ok in H1; try eassumption; [|Lia.lia].
      destruct H1 as (rinst & ? & ?).
      rewrite H1 in H5.
      repeat t.
      setoid_rewrite H9 in H5.

      (** Begin symbolic evaluation of kami code *)
      kami_cbn_all.

      (* -- pick the subterm for the Kami instruction *)
      match goal with
      | [H: context [instrMem ?ipc] |- _] => set (kinst:= instrMem ipc)
      end.
      repeat
        match goal with
        | [H: context [instrMem ?ipc] |- _] => change (instrMem ipc) with kinst in H
        end.
      clearbody kinst.

      (* -- pick the execution function for simplification *)
      match goal with
      | [H: context [@evalExpr ?fk (rv32DoExec ?sz ?ty ?rs1 ?rs2 ?pc ?inst)] |- _] =>
        remember (@evalExpr fk (rv32DoExec sz ty rs1 rs2 pc inst)) as execVal
      end.
      kami_cbn_hint HeqexecVal rv32DoExec.
      
      (* -- pick the nextPc function *)
      match goal with
      | [H: context [@evalExpr ?fk (rv32NextPc ?sz ?ty ?rf ?pc ?inst)] |- _] =>
        remember (@evalExpr fk (rv32NextPc sz ty rf pc inst)) as npc
      end.
      kami_cbn_hint Heqnpc rv32NextPc.

      (* -- convert [weq] to [Z.eqb] in Kami decoding/execution *)
      (** Heads-up: COQBUG(rewrite pattern matching on if/match is broken
       * due to "hidden branch types") *)
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
      cbv [bool_rect] in *.

      (* -- some more word-to-Z conversions *)
      progress
        repeat (match goal with
                | [H: context G [Z.of_N (@wordToN ?n ?x)] |- _] =>
                  let nn := eval cbv in (Z.of_nat n) in
                      let e := context G [@kunsigned nn x] in
                      change e in H
                | [H: context G [kunsigned (@natToWord ?n ?x)] |- _] =>
                  let xx := eval cbv in (Z.of_nat x) in
                      let e := context G [xx] in
                      change e in H
                | [H: context G [kunsigned (@WS ?b ?n ?t)] |- _] =>
                  let xx := eval cbv in (kunsigned (width:= Z.of_nat (S n)) (WS b t)) in
                      let e := context G [xx] in
                      change e in H
                end).
 
      (* -- separate out cases of Kami execution *)
      idtac "kamiStep_sound: separate out cases of Kami execution".
      Timeout
        300
        (progress
           repeat match goal with
                  | [H : context G [if Z.eqb ?x ?y then ?a else ?b] |- _] =>
                    destruct (Z.eqb_spec x y) in *
                  | [H : context G [if (Z.eqb ?x ?y && _ && _)%bool then _ else _] |- _] =>
                    destruct (Z.eqb_spec x y)
                  | [H : context G [if (_ && Z.eqb ?x ?y && _)%bool then _ else _] |- _] =>
                    destruct (Z.eqb_spec x y)
                  | [H : context G [if (_ && _ && Z.eqb ?x ?y)%bool then _ else _] |- _] =>
                    destruct (Z.eqb_spec x y)
                  | [H: ?x = ?a, G: ?x = ?b |- _] =>
                    let aa := eval cbv (* delta [a] *) in a in
                    let bb := eval cbv (* delta [b] *) in b in
                    let t := isZcst aa in constr_eq t true;
                    let t := isZcst bb in constr_eq t true;
                    assert_fails (constr_eq aa bb);
                    exfalso; remember x; clear -H G;
                    cbv in H; cbv in G; rewrite H in G; inversion G
                  | [H: ?x = ?a, G: ?x <> ?b |- _] =>
                    let aa := eval cbv (* delta [a] *) in a in
                    let bb := eval cbv (* delta [b] *) in b in
                    let t := isZcst aa in constr_eq t true;
                    let t := isZcst bb in constr_eq t true;
                    assert_fails (constr_eq aa bb);
                    clear G
                  end).

      (* -- filter out load/store/branch instructions (not handled by [execNm]) *)
      all: try match goal with
               | [H: negb (kunsigned $0 =? 0) = true |- _] => exfalso; clear -H; discriminate
               | [H: (kunsigned opLd =? _) = true |- _] => exfalso; clear -H; discriminate
               | [H: (kunsigned opSt =? _) = true |- _] => exfalso; clear -H; discriminate
               end.

      (* -- further simplification *)
      all: repeat match goal with
                  | [H: context [evalUniBit (ZeroExtendTrunc _ _) _] |- _] =>
                    cbv [evalUniBit] in H; rewrite kami_evalZeroExtendTrunc_32 in H
                  | [H: context [evalUniBit (SignExtendTrunc _ _) _] |- _] =>
                    cbv [evalUniBit] in H; rewrite kami_evalSignExtendTrunc_32 in H
                  end.
      all: cbv [evalUniBit] in *; (* would reveal proofs if not rewritten above *)
        cbv [kunsigned] in *;
        repeat match goal with
               | H: _ |- _ => progress rewrite ?unsigned_split2_split1_as_bitSlice, ?unsigned_split1_as_bitSlice, ?unsigned_split2_as_bitSlice in H
               end.
      all: repeat match goal with
                  | [H: context [evalSignExtendTrunc _ _] |- _] =>
                    rewrite kami_evalSignExtendTrunc in HeqexecVal by (simpl; Lia.lia)
                  end.

      all:
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
               end.

      (* -- unfold [decode] of riscv-coq *)
      all:
        let dec := fresh "dec" in
        let Hdec := fresh "Hdec" in
        match goal with
        | H : context[decode ?a ?b] |- _ => remember (decode a b) as dec eqn:Hdec in H
        end;
        cbv beta iota delta [decode] in Hdec;
        repeat
          match goal with
          | [Hbs: bitSlice _ _ _ = _ |- _] => rewrite !Hbs in Hdec
          end.

      1: idtac "kamiStep_sound: The next step is very slow, taking ~4 minutes".
      Time all:
        repeat
          (match goal with
           | _ => progress cbn iota beta delta
                           [iset andb
                                 Z.gtb Z.eqb Pos.eqb
                                 BinInt.Z.of_nat Pos.of_succ_nat
                                 BinInt.Z.compare Pos.compare Pos.compare_cont
                                 Datatypes.length nth

                                 (* grep Definition ./deps/riscv-coq/src/riscv/Spec/Decode.v | cut -d' ' -f2 | sort | uniq | tr '\n' ' ' ; echo *)
                                 bitwidth decode FPRegister funct12_EBREAK funct12_ECALL funct12_MRET funct12_SRET funct12_URET funct12_WFI funct2_FMADD_S funct3_ADD funct3_ADDI funct3_ADDIW funct3_ADDW funct3_AMOD funct3_AMOW funct3_AND funct3_ANDI funct3_BEQ funct3_BGE funct3_BGEU funct3_BLT funct3_BLTU funct3_BNE funct3_CSRRC funct3_CSRRCI funct3_CSRRS funct3_CSRRSI funct3_CSRRW funct3_CSRRWI funct3_DIV funct3_DIVU funct3_DIVUW funct3_DIVW funct3_FCLASS_S funct3_FENCE funct3_FENCE_I funct3_FEQ_S funct3_FLE_S funct3_FLT_S funct3_FLW funct3_FMAX_S funct3_FMIN_S funct3_FMV_X_W funct3_FSGNJN_S funct3_FSGNJ_S funct3_FSGNJX_S funct3_FSW funct3_LB funct3_LBU funct3_LD funct3_LH funct3_LHU funct3_LW funct3_LWU funct3_MUL funct3_MULH funct3_MULHSU funct3_MULHU funct3_MULW funct3_OR funct3_ORI funct3_PRIV funct3_REM funct3_REMU funct3_REMUW funct3_REMW funct3_SB funct3_SD funct3_SH funct3_SLL funct3_SLLI funct3_SLLIW funct3_SLLW funct3_SLT funct3_SLTI funct3_SLTIU funct3_SLTU funct3_SRA funct3_SRAI funct3_SRAIW funct3_SRAW funct3_SRL funct3_SRLI funct3_SRLIW funct3_SRLW funct3_SUB funct3_SUBW funct3_SW funct3_XOR funct3_XORI funct5_AMOADD funct5_AMOAND funct5_AMOMAX funct5_AMOMAXU funct5_AMOMIN funct5_AMOMINU funct5_AMOOR funct5_AMOSWAP funct5_AMOXOR funct5_LR funct5_SC funct6_SLLI funct6_SRAI funct6_SRLI funct7_ADD funct7_ADDW funct7_AND funct7_DIV funct7_DIVU funct7_DIVUW funct7_DIVW funct7_FADD_S funct7_FCLASS_S funct7_FCVT_S_W funct7_FCVT_W_S funct7_FDIV_S funct7_FEQ_S funct7_FMIN_S funct7_FMUL_S funct7_FMV_W_X funct7_FMV_X_W funct7_FSGNJ_S funct7_FSQRT_S funct7_FSUB_S funct7_MUL funct7_MULH funct7_MULHSU funct7_MULHU funct7_MULW funct7_OR funct7_REM funct7_REMU funct7_REMUW funct7_REMW funct7_SFENCE_VMA funct7_SLL funct7_SLLIW funct7_SLLW funct7_SLT funct7_SLTU funct7_SRA funct7_SRAIW funct7_SRAW funct7_SRL funct7_SRLIW funct7_SRLW funct7_SUB funct7_SUBW funct7_XOR isValidA isValidA64 isValidCSR isValidF isValidF64 isValidI isValidI64 isValidM isValidM64 Opcode opcode_AMO opcode_AUIPC opcode_BRANCH opcode_JAL opcode_JALR opcode_LOAD opcode_LOAD_FP opcode_LUI opcode_MADD opcode_MISC_MEM opcode_MSUB opcode_NMADD opcode_NMSUB opcode_OP opcode_OP_32 opcode_OP_FP opcode_OP_IMM opcode_OP_IMM_32 opcode_STORE opcode_STORE_FP opcode_SYSTEM Register RoundMode rs2_FCVT_L_S rs2_FCVT_LU_S rs2_FCVT_W_S rs2_FCVT_WU_S supportsA supportsF supportsM] in *
           | x := @nil _ |- _ => subst x
           | _ => t
           end).

      all: try subst opcode; try subst funct3; try subst funct6; try subst funct7;
        try subst shamtHi; try subst shamtHiTest.
      all: try cbn in decodeI.
      all: cbv [funct12_EBREAK funct12_ECALL funct12_MRET funct12_SRET funct12_URET funct12_WFI funct2_FMADD_S funct3_ADD funct3_ADDI funct3_ADDIW funct3_ADDW funct3_AMOD funct3_AMOW funct3_AND funct3_ANDI funct3_BEQ funct3_BGE funct3_BGEU funct3_BLT funct3_BLTU funct3_BNE funct3_CSRRC funct3_CSRRCI funct3_CSRRS funct3_CSRRSI funct3_CSRRW funct3_CSRRWI funct3_DIV funct3_DIVU funct3_DIVUW funct3_DIVW funct3_FCLASS_S funct3_FENCE funct3_FENCE_I funct3_FEQ_S funct3_FLE_S funct3_FLT_S funct3_FLW funct3_FMAX_S funct3_FMIN_S funct3_FMV_X_W funct3_FSGNJN_S funct3_FSGNJ_S funct3_FSGNJX_S funct3_FSW funct3_LB funct3_LBU funct3_LD funct3_LH funct3_LHU funct3_LW funct3_LWU funct3_MUL funct3_MULH funct3_MULHSU funct3_MULHU funct3_MULW funct3_OR funct3_ORI funct3_PRIV funct3_REM funct3_REMU funct3_REMUW funct3_REMW funct3_SB funct3_SD funct3_SH funct3_SLL funct3_SLLI funct3_SLLIW funct3_SLLW funct3_SLT funct3_SLTI funct3_SLTIU funct3_SLTU funct3_SRA funct3_SRAI funct3_SRAIW funct3_SRAW funct3_SRL funct3_SRLI funct3_SRLIW funct3_SRLW funct3_SUB funct3_SUBW funct3_SW funct3_XOR funct3_XORI funct5_AMOADD funct5_AMOAND funct5_AMOMAX funct5_AMOMAXU funct5_AMOMIN funct5_AMOMINU funct5_AMOOR funct5_AMOSWAP funct5_AMOXOR funct5_LR funct5_SC funct6_SLLI funct6_SRAI funct6_SRLI funct7_ADD funct7_ADDW funct7_AND funct7_DIV funct7_DIVU funct7_DIVUW funct7_DIVW funct7_FADD_S funct7_FCLASS_S funct7_FCVT_S_W funct7_FCVT_W_S funct7_FDIV_S funct7_FEQ_S funct7_FMIN_S funct7_FMUL_S funct7_FMV_W_X funct7_FMV_X_W funct7_FSGNJ_S funct7_FSQRT_S funct7_FSUB_S funct7_MUL funct7_MULH funct7_MULHSU funct7_MULHU funct7_MULW funct7_OR funct7_REM funct7_REMU funct7_REMUW funct7_REMW funct7_SFENCE_VMA funct7_SLL funct7_SLLIW funct7_SLLW funct7_SLT funct7_SLTU funct7_SRA funct7_SRAIW funct7_SRAW funct7_SRL funct7_SRLIW funct7_SRLW funct7_SUB funct7_SUBW funct7_XOR isValidA isValidA64 isValidCSR isValidF isValidF64 isValidI isValidI64 isValidM isValidM64 Opcode opcode_AMO opcode_AUIPC opcode_BRANCH opcode_JAL opcode_JALR opcode_LOAD opcode_LOAD_FP opcode_LUI opcode_MADD opcode_MISC_MEM opcode_MSUB opcode_NMADD opcode_NMSUB opcode_OP opcode_OP_32 opcode_OP_FP opcode_OP_IMM opcode_OP_IMM_32 opcode_STORE opcode_STORE_FP opcode_SYSTEM Register RoundMode rs2_FCVT_L_S rs2_FCVT_LU_S rs2_FCVT_W_S rs2_FCVT_WU_S supportsA supportsF supportsM] in *;
        repeat match goal with
               | [v := context [Z.eqb ?x ?y], H: ?x <> ?y |- _] =>
                 destruct (Z.eqb_spec x y) in *; [exfalso; auto; fail|cbn in v]
               end.
      all: try cbn in decodeI.

      (** Start the consistency proof for each instruction *)
      
      (* 42: fence instructions. Can draw [False] since [rd <> 0] in [execNm]. *)
      42: case TODO_joonwon.
      (* 41: mul/div instructions. Should be able to draw [False] *)
      41: case TODO_joonwon.

      (* 40: the case that require additional simplification
       * to draw [False] by [mcomp_step_in]. *)
      40: (subst decodeI decodeM resultI resultM results;
           repeat rewrite Bool.andb_false_r in Hdec; cbn in Hdec).

      (* -- evaluate the riscv-coq decoder/executer *)
      all: subst dec; mcomp_step_in H5;
        repeat match goal with
               | H : False |- _ => case H
               | H : Z |- _ => clear H
               | H : list Instruction |- _ => clear H
               | H : Instruction |- _ => clear H
               end.

      (** Heads-up: known proof automation issues *)
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
                  | context G [when ?b _] => destr b
                  | context G [if ?b then _ else _] => destr b
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
      all: try subst regs; try subst kupd.

      (** Proving simulation; solve trivial goals first *)

      all: prove_states_related.

      all: match goal with | H: pc_related ?kpc _ |- _ => red in H; subst kpc end.
      all: try reflexivity.

      (* -- remaining [pc_related] proofs *)

      { (* [pc_related_and_valid] for `JAL` *)
        subst newPC jimm20.
        split; [apply AddrAligned_consistent; assumption|].
        clear; red.
        cbv [Utility.add
               ZToReg MachineWidth_XLEN
               word.add word WordsKami wordW KamiWord.word
               word.of_Z kofZ].

        repeat f_equal.
        rewrite kami_evalSignExtendTrunc by (simpl; Lia.lia).
        repeat f_equal.
        case TODO_word.
      }

      { (* [pc_related_and_valid] for `JALR` *)
        subst newPC oimm12 v rs1.
        split; [apply AddrAligned_consistent; assumption|red].
        cbv [Utility.add
               ZToReg MachineWidth_XLEN
               word.add word WordsKami wordW KamiWord.word
               word.of_Z kofZ].
        regs_get_red_goal.
        case TODO_word.
      }

      (* -- proof per an instruction execution *)
      all: try match goal with
               | [H: _ {| getMachine := _ |} |- _] => clear H
               end.
      all: try subst val; cbv [ZToReg MachineWidth_XLEN]; cbn [evalBinBitBool].
      all: eapply (@word.unsigned_inj _ (@word (@WordsKami width width_cases)) _).
      all: rewrite <-?ZToWord_Z_of_N.
      all: change (ZToWord 32) with (@word.of_Z 32 (@word (@WordsKami width width_cases))).
      all: rewrite ?word.unsigned_of_Z.

      (* -- below solves 6 subgoals for {addi, slti, sltiu, xori, ori, andi} *)
      all: try (subst v imm12 rs1;
                regs_get_red_goal;
                rewrite unsigned_split2_as_bitSlice;
                reflexivity).
      
      { (* lui *)
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
        blia.
      }

      { (* auipc *)
        clear.
        subst oimm20.
        unfold Utility.add.
        eapply f_equal.
        rewrite wplus_comm; eapply f_equal2; [|reflexivity].
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
        blia.
      }

      { (* slli *)
        subst v shamt6 rs1.
        regs_get_red_goal.
        clear -e2.
        cbv [machineIntToShamt id].
        match goal with
        | [ |- context [bitSlice ?w ?a ?b] ] =>
          replace (bitSlice w a b)
            with (Z.of_N (wordToN (split2 20 5 (split1 (20 + 5) 7 kinst))))
            by case TODO_word
        end.
        case TODO_word. (* consistency between `wlshift` and `sll` *)
      }

      { (* srli *)
        subst v shamt6 rs1.
        regs_get_red_goal.
        clear -e2.
        cbv [machineIntToShamt id].
        match goal with
        | [ |- context [bitSlice ?w ?a ?b] ] =>
          replace (bitSlice w a b)
            with (Z.of_N (wordToN (split2 20 5 (split1 (20 + 5) 7 kinst))))
            by case TODO_word
        end.
        case TODO_word. (* consistency between `wrshift` and `srl` *)
      }

      { (* srai *)
        subst v shamt6 rs1.
        regs_get_red_goal.
        clear -e2.
        cbv [machineIntToShamt id].
        match goal with
        | [ |- context [bitSlice ?w ?a ?b] ] =>
          replace (bitSlice w a b)
            with (Z.of_N (wordToN (split2 20 5 (split1 (20 + 5) 7 kinst))))
            by case TODO_word
        end.
        case TODO_word. (* consistency between `wrshifta` and `sra` *)
      }

      { (* sll *)
        subst v v0 rs1 rs2.
        regs_get_red_goal.
        cbv [regToShamt].
        case TODO_word. (* consistency between `wlshift` and `sll` *)
      }

      { (* srl *)
        subst v v0 rs1 rs2.
        regs_get_red_goal.
        cbv [regToShamt].
        case TODO_word. (* consistency between `wrshift` and `srl` *)
      }

      { (* sra *)
        subst v v0 rs1 rs2.
        regs_get_red_goal.
        cbv [regToShamt].
        case TODO_word. (* consistency between `wrshifta` and `sra` *)
      }

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
      destruct H11.
      eapply fetch_ok in H1; try eassumption; [|Lia.lia].
      destruct H1 as (rinst & ? & ?).
      rewrite H1 in H5.
      repeat t.
      setoid_rewrite H9 in H5.

      (** Begin symbolic evaluation of kami code *)
      kami_cbn_all.

      (* -- pick the subterm for the Kami instruction *)
      match goal with
      | [H: context [instrMem ?ipc] |- _] => set (kinst:= instrMem ipc)
      end.
      repeat
        match goal with
        | [H: context [instrMem ?ipc] |- _] => change (instrMem ipc) with kinst in H
        end.
      clearbody kinst.

      (* -- [execNmZ] does no execution; just pick the nextPc function *)
      match goal with
      | [H: context [@evalExpr ?fk (rv32NextPc ?sz ?ty ?rf ?pc ?inst)] |- _] =>
        remember (@evalExpr fk (rv32NextPc sz ty rf pc inst)) as npc
      end.
      kami_cbn_hint Heqnpc rv32NextPc.

      (* -- convert [weq] to [Z.eqb] in Kami decoding/execution *)
      (** Heads-up: COQBUG(rewrite pattern matching on if/match is broken
       * due to "hidden branch types") *)
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
      cbv [bool_rect] in *.

      (* -- some more word-to-Z conversions *)
      progress
        repeat (match goal with
                | [H: context G [Z.of_N (@wordToN ?n ?x)] |- _] =>
                  let nn := eval cbv in (Z.of_nat n) in
                      let e := context G [@kunsigned nn x] in
                      change e in H
                | [H: context G [kunsigned (@natToWord ?n ?x)] |- _] =>
                  let xx := eval cbv in (Z.of_nat x) in
                      let e := context G [xx] in
                      change e in H
                | [H: context G [kunsigned (@WS ?b ?n ?t)] |- _] =>
                  let xx := eval cbv in (kunsigned (width:= Z.of_nat (S n)) (WS b t)) in
                      let e := context G [xx] in
                      change e in H
                end).
 
      (* -- separate out cases of Kami execution *)
      idtac "kamiStep_sound: separate out cases of Kami execution".
      Timeout
        300
        (progress
           repeat match goal with
                  | [H : context G [if Z.eqb ?x ?y then ?a else ?b] |- _] =>
                    destruct (Z.eqb_spec x y) in *
                  | [H : context G [if (Z.eqb ?x ?y && _ && _)%bool then _ else _] |- _] =>
                    destruct (Z.eqb_spec x y)
                  | [H : context G [if (_ && Z.eqb ?x ?y && _)%bool then _ else _] |- _] =>
                    destruct (Z.eqb_spec x y)
                  | [H : context G [if (_ && _ && Z.eqb ?x ?y)%bool then _ else _] |- _] =>
                    destruct (Z.eqb_spec x y)
                  | [H: ?x = ?a, G: ?x = ?b |- _] =>
                    let aa := eval cbv (* delta [a] *) in a in
                    let bb := eval cbv (* delta [b] *) in b in
                    let t := isZcst aa in constr_eq t true;
                    let t := isZcst bb in constr_eq t true;
                    assert_fails (constr_eq aa bb);
                    exfalso; remember x; clear -H G;
                    cbv in H; cbv in G; rewrite H in G; inversion G
                  | [H: ?x = ?a, G: ?x <> ?b |- _] =>
                    let aa := eval cbv (* delta [a] *) in a in
                    let bb := eval cbv (* delta [b] *) in b in
                    let t := isZcst aa in constr_eq t true;
                    let t := isZcst bb in constr_eq t true;
                    assert_fails (constr_eq aa bb);
                    clear G
                  end).

      (* -- filter out load/store instructions (not handled by [execNm]) *)
      all: try match goal with
               | [H: (kunsigned opLd =? _) = true |- _] => exfalso; clear -H; discriminate
               | [H: (kunsigned opSt =? _) = true |- _] => exfalso; clear -H; discriminate
               end.

      (* -- further simplification *)
      all: repeat match goal with
                  | [H: context [evalUniBit (ZeroExtendTrunc _ _) _] |- _] =>
                    cbv [evalUniBit] in H; rewrite kami_evalZeroExtendTrunc_32 in H
                  | [H: context [evalUniBit (SignExtendTrunc _ _) _] |- _] =>
                    cbv [evalUniBit] in H; rewrite kami_evalSignExtendTrunc_32 in H
                  end.
      all: cbv [evalUniBit] in *; (* would reveal proofs if not rewritten above *)
        cbv [kunsigned] in *;
        repeat match goal with
               | H: _ |- _ => progress rewrite ?unsigned_split2_split1_as_bitSlice, ?unsigned_split1_as_bitSlice, ?unsigned_split2_as_bitSlice in H
               end.
      all: repeat match goal with
                  | [H: context [evalSignExtendTrunc _ _] |- _] =>
                    rewrite kami_evalSignExtendTrunc in HeqexecVal by (simpl; Lia.lia)
                  end.

      all:
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
               end.

      (* -- unfold [decode] of riscv-coq *)
      all:
        let dec := fresh "dec" in
        let Hdec := fresh "Hdec" in
        match goal with
        | H : context[decode ?a ?b] |- _ => remember (decode a b) as dec eqn:Hdec in H
        end;
        cbv beta iota delta [decode] in Hdec;
        repeat
          match goal with
          | [Hbs: bitSlice _ _ _ = _ |- _] => rewrite !Hbs in Hdec
          end.

      1: idtac "kamiStep_sound: The next step is very slow, taking ~4 minutes".
      Time all:
        repeat
          (match goal with
           | _ => progress cbn iota beta delta
                           [iset andb
                                 Z.gtb Z.eqb Pos.eqb
                                 BinInt.Z.of_nat Pos.of_succ_nat
                                 BinInt.Z.compare Pos.compare Pos.compare_cont
                                 Datatypes.length nth

                                 (* grep Definition ./deps/riscv-coq/src/riscv/Spec/Decode.v | cut -d' ' -f2 | sort | uniq | tr '\n' ' ' ; echo *)
                                 bitwidth decode FPRegister funct12_EBREAK funct12_ECALL funct12_MRET funct12_SRET funct12_URET funct12_WFI funct2_FMADD_S funct3_ADD funct3_ADDI funct3_ADDIW funct3_ADDW funct3_AMOD funct3_AMOW funct3_AND funct3_ANDI funct3_BEQ funct3_BGE funct3_BGEU funct3_BLT funct3_BLTU funct3_BNE funct3_CSRRC funct3_CSRRCI funct3_CSRRS funct3_CSRRSI funct3_CSRRW funct3_CSRRWI funct3_DIV funct3_DIVU funct3_DIVUW funct3_DIVW funct3_FCLASS_S funct3_FENCE funct3_FENCE_I funct3_FEQ_S funct3_FLE_S funct3_FLT_S funct3_FLW funct3_FMAX_S funct3_FMIN_S funct3_FMV_X_W funct3_FSGNJN_S funct3_FSGNJ_S funct3_FSGNJX_S funct3_FSW funct3_LB funct3_LBU funct3_LD funct3_LH funct3_LHU funct3_LW funct3_LWU funct3_MUL funct3_MULH funct3_MULHSU funct3_MULHU funct3_MULW funct3_OR funct3_ORI funct3_PRIV funct3_REM funct3_REMU funct3_REMUW funct3_REMW funct3_SB funct3_SD funct3_SH funct3_SLL funct3_SLLI funct3_SLLIW funct3_SLLW funct3_SLT funct3_SLTI funct3_SLTIU funct3_SLTU funct3_SRA funct3_SRAI funct3_SRAIW funct3_SRAW funct3_SRL funct3_SRLI funct3_SRLIW funct3_SRLW funct3_SUB funct3_SUBW funct3_SW funct3_XOR funct3_XORI funct5_AMOADD funct5_AMOAND funct5_AMOMAX funct5_AMOMAXU funct5_AMOMIN funct5_AMOMINU funct5_AMOOR funct5_AMOSWAP funct5_AMOXOR funct5_LR funct5_SC funct6_SLLI funct6_SRAI funct6_SRLI funct7_ADD funct7_ADDW funct7_AND funct7_DIV funct7_DIVU funct7_DIVUW funct7_DIVW funct7_FADD_S funct7_FCLASS_S funct7_FCVT_S_W funct7_FCVT_W_S funct7_FDIV_S funct7_FEQ_S funct7_FMIN_S funct7_FMUL_S funct7_FMV_W_X funct7_FMV_X_W funct7_FSGNJ_S funct7_FSQRT_S funct7_FSUB_S funct7_MUL funct7_MULH funct7_MULHSU funct7_MULHU funct7_MULW funct7_OR funct7_REM funct7_REMU funct7_REMUW funct7_REMW funct7_SFENCE_VMA funct7_SLL funct7_SLLIW funct7_SLLW funct7_SLT funct7_SLTU funct7_SRA funct7_SRAIW funct7_SRAW funct7_SRL funct7_SRLIW funct7_SRLW funct7_SUB funct7_SUBW funct7_XOR isValidA isValidA64 isValidCSR isValidF isValidF64 isValidI isValidI64 isValidM isValidM64 Opcode opcode_AMO opcode_AUIPC opcode_BRANCH opcode_JAL opcode_JALR opcode_LOAD opcode_LOAD_FP opcode_LUI opcode_MADD opcode_MISC_MEM opcode_MSUB opcode_NMADD opcode_NMSUB opcode_OP opcode_OP_32 opcode_OP_FP opcode_OP_IMM opcode_OP_IMM_32 opcode_STORE opcode_STORE_FP opcode_SYSTEM Register RoundMode rs2_FCVT_L_S rs2_FCVT_LU_S rs2_FCVT_W_S rs2_FCVT_WU_S supportsA supportsF supportsM] in *
           | x := @nil _ |- _ => subst x
           | _ => t
           end).

      all: try subst opcode; try subst funct3; try subst funct6; try subst funct7;
        try subst shamtHi; try subst shamtHiTest.
      all: try cbn in decodeI.
      all: cbv [funct12_EBREAK funct12_ECALL funct12_MRET funct12_SRET funct12_URET funct12_WFI funct2_FMADD_S funct3_ADD funct3_ADDI funct3_ADDIW funct3_ADDW funct3_AMOD funct3_AMOW funct3_AND funct3_ANDI funct3_BEQ funct3_BGE funct3_BGEU funct3_BLT funct3_BLTU funct3_BNE funct3_CSRRC funct3_CSRRCI funct3_CSRRS funct3_CSRRSI funct3_CSRRW funct3_CSRRWI funct3_DIV funct3_DIVU funct3_DIVUW funct3_DIVW funct3_FCLASS_S funct3_FENCE funct3_FENCE_I funct3_FEQ_S funct3_FLE_S funct3_FLT_S funct3_FLW funct3_FMAX_S funct3_FMIN_S funct3_FMV_X_W funct3_FSGNJN_S funct3_FSGNJ_S funct3_FSGNJX_S funct3_FSW funct3_LB funct3_LBU funct3_LD funct3_LH funct3_LHU funct3_LW funct3_LWU funct3_MUL funct3_MULH funct3_MULHSU funct3_MULHU funct3_MULW funct3_OR funct3_ORI funct3_PRIV funct3_REM funct3_REMU funct3_REMUW funct3_REMW funct3_SB funct3_SD funct3_SH funct3_SLL funct3_SLLI funct3_SLLIW funct3_SLLW funct3_SLT funct3_SLTI funct3_SLTIU funct3_SLTU funct3_SRA funct3_SRAI funct3_SRAIW funct3_SRAW funct3_SRL funct3_SRLI funct3_SRLIW funct3_SRLW funct3_SUB funct3_SUBW funct3_SW funct3_XOR funct3_XORI funct5_AMOADD funct5_AMOAND funct5_AMOMAX funct5_AMOMAXU funct5_AMOMIN funct5_AMOMINU funct5_AMOOR funct5_AMOSWAP funct5_AMOXOR funct5_LR funct5_SC funct6_SLLI funct6_SRAI funct6_SRLI funct7_ADD funct7_ADDW funct7_AND funct7_DIV funct7_DIVU funct7_DIVUW funct7_DIVW funct7_FADD_S funct7_FCLASS_S funct7_FCVT_S_W funct7_FCVT_W_S funct7_FDIV_S funct7_FEQ_S funct7_FMIN_S funct7_FMUL_S funct7_FMV_W_X funct7_FMV_X_W funct7_FSGNJ_S funct7_FSQRT_S funct7_FSUB_S funct7_MUL funct7_MULH funct7_MULHSU funct7_MULHU funct7_MULW funct7_OR funct7_REM funct7_REMU funct7_REMUW funct7_REMW funct7_SFENCE_VMA funct7_SLL funct7_SLLIW funct7_SLLW funct7_SLT funct7_SLTU funct7_SRA funct7_SRAIW funct7_SRAW funct7_SRL funct7_SRLIW funct7_SRLW funct7_SUB funct7_SUBW funct7_XOR isValidA isValidA64 isValidCSR isValidF isValidF64 isValidI isValidI64 isValidM isValidM64 Opcode opcode_AMO opcode_AUIPC opcode_BRANCH opcode_JAL opcode_JALR opcode_LOAD opcode_LOAD_FP opcode_LUI opcode_MADD opcode_MISC_MEM opcode_MSUB opcode_NMADD opcode_NMSUB opcode_OP opcode_OP_32 opcode_OP_FP opcode_OP_IMM opcode_OP_IMM_32 opcode_STORE opcode_STORE_FP opcode_SYSTEM Register RoundMode rs2_FCVT_L_S rs2_FCVT_LU_S rs2_FCVT_W_S rs2_FCVT_WU_S supportsA supportsF supportsM] in *;
        repeat match goal with
               | [v := context [Z.eqb ?x ?y], H: ?x <> ?y |- _] =>
                 destruct (Z.eqb_spec x y) in *; [exfalso; auto; fail|cbn in v]
               end.
      all: try cbn in decodeI.

      (** Start the consistency proof for each instruction *)

      (* -- TODO @joonwonc: what is this case? *)
      11: case TODO_joonwon.
      
      (* -- evaluate the riscv-coq decoder/executer *)
      all: subst dec; mcomp_step_in H5;
        repeat match goal with
               | H : False |- _ => case H
               | H : Z |- _ => clear H
               | H : list Instruction |- _ => clear H
               | H : Instruction |- _ => clear H
               end.

      (** Heads-up: known proof automation issues *)
      (* TODO: we should not blast cases of riscv-coq when hypotheses tell us
       * which case kami took *)
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
      all: try subst regs; try subst kupd.

      (** Proving simulation; solve trivial goals first *)

      all: prove_states_related.
      all: match goal with | H: pc_related ?kpc _ |- _ => red in H; subst kpc end.

      (* -- TODO @joonwonc: instead of below [try assumption] for [regs_related],
       * FIX [prove_states_related] to cover this trivial case. *)
      all: try assumption.

      (* -- prove [regs_related] to write to r0 *)
      all: try match goal with
               | [rd := ?bs, Hbs: ?bs = 0 |- regs_related _ _] =>
                 subst rd; rewrite Hbs; assumption
               end.

      (* -- remaining [pc_related] proofs *)

      { (* jal *)
        subst newPC jimm20.
        split; [apply AddrAligned_consistent; assumption|].
        clear; red.
        cbv [Utility.add
               ZToReg MachineWidth_XLEN
               word.add word WordsKami wordW KamiWord.word
               word.of_Z kofZ].
        repeat f_equal.
        rewrite kami_evalSignExtendTrunc by (simpl; Lia.lia).
        repeat f_equal.
        case TODO_word.
      }

      { (* jalr *)
        subst newPC oimm12 v rs1.
        split; [apply AddrAligned_consistent; assumption|red].
        cbv [Utility.add
               ZToReg MachineWidth_XLEN
               word.add word WordsKami wordW KamiWord.word
               word.of_Z kofZ].
        regs_get_red_goal.
        case TODO_word.
      }

      { (* beq(eq) *)
        subst newPC sbimm12.
        split; [apply AddrAligned_consistent; assumption|].
        clear; red.
        cbv [Utility.add
               ZToReg MachineWidth_XLEN
               word.add word WordsKami wordW KamiWord.word
               word.of_Z kofZ].
        repeat f_equal.
        rewrite kami_evalSignExtendTrunc by (simpl; Lia.lia).
        repeat f_equal.
        case TODO_word.
      }
      
      { (* beq(eq-neq contradiction) *)
        exfalso; subst v v0 rs1 rs2.
        regs_get_red E.
        apply N2Z.inj, wordToN_inj in e1; auto.
      }
      
      { (* beq(eq-neq contradiction) *)
        exfalso; subst v v0 rs1 rs2.
        regs_get_red E; congruence.
      }

      { (* bne(neq) *)
        match goal with
        | [ |- context [Z.eqb ?x ?y] ] => destruct (Z.eqb_spec x y)
        end.
        { exfalso; subst v v0 rs1 rs2.
          regs_get_red E.
          cbv [reg_eqb MachineWidth_XLEN word.eqb word WordsKami wordW KamiWord.word] in E.
          apply weqb_false in E.
          apply N2Z.inj, wordToN_inj in e1; auto.
        }
        { cbv [negb].
          subst addr sbimm12.
          split; [apply AddrAligned_consistent; assumption|].
          clear; red.
          cbv [Utility.add
                 ZToReg MachineWidth_XLEN
                 word.add word WordsKami wordW KamiWord.word
                 word.of_Z kofZ].
          repeat f_equal.
          rewrite kami_evalSignExtendTrunc by (simpl; Lia.lia).
          repeat f_equal.
          case TODO_word.
        }
      }

      { (* bne(eq) *)
        match goal with
        | [ |- context [Z.eqb ?x ?y] ] => destruct (Z.eqb_spec x y)
        end.
        { apply pc_related_plus4; red; eauto. }
        { exfalso; subst v v0 rs1 rs2.
          regs_get_red E.
          cbv [reg_eqb MachineWidth_XLEN word.eqb word WordsKami wordW KamiWord.word] in E.
          apply Bool.negb_false_iff in E; apply weqb_sound in E.
          congruence.
        }
      }

      { (* blt(lt) *)
        cbv [evalBinBitBool].
        cbv [signed_less_than
               MachineWidth_XLEN
               word.lts word WordsKami wordW KamiWord.word] in E.
        subst v v0 rs1 rs2.
        regs_get_red E.
        destruct (wslt_dec _ _); [|discriminate].
        subst addr sbimm12.
        split; [apply AddrAligned_consistent; assumption|].
        clear; red.
        cbv [Utility.add
               ZToReg MachineWidth_XLEN
               word.add word WordsKami wordW KamiWord.word
               word.of_Z kofZ].
        repeat f_equal.
        rewrite kami_evalSignExtendTrunc by (simpl; Lia.lia).
        repeat f_equal.
        case TODO_word.
      }

      { (* blt(not lt) *)
        cbv [evalBinBitBool].
        cbv [signed_less_than
               MachineWidth_XLEN
               word.lts word WordsKami wordW KamiWord.word] in E.
        subst v v0 rs1 rs2.
        regs_get_red E.
        destruct (wslt_dec _ _); [discriminate|].
        apply pc_related_plus4; red; eauto.
      }

      { (* bge(ge) *)
        cbv [evalBinBitBool].
        cbv [signed_less_than
               MachineWidth_XLEN
               word.lts word WordsKami wordW KamiWord.word] in E.
        subst v v0 rs1 rs2.
        regs_get_red E.
        destruct (wslt_dec _ _); [discriminate|].
        subst addr sbimm12.
        split; [apply AddrAligned_consistent; assumption|].
        clear; red.
        cbv [Utility.add
               ZToReg MachineWidth_XLEN
               word.add word WordsKami wordW KamiWord.word
               word.of_Z kofZ].
        repeat f_equal.
        rewrite kami_evalSignExtendTrunc by (simpl; Lia.lia).
        repeat f_equal.
        case TODO_word.
      }

      { (* bge(not ge) *)
        cbv [evalBinBitBool].
        cbv [signed_less_than
               MachineWidth_XLEN
               word.lts word WordsKami wordW KamiWord.word] in E.
        subst v v0 rs1 rs2.
        regs_get_red E.
        destruct (wslt_dec _ _); [|discriminate].
        apply pc_related_plus4; red; eauto.
      }

      { (* bltu(ltu) *)
        cbv [evalBinBitBool].
        cbv [ltu MachineWidth_XLEN
                 word.ltu word WordsKami wordW KamiWord.word] in E.
        subst v v0 rs1 rs2.
        regs_get_red E.
        destruct (wlt_dec _ _); [|discriminate].
        subst addr sbimm12.
        split; [apply AddrAligned_consistent; assumption|].
        clear; red.
        cbv [Utility.add
               ZToReg MachineWidth_XLEN
               word.add word WordsKami wordW KamiWord.word
               word.of_Z kofZ].
        repeat f_equal.
        rewrite kami_evalSignExtendTrunc by (simpl; Lia.lia).
        repeat f_equal.
        case TODO_word.
      }

      { (* bltu(not ltu) *)
        cbv [evalBinBitBool].
        cbv [ltu MachineWidth_XLEN
                 word.ltu word WordsKami wordW KamiWord.word] in E.
        subst v v0 rs1 rs2.
        regs_get_red E.
        destruct (wlt_dec _ _); [discriminate|].
        apply pc_related_plus4; red; eauto.
      }

      { (* bgeu(geu) *)
        cbv [evalBinBitBool].
        cbv [ltu MachineWidth_XLEN
                 word.ltu word WordsKami wordW KamiWord.word] in E.
        subst v v0 rs1 rs2.
        regs_get_red E.
        destruct (wlt_dec _ _); [discriminate|].
        subst addr sbimm12.
        split; [apply AddrAligned_consistent; assumption|].
        clear; red.
        cbv [Utility.add
               ZToReg MachineWidth_XLEN
               word.add word WordsKami wordW KamiWord.word
               word.of_Z kofZ].
        repeat f_equal.
        rewrite kami_evalSignExtendTrunc by (simpl; Lia.lia).
        repeat f_equal.
        case TODO_word.
      }

      { (* bgeu(not geu) *)
        cbv [evalBinBitBool].
        cbv [ltu MachineWidth_XLEN
                 word.ltu word WordsKami wordW KamiWord.word] in E.
        subst v v0 rs1 rs2.
        regs_get_red E.
        destruct (wlt_dec _ _); [|discriminate].
        apply pc_related_plus4; red; eauto.
      }

      all: idtac "kamiStep_sound: starting the Qed...".
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

  Definition mm: Modules := Kami.Ex.SC.mm
                              (existT _ rv32DataBytes eq_refl)
                              kamiMemInit kami_FE310_AbsMMIO.
  Definition p4mm: Modules := p4mm Hinstr kamiMemInit kami_FE310_AbsMMIO.

  Definition riscvRegsInit:
    {rrfi: Registers & regs_related (evalConstT (rfInit procInit)) rrfi}.
  Proof.
    case TODO_joonwon.
  Defined.

  Definition riscvMemInit := map.of_list (List.map
    (fun i : nat =>
      (word.of_Z (Z.of_nat i),
       byte.of_Z (uwordToZ (evalConstT kamiMemInit $i))))
    (seq 0 (2 ^ Z.to_nat memSizeLg))).
  Lemma mem_related_riscvMemInit : mem_related _ (evalConstT kamiMemInit) riscvMemInit.
  Proof.
    assert (map.ok mem) by case TODO_joonwon.
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
           {| RiscvMachine.getRegs := projT1 riscvRegsInit;
              RiscvMachine.getPc := word.of_Z 0;
              RiscvMachine.getNextPc := word.of_Z 4;
              RiscvMachine.getMem := riscvMemInit;
              RiscvMachine.getXAddrs := kamiXAddrs;
              RiscvMachine.getLog := nil; (* <-- intended to be nil *) |};
         getMetrics := MetricLogging.EmptyMetricLog; |}.
  Proof.
    econstructor; try reflexivity.
    2: eapply pRegsToT_init.
    - econstructor.
    - intros; discriminate.
    - split; reflexivity.
    - apply (projT2 riscvRegsInit).
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
