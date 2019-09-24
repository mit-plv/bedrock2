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
Require Import riscv.Utility.MMIOTrace.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MinimalMMIO.
Require Import riscv.Platform.MetricMinimalMMIO.

Require Import Kami.Syntax Kami.Semantics Kami.Tactics.
Require Import Kami.Ex.MemTypes Kami.Ex.SC Kami.Ex.SCMMInl Kami.Ex.SCMMInv.
Require Import Kami.Ex.IsaRv32.

Require Import processor.KamiProc.
Require Import processor.FetchOk processor.DecExecOk.

Local Open Scope Z_scope.

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

Instance KamiWordsInst: Utility.Words := @KamiWord.WordsKami width width_cases.

Section Equiv.
  (* TODO not sure if we want to use ` or rather a parameter record *)
  Context {Registers: map.map Register word}
          {mem: map.map word byte}
          {mmio_semantics : ExtSpec}.

  Local Notation M := (free action result).
  Local Notation RiscvMachine := (@MetricRiscvMachine KamiWordsInst Registers mem).
  Local Existing Instance MetricMinimalMMIO.IsRiscvMachine.
  Local Existing Instance MetricMinimalMMIOSatisfiesPrimitives.

  (** * Processor, software machine, and states *)

  Variable (instrMemSizeLg: Z).
  Hypotheses (Hinstr1: 3 <= instrMemSizeLg)
             (Hinstr2: instrMemSizeLg <= width - 2).

  Variables (prg: kword instrMemSizeLg -> kword 32)
            (otherMemInit: mem).
  Definition memInit: MemInit (Z.to_nat width) 4%nat.
    pose prg.
    pose otherMemInit.
    case TODO. (* TODO @joonwonc: define using [prg] and [otherMemInit] *)
  Defined.

  Local Definition kamiProc := @KamiProc.proc instrMemSizeLg memInit.
  Local Definition KamiMachine := KamiProc.hst.
  Local Definition KamiSt := @KamiProc.st instrMemSizeLg.
  Local Notation kamiXAddrs := (kamiXAddrs instrMemSizeLg).
  Local Notation toKamiPc := (toKamiPc instrMemSizeLg).
  Local Notation convertDataMem := (@convertDataMem mem).
  Local Definition kamiStMk :=
    @KamiProc.mk (Z.to_nat width)
                 (Z.to_nat instrMemSizeLg)
                 rv32InstBytes rv32DataBytes rv32RfIdx.

  Definition iset: InstructionSet := RV32IM.

  (** * The Observable Behavior: MMIO events *)

  Definition signedByteTupleToReg{n: nat}(v: HList.tuple byte n): word :=
    word.of_Z (BitOps.signExtend (8 * Z.of_nat n) (LittleEndian.combine n v)).

  Definition mmioLoadEvent(m: mem)(addr: word)(n: nat)(v: HList.tuple byte n): LogItem :=
    ((m, MMInput, [addr]), (m, [signedByteTupleToReg v])).

  Definition mmioStoreEvent(m: mem)(addr: word)(n: nat)(v: HList.tuple byte n): LogItem :=
    ((m, MMOutput, [addr; signedByteTupleToReg v]), (m, [])).

  (** NOTE: we have no idea how to deal with [translate] when [RVS] is
   * parametrized, so let's just use the default instance for now. *)
  (* Context {RVS: riscv.Spec.Machine.RiscvMachine M word}. *)

  (* common event between riscv-coq and Kami *)
  Inductive Event: Type :=
  | MMInputEvent(addr v: word)
  | MMOutputEvent(addr v: word).

  (* note: given-away and received memory has to be empty *)
  Inductive events_related: Event -> LogItem -> Prop :=
  | relate_MMInput: forall addr v,
      events_related (MMInputEvent addr v) ((map.empty, MMInput, [addr]), (map.empty, [v]))
  | relate_MMOutput: forall addr v,
      events_related (MMOutputEvent addr v) ((map.empty, MMOutput, [addr; v]), (map.empty, [])).

  Inductive traces_related: list Event -> list LogItem -> Prop :=
  | relate_nil:
      traces_related nil nil
  | relate_cons: forall e e' t t',
      events_related e e' ->
      traces_related t t' ->
      traces_related (e :: t) (e' :: t').

  Inductive states_related: KamiMachine * list Event -> RiscvMachine -> Prop :=
  | relate_states:
      forall t t' m riscvXAddrs kpc krf rrf rpc nrpc pinit instrMem kdataMem rdataMem metrics,
        traces_related t t' ->
        KamiProc.RegsToT m = Some (kamiStMk kpc krf pinit instrMem kdataMem) ->
        (pinit = false -> riscvXAddrs = kamiXAddrs) ->
        (pinit = true -> RiscvXAddrsSafe instrMemSizeLg instrMem kdataMem riscvXAddrs) ->
        kpc = toKamiPc rpc ->
        nrpc = word.add rpc (word.of_Z 4) ->
        rrf = convertRegs krf ->
        rdataMem = convertDataMem kdataMem ->
        states_related
          (m, t) {| getMachine := {| RiscvMachine.getRegs := rrf;
                                     RiscvMachine.getPc := rpc;
                                     RiscvMachine.getNextPc := nrpc;
                                     RiscvMachine.getMem := rdataMem;
                                     RiscvMachine.getXAddrs := riscvXAddrs;
                                     RiscvMachine.getLog := t'; |};
                    getMetrics := metrics; |}.

  (* redefine mcomp_sat to simplify for the case where no answer is returned *)
  Definition mcomp_sat_unit(m: M unit)(initialL: RiscvMachine)(post: RiscvMachine -> Prop): Prop :=
    mcomp_sat m initialL (fun (_: unit) => post).

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

  Ltac eval_decode H :=
    unfold decode in H;
    repeat
      match goal with
      | [Hbs: bitSlice _ _ _ = _ |- _] => rewrite Hbs in H
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
    repeat rewrite app_nil_r in H;
    cbv [Datatypes.length
           Pos.of_succ_nat
           Z.gtb Z.compare Pos.compare Pos.compare_cont
           Z.of_nat nth] in H.

  Inductive PHide: Prop -> Prop :=
  | PHidden: forall P: Prop, P -> PHide P.

  Lemma kamiStep_sound_case_pgmInit:
    forall km1 t0 rm1 post kupd cs
           (Hkinv: scmm_inv
                     rv32RfIdx
                     (rv32Fetch (Z.to_nat width)
                                (Z.to_nat instrMemSizeLg)) km1),
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

  (** TODO @joonwonc: make two definitions consistent. *)
  Lemma kamiPgmInitFull_RiscvXAddrsSafe:
    forall pgmFull dataMem,
      KamiPgmInitFull (rv32Fetch (Pos.to_nat 32) (Z.to_nat instrMemSizeLg))
                      pgmFull dataMem ->
      RiscvXAddrsSafe instrMemSizeLg pgmFull dataMem kamiXAddrs.
  Proof.
  Admitted.

  Lemma kamiStep_sound_case_pgmInitEnd:
    forall km1 t0 rm1 post kupd cs
           (Hkinv: scmm_inv
                     rv32RfIdx
                     (rv32Fetch (Z.to_nat width)
                                (Z.to_nat instrMemSizeLg)) km1),
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

  Lemma kamiStep_sound_case_execLd:
    forall km1 t0 rm1 post kupd cs
           (Hkinv: scmm_inv
                     rv32RfIdx
                     (rv32Fetch (Z.to_nat width)
                                (Z.to_nat instrMemSizeLg)) km1),
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
    simpl in H; subst pinit.

    destruct (evalExpr (isMMIO type ldAddr)) eqn:Hmmio.
    - specialize (H9 eq_refl); clear H10.
      destruct H9 as (kt2 & mmioLdRq & mmioLdRs & ? & ? & ? & ? & ?).
      simpl in H; subst cs.

      (** invert a riscv-coq step *)
      rename H0 into HR; move HR at bottom.
      cbv [mcomp_sat_unit
             mcomp_sat
             MinimalMMIOPrimitivesParams
             MetricMinimalMMIOPrimitivesParams] in HR.
      simpl interp at 1 in HR.
      repeat
        (unfold interp_action at 1 in HR;
         cbn [fst snd] in HR;
         unfold MinimalMMIO.interp_action at 1 in HR).
      simpl in HR.

      (* invert fetch *)
      cbv [load] in HR; simpl in HR.
      destruct HR as [HXaddr HR].
      specialize (HXaddr eq_refl); eapply fetch_ok in HXaddr; eauto.
      destruct HXaddr as (rinst & ? & ?).
      (* rewrite H in HR. <-- I want this :P *)
      match type of HR with
        match ?X with _ => _ end =>
        destruct X as [rinst0|] eqn:Hrinst
      end.
      2: {
        exfalso.
        unfold Memory.loadWord in H.
        match goal with
        | [H1: Memory.load_bytes _ _ _ = _, H2: Memory.load_bytes _ _ _ = _ |- _] =>
          match type of H1 with
          | ?t1 = _ => match type of H2 with
                       | ?t2 = _ => change t1 with t2 in H1
                       end
          end; rewrite H1 in H2; try discriminate
        end.
      }

      (* relation between the two raw instructions *)
      unfold Memory.loadWord in H.
      match goal with
      | [H1: Memory.load_bytes _ _ _ = _, H2: Memory.load_bytes _ _ _ = _ |- _] =>
        match type of H1 with
        | ?t1 = _ => match type of H2 with
                     | ?t2 = _ => change t1 with t2 in H1
                     end
        end; rewrite H1 in H2
      end.
      (* inversion_clear H ..? *)
      inversion H; subst rinst0; clear H.
      assert (combine (byte:= @byte_Inst _ (@MachineWidth_XLEN W))
                      4 rinst =
              wordToZ kinst) as Hfetch by (subst kinst; assumption).
      simpl in HR, Hfetch; rewrite Hfetch in HR.

      (* evaluate [decode] *)
      assert (bitSlice (wordToZ kinst) 0 7 = opcode_LOAD) as Hkopc.
      { move H2 at bottom.
        unfold getOptype, rv32Dec, rv32GetOptype in H2.
        unfold evalExpr in H2; fold evalExpr in H2.
        destruct (isEq _ _ _) in H2;
          [|destruct (isEq _ _ _) in H2; discriminate].
        apply (f_equal (@wordToZ _)) in e.
        rewrite kami_getOpcode_ok in e.
        assumption.
      }
      cbv [Init.Nat.mul Init.Nat.add rv32InstBytes BitsPerByte] in Hkopc.

      pose proof (bitSlice_range_ex
                    (wordToZ kinst) 12 15 ltac:(abstract blia))
        as Hf3.
      change (2 ^ (15 - 12)) with 8 in Hf3.
      assert (let z := bitSlice (wordToZ kinst) 12 15 in
              z = 0 \/ z = 1 \/ z = 2 \/ z = 3 \/
              z = 4 \/ z = 5 \/ z = 6 \/ z = 7) by (abstract blia).
      clear Hf3.
      cbv [Init.Nat.mul Init.Nat.add rv32InstBytes BitsPerByte] in H.
      destruct H as [|[|[|[|[|[|[|]]]]]]].
      4, 7, 8: case TODO. (** TODO: [InvalidInstruction] *)

      + (** LB: load-byte *)
        eval_decode HR.

        (* invert the body of [execute] *)
        

        case TODO.

      + (** LH: load-half *) case TODO.
      + (** LW: load-word *) case TODO.
      + (** LHU: load-half-unsigned *) case TODO.
      + (** LBU: load-byte-unsigned *) case TODO.

    - case TODO.

  Qed.

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
      left.
      inversion H3; subst; clear H3 HAction.
      destruct klbl as [annot defs calls]; simpl in *; subst.
      destruct annot; [|discriminate].
      inversion H6; subst; clear H6.
      inversion H2; subst; clear H2.
      eauto using kamiStep_sound_case_pgmInit.

    - (* case "pgmInitEnd" *)
      left.
      inversion H4; subst; clear H4 HAction.
      destruct klbl as [annot defs calls]; simpl in *; subst.
      destruct annot; [|discriminate].
      inversion H6; subst; clear H6.
      inversion H2; subst; clear H2.
      eauto using kamiStep_sound_case_pgmInitEnd.

    - (* case "execLd" *)
      right.
      inversion H3; subst; clear H3 HAction.
      destruct klbl as [annot defs calls]; simpl in *; subst.
      destruct annot; [|discriminate].
      inversion H6; subst; clear H6.
      inversion H2; subst; clear H2.
      case TODO.

    - (* case "execLdZ" *) case TODO.
    - (* case "execSt" *) case TODO.
    - (* case "execNm" *)
      right.

      (** Apply the Kami inversion lemma for the [execNm] rule. *)
      inversion H4; subst; clear H4 HAction.
      destruct klbl as [annot defs calls]; simpl in *; subst.
      destruct annot; [|discriminate].
      inversion H6; subst; clear H6.
      inversion H2; subst; clear H2.
      inversion H0; subst; clear H0.
      eapply invert_Kami_execNm in H; eauto.
      unfold kamiStMk, KamiProc.pc, KamiProc.rf, KamiProc.pgm, KamiProc.mem in H.
      destruct H as [? [? [km2 [? ?]]]].
      simpl in H, H0; subst.
      clear H6.
      specialize (H7 eq_refl); rename H7 into Hxs.

      rename H1 into HR; move HR at bottom.
      cbv [mcomp_sat_unit
             mcomp_sat
             MinimalMMIOPrimitivesParams
             MetricMinimalMMIOPrimitivesParams] in HR.
      simpl interp at 1 in HR.
      repeat
        (unfold interp_action at 1 in HR;
         cbn [fst snd] in HR;
         unfold MinimalMMIO.interp_action at 1 in HR).
      simpl in HR.

      (* invert fetch *)
      cbv [load] in HR; simpl in HR.
      destruct HR as [HXaddr HR].
      specialize (HXaddr eq_refl); eapply fetch_ok in HXaddr; eauto.
      destruct HXaddr as (rinst & ? & ?).
      (* rewrite H in HR. <-- I want this :P *)
      match type of HR with
        match ?X with _ => _ end =>
        destruct X as [rinst0|] eqn:Hrinst
      end.
      2: {
        exfalso.
        unfold Memory.loadWord in H.
        match goal with
        | [H1: Memory.load_bytes _ _ _ = _, H2: Memory.load_bytes _ _ _ = _ |- _] =>
          match type of H1 with
          | ?t1 = _ => match type of H2 with
                       | ?t2 = _ => change t1 with t2 in H1
                       end
          end; rewrite H1 in H2; try discriminate
        end.
      }

      unfold Memory.loadWord in H.
      match goal with
      | [H1: Memory.load_bytes _ _ _ = _, H2: Memory.load_bytes _ _ _ = _ |- _] =>
        match type of H1 with
        | ?t1 = _ => match type of H2 with
                     | ?t2 = _ => change t1 with t2 in H1
                     end
        end; rewrite H1 in H2
      end.
      (* inversion_clear H ..? *)
      inversion H; subst rinst0; clear H.

      (** Invert Kami decode/execute *)
      destruct H3 as (kinst & exec_val & ? & ? & ?).

      assert (combine (byte:= @byte_Inst _ (@MachineWidth_XLEN W))
                      4 rinst =
              wordToZ kinst) as Hfetch by (subst kinst; assumption).
      simpl in HR, Hfetch; rewrite Hfetch in HR.

      (* evaluate [decode]. *)
      assert (bitSlice (wordToZ kinst) 0 7 = opcode_OP) as H11 by case TODO.
      cbv [Init.Nat.mul Init.Nat.add rv32InstBytes BitsPerByte] in H11.
      assert (bitSlice (wordToZ kinst) 12 15 = funct3_ADD) as H12 by case TODO.
      cbv [Init.Nat.mul Init.Nat.add rv32InstBytes BitsPerByte] in H12.
      assert (bitSlice (wordToZ kinst) 25 32 = funct7_ADD) as H13 by case TODO.
      cbv [Init.Nat.mul Init.Nat.add rv32InstBytes BitsPerByte] in H13.
      eval_decode HR.

      (* invert the body of [execute] *)
      simpl in HR.
      unfold interp_action at 1 in HR.
      unfold MinimalMMIO.interp_action at 1 in HR.
      cbn [fst snd] in HR.
      match type of HR with
        match ?X with _ => _ end =>
        destruct X; [(** TODO @joonwonc: prove the value of `R0` is
                      * always zero in Kami steps. *) case TODO|]
      end.
      destruct HR as [? HR].
      
      simpl in HR.
      match type of HR with
        match ?X with _ => _ end => destruct X eqn:?; [|exfalso]
      end.
      2: {
        eapply convertRegs_valid, Heqo; [eassumption|].
        change 32 with (2^5).
        eapply bitSlice_range_ex; blia.
      }

      unfold interp_action at 1 in HR.
      unfold MinimalMMIO.interp_action at 1 in HR.
      cbn [fst snd] in HR.
      match type of HR with
        match ?X with _ => _ end =>
        destruct X; [(** TODO @joonwonc: ditto, about `R0` *) case TODO|]
      end.
      destruct HR as [? HR].
      
      simpl in HR.
      match type of HR with
        match ?X with _ => _ end => destruct X eqn:?; [|exfalso]
      end.
      2: {
        eapply convertRegs_valid, Heqo0; [eassumption|].
        change 32 with (2^5).
        eapply bitSlice_range_ex; blia.
      }

      unfold interp_action at 1 in HR.
      unfold MinimalMMIO.interp_action at 1 in HR.
      cbn [fst snd] in HR.
      match type of HR with
        match ?X with _ => _ end =>
        destruct X; [(** TODO @joonwonc: writing to `R0` *) case TODO|]
      end.
      destruct HR as [? HR].

      simpl in HR.
      unfold interp_action at 1 in HR.
      unfold MinimalMMIO.interp_action at 1 in HR.
      cbn [fst snd] in HR.
      simpl in HR.

      (** Construction *)
      unfold doExec, getNextPc, rv32Exec in *.
      do 2 eexists.
      split; [|split];
        [eapply KamiSilent; reflexivity| |eassumption].
      remember (evalExpr (rv32GetDst type kinst)) as dst.

      econstructor.
      { assumption. }
      { unfold RegsToT; rewrite H2.
        subst km2 dst; reflexivity.
      }
      { intros; discriminate. }
      { intros; assumption. }
      { subst.
        rewrite kami_rv32NextPc_op_ok; auto.
        { rewrite <-toKamiPc_wplus_distr; auto. }
        { rewrite kami_getOpcode_ok; assumption. }
      }
      { reflexivity. }
      { subst exec_val.
        rewrite <-kami_rv32GetDst_ok by assumption.
        rewrite <-kami_rv32GetSrc1_ok in Heqo by assumption.
        rewrite <-kami_rv32GetSrc2_ok in Heqo0 by assumption.
        rewrite convertRegs_put
          with (instrMemSizeLg:= instrMemSizeLg) by assumption.
        erewrite <-convertRegs_get
          with (instrMemSizeLg:= instrMemSizeLg) (v:= k) by auto.
        erewrite <-convertRegs_get
          with (instrMemSizeLg:= instrMemSizeLg) (v:= k0) by auto.
        erewrite kami_rv32DoExec_Add_ok;
          [|rewrite kami_getOpcode_ok; assumption
           |rewrite kami_getFunct7_ok; assumption
           |rewrite kami_getFunct3_ok; assumption].
        reflexivity.
      }
      { reflexivity. }

    - (* case "execNmZ" *) case TODO.

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

  Definition mm: Modules := Kami.Ex.SC.mm memInit rv32MMIO.
  Definition p4mm: Modules := p4mm (conj Hinstr1 Hinstr2) memInit.

  Lemma states_related_init:
    states_related (initRegs (getRegInits (@proc instrMemSizeLg memInit)), [])
                   {| getMachine :=
                        {| (* TODO will need to be the actual value corresponding
                             to Kami in order for the proof to work *)
                          RiscvMachine.getRegs :=
                            convertRegs (Kami.Semantics.evalConstT KamiProc.rfInitVal);
                          RiscvMachine.getPc := word.of_Z 0;
                          RiscvMachine.getNextPc := word.of_Z 4;
                          RiscvMachine.getMem :=
                            map.putmany otherMemInit (convertInstrMem _ prg);
                          RiscvMachine.getXAddrs := nil; (* <-- TODO adapt *)
                          RiscvMachine.getLog := nil; (* <-- intended to be nil *) |};
                      getMetrics := MetricLogging.EmptyMetricLog; |}.
  Proof.
    case TODO.
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
                m0RV.(getMem) = map.putmany otherMemInit (convertInstrMem _ prg) -> (* rhs overrides lhs *)
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
    pose proof (@proc_correct instrMemSizeLg (conj Hinstr1 Hinstr2) memInit) as P.
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
      + unfold getMachine, getRegs; intros.
        eapply convertRegs_valid; [eassumption|blia].
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
