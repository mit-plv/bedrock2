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

Require Import Kami.Syntax Kami.Semantics Kami.Tactics.
Require Import Kami.Ex.MemTypes Kami.Ex.SC Kami.Ex.SCMMInl Kami.Ex.SCMMInv.
Require Import Kami.Ex.IsaRv32.

Require Import processor.KamiProc.
Require Import processor.FetchOk processor.DecExecOk.

Local Open Scope Z_scope.

Instance KamiWordsInst: Utility.Words := @KamiWord.WordsKami width width_cases.

Section Equiv.

  (* TODO not sure if we want to use ` or rather a parameter record *)
  Context {M: Type -> Type}.
  Context {Registers: map.map Register word}
          {mem: map.map word byte}.

  Notation RiscvMachine := (@MetricRiscvMachine KamiWordsInst Registers mem).

  Context (mcomp_sat:
             forall A: Type,
               M A -> RiscvMachine -> (A -> RiscvMachine -> Prop) -> Prop)
          {MMonad: Monad M}
          {rvm: RiscvProgram M word}.
  Arguments mcomp_sat {A}.

  (** * Processor, software machine, and states *)

  Variable (instrMemSizeLg: Z).
  Hypothesis (HinstrMemBound: instrMemSizeLg <= width - 2).

  Variable (memInit: MemInit (Z.to_nat width) rv32DataBytes).

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

  (* These two specify what happens on loads and stores which are outside the memory, eg MMIO *)
  (* TODO these will have to be more concrete *)
  Context (nonmem_load: forall (n: nat), SourceType -> word -> M (HList.tuple byte n)).
  Context (nonmem_store: forall (n: nat), SourceType -> word -> HList.tuple byte n -> M unit).

  Instance MinimalMMIOPrimitivesParams: PrimitivesParams M RiscvMachine := {
    Primitives.mcomp_sat := @mcomp_sat;

    (* any value can be found in an uninitialized register *)
    Primitives.is_initial_register_value x := True;

    Primitives.nonmem_load := nonmem_load;
    Primitives.nonmem_store := nonmem_store;
  }.

  Context {Pr: MetricPrimitives MinimalMMIOPrimitivesParams}.

  (** NOTE: we have no idea how to deal with [translate] 
   * if [RVS] is parametrized, so let's just use the default instance for now.
   *)
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
      forall t t' m riscvXAddrs kpc rf rrf pc pinit instrMem dataMem metrics,
        traces_related t t' ->
        KamiProc.RegsToT m = Some (kamiStMk kpc rf pinit instrMem dataMem) ->
        (pinit = false -> riscvXAddrs = kamiXAddrs) ->
        (pinit = true -> RiscvXAddrsSafe instrMemSizeLg instrMem dataMem riscvXAddrs) ->
        kpc = toKamiPc pc ->
        rrf = convertRegs rf ->
        states_related
          (m, t) {| getMachine := {| RiscvMachine.getRegs := rrf;
                                     RiscvMachine.getPc := pc;
                                     RiscvMachine.getNextPc := word.add pc (word.of_Z 4);
                                     RiscvMachine.getMem := convertDataMem dataMem;
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

  Ltac inv_bind H :=
    apply (proj2 (@spec_Bind _ _ _ _ MinimalMMIOPrimitivesParams mcomp_sat_ok _ _ _ _ _ _)) in H;
    let mid := fresh "mid" in
    destruct H as (mid & ? & ?).

  Ltac inv_getPC H :=
    match type of H with
    | _ _ _ ?mid =>
      apply spec_getPC with (post0:= mid) in H; simpl in H
    end.

  Ltac inv_bind_apply H :=
    match type of H with
    | ?mid _ _ =>
      repeat
        match goal with
        | [H0: forall _ _, mid _ _ -> _ |- _] => specialize (H0 _ _ H)
        end
    end.

  Ltac inv_loadWord H :=
    apply @spec_loadWord in H; [|assumption..]; simpl in H.

  Ltac inv_step H :=
    apply @spec_step in H; [|assumption..];
    unfold withNextPc, RiscvMachine.getNextPc, withRegs in H;
    simpl in H.

  Ltac inv_mcomp_sat :=
    repeat
      match goal with
      | [H: mcomp_sat_unit _ _ _ |- _] => move H at bottom; red in H; unfold run1 in H
      | [H: mcomp_sat (_ <- _; _) _ _ |- _] => inv_bind H

      | [H: Primitives.mcomp_sat (_ <- _; _) _ _ |- _] => inv_bind H
      | [H: _ _ _ |- _] => progress (inv_bind_apply H)
                                    
      | [H: Primitives.mcomp_sat getPC _ _ |- _] => inv_getPC H
      | [H: Primitives.mcomp_sat (loadWord _ _) _ _ |- _] => inv_loadWord H
      end.

  Ltac inv_riscv_fetch :=
    repeat
      match goal with
      | [H: _ /\ _ |- _] => destruct H
      | [H: Fetch = Fetch -> isXAddr _ _ |- _] =>
        specialize (H eq_refl); eapply fetch_ok in H; eauto;
        let rinst := fresh "rinst" in
        destruct H as (rinst & ? & ?)
      | [H: _ \/ (Memory.loadWord _ _ = None /\ _) |- _] => destruct H; [|exfalso]
      | [H: exists _, _ /\ _ |- _] =>
        let rinst := fresh "rinst" in destruct H as (rinst & ? & ?)
      | [H1: Memory.loadWord _ _ = _, H2: Memory.loadWord _ _ = _ |- _] =>
        match type of H1 with
        | ?t1 = _ => match type of H2 with
                     | ?t2 = _ => change t1 with t2 in H1
                     end
        end; rewrite H1 in H2; try discriminate
      | [H: Some ?v = Some _ |- _] => inversion H; subst v; clear H
      end.

  Ltac inv_riscv :=
    repeat
      (inv_mcomp_sat;
       repeat
         (** TODO: add cases for decode and execute *)
         match goal with
         | _ => inv_riscv_fetch
         end).

  Ltac kami_step_case_empty :=
    left; FMap.mred; fail.

  Inductive PHide: Prop -> Prop :=
  | PHidden: forall P: Prop, P -> PHide P.

  Hypothesis (HpgmInit: PgmInitNotMMIO
                          (rv32Fetch (Z.to_nat width) (Z.to_nat instrMemSizeLg))
                          rv32MMIO).

  Lemma kamiStep_sound_case_pgmInit:
    forall km1 t0 rm1 post kupd cs
           (Hkinv: scmm_inv
                     rv32RfIdx
                     (rv32Fetch (BinInt.Z.to_nat width)
                                (BinInt.Z.to_nat instrMemSizeLg)) km1),
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
    eapply invert_Kami_pgmInit in H1; eauto.
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
      KamiPgmInitFull (rv32Fetch (Pos.to_nat 32) (BinInt.Z.to_nat instrMemSizeLg))
                      pgmFull dataMem ->
      RiscvXAddrsSafe instrMemSizeLg pgmFull dataMem kamiXAddrs.
  Proof.
  Admitted.

  Lemma kamiStep_sound_case_pgmInitEnd:
    forall km1 t0 rm1 post kupd cs
           (Hkinv: scmm_inv
                     rv32RfIdx
                     (rv32Fetch (BinInt.Z.to_nat width)
                                (BinInt.Z.to_nat instrMemSizeLg)) km1),
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
    eapply invert_Kami_pgmInitEnd in H1; eauto.
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
                     (rv32Fetch (BinInt.Z.to_nat width)
                                (BinInt.Z.to_nat instrMemSizeLg)) km1),
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
    destruct H1 as (? & kinst & ldAddr & ? & ? & ? & ?).
    simpl in H; subst pinit.

    destruct (evalExpr (isMMIO type ldAddr)) eqn:Hmmio.
    - specialize (H3 eq_refl); clear H8.
      destruct H3 as (kt2 & mmioLdRq & mmioLdRs & ? & ? & ? & ? & ?).
      simpl in H; subst cs.

      (** Invert a riscv-coq step. *)
      inv_riscv.

      (** Relation between the two raw instructions *)
      assert (combine (byte:= @byte_Inst _ (@MachineWidth_XLEN W))
                      4 rinst =
              wordToZ kinst) as Hfetch by (subst kinst; assumption).
      simpl in H0, Hfetch; rewrite Hfetch in H0.

      (** Invert riscv-coq decode/execute *)
      match type of H0 with
      | context [decode ?i ?al] =>
        destruct (decode i al) eqn:Hdec;
          [(* IInstruction *)
          |(* MInstruction *) admit
          |(** TODO @samuelgruetter: remove the other cases except I and M --
            * execution with [iset] (= RV32IM) cannot have such cases.
            *)
          admit..]
      end.
      (** TODO @samuelgruetter: here the instruction should be [Lw _ _ _] *)
      destruct iInstruction.
      4-40: admit.
      1-2: admit.

      apply invert_decode_Lw in Hdec.
      destruct Hdec as [Hopc [Hrd [Hf3 [Hrs1 Himm12]]]].

      simpl in H0.

      inv_riscv.

      apply spec_getRegister with (post0:= mid2) in H0.
      destruct H0; [|admit (** TODO @joonwonc: prove the value of `R0` is
                            * always zero in Kami steps. *)].
      simpl in H0; destruct H0.
      destruct_one_match_hyp;
        [rename w into v1|admit (** TODO: prove it never fails to read
                                 * a register value once the register
                                 * is valid. *)].

      inv_riscv.
      apply spec_Return in H15.

      inv_bind_apply H15.
      inv_bind H17.
      inv_loadWord H17.
      destruct H17.
      destruct H19; [admit|]. (* Let's go to the MMIO case. *)
      destruct H19.

      Fail (unfold nonmem_load in H20).

      (** Construction *)

      (* do 2 eexists. *)
      (* repeat split; [| |eassumption]. *)
      (* + eapply KamiMMIO; reflexivity. *)
      (* + rewrite H8. *)
      (*   econstructor; eauto. *)
      (*   * admit. *)
      (*   * unfold getNextPc, rv32Exec. *)
      (*     rewrite kami_rv32NextPc_load_ok; auto; *)
      (*       [|rewrite kami_getOpcode_ok *)
      (*           with (instrMemSizeLg:= instrMemSizeLg); assumption]. *)
      (*     unfold kamiStMk; simpl. *)
      (*     admit. *)
      (*   * subst rd. *)
      (*     erewrite convertRegs_put by eassumption. *)
      (*     admit. *)

      admit.

    - clear H3; specialize (H8 eq_refl).
      
  Admitted.
  
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
    apply scmm_inv_ok in Hkreach; [|reflexivity|assumption].

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
      eauto using kamiStep_sound_case_execLd.
      
    - (* case "execLdZ" *) admit.
    - (* case "execSt" *) admit.
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

      (** Invert a riscv-coq step. *)
      inv_riscv.
      
      (** Invert Kami decode/execute *)
      destruct H3 as (kinst & exec_val & ? & ? & ?).

      (** Relation between the two raw instructions *)
      assert (combine (byte:= @byte_Inst _ (@MachineWidth_XLEN W))
                      4 rinst =
              wordToZ kinst) as Hfetch by (subst kinst; assumption).
      simpl in H0, Hfetch; rewrite Hfetch in H0.

      (** Invert riscv-coq decode/execute *)
      match type of H0 with
      | context [decode ?i ?al] =>
        destruct (decode i al) eqn:Hdec;
          [(* IInstruction *)
          |(* MInstruction *) admit
          |(** TODO @samuelgruetter: remove the other cases except I and M --
            * execution with [iset] (= RV32IM) cannot have such cases.
            *)
          admit..]
      end.
      destruct iInstruction.
      21: { (* Case of Add *)
        apply invert_decode_Add in Hdec.
        destruct Hdec as [Hopc [Hrd [Hf3 [Hrs1 [Hrs2 Hf7]]]]].

        simpl in H0.
        (** TODO @samuelgruetter: using [Hdec] we should be able to derive
         * the relation among [inst], [rd], [rs1], and [rs2],
         * e.g., [bitSlice inst _ _ = rs1].
         *)

        inv_bind H0.
        apply spec_getRegister with (post0:= mid2) in H0.
        destruct H0; [|admit (** TODO @joonwonc: prove the value of `R0` is
                              * always zero in Kami steps. *)].
        simpl in H0; destruct H0.
        destruct_one_match_hyp;
          [rename w into v1|admit (** TODO: prove it never fails to read
                                   * a register value once the register
                                   * is valid. *)].
        inv_bind_apply H12.
        inv_bind H11.
        apply spec_getRegister with (post0:= mid3) in H11.
        destruct H11; [|admit (** TODO @joonwonc: ditto, about `R0` *)].
        simpl in H11; destruct H11.
        destruct_one_match_hyp; [rename w into v2|
                                 admit (** TODO: ditto, about valid register reads *)].
        inv_bind_apply H14.
        apply @spec_setRegister in H13; [|assumption..].
        destruct H13; [|admit (** TODO @joonwonc: writing to `R0` *)].
        simpl in H13; destruct H13.
        inv_bind_apply H15.
        inv_step H1.

        (** Construction *)
        unfold doExec, getNextPc, rv32Exec in *.
        do 2 eexists.
        split; [|split];
          [eapply KamiSilent; reflexivity| |eassumption].
        remember (evalExpr (rv32GetDst type kinst)) as dst.

        econstructor.
        - assumption.
        - unfold RegsToT; rewrite H2, H10.
          subst dst; reflexivity.
        - intros; discriminate.
        - intros; assumption.
        - subst.
          rewrite kami_rv32NextPc_op_ok; auto;
            [|rewrite kami_getOpcode_ok
                with (instrMemSizeLg:= instrMemSizeLg); assumption].
          rewrite <-toKamiPc_wplus_distr; auto.
        - subst exec_val.
          replace rd with (Word.wordToZ dst) in *
            by (subst dst rd;
                apply kami_rv32GetDst_ok
                  with (instrMemSizeLg:= instrMemSizeLg); assumption).
          replace rs1
            with (Word.wordToZ (evalExpr (rv32GetSrc1 type kinst))) in *
            by (subst rs1;
                apply kami_rv32GetSrc1_ok
                  with (instrMemSizeLg:= instrMemSizeLg); assumption).
          replace rs2
            with (Word.wordToZ (evalExpr (rv32GetSrc2 type kinst))) in *
            by (subst rs2;
                apply kami_rv32GetSrc2_ok
                  with (instrMemSizeLg:= instrMemSizeLg); assumption).
          erewrite <-convertRegs_get
            with (instrMemSizeLg:= instrMemSizeLg) (v:= v1) by auto.
          erewrite <-convertRegs_get
            with (instrMemSizeLg:= instrMemSizeLg) (v:= v2) by auto.
          rewrite kami_rv32DoExec_Add_ok;
            [|rewrite kami_getOpcode_ok
                with (instrMemSizeLg:= instrMemSizeLg); assumption
             |rewrite kami_getFunct7_ok
                with (instrMemSizeLg:= instrMemSizeLg); assumption
             |rewrite kami_getFunct3_ok
                with (instrMemSizeLg:= instrMemSizeLg); assumption].
          rewrite convertRegs_put
            with (instrMemSizeLg:= instrMemSizeLg) by assumption.
          subst dst.
          reflexivity.
      }
      all: admit.

    - (* case "execNmZ" *) admit.

  Admitted.

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
  Definition mm_without_MMIO(prog: kword instrMemSizeLg -> kword 32): Modules.
  (* pseudo-Kami-code:
     MODULE {
        Register "mem" : Vector (Data dataBytes) addrSize <- "prog padded with zeroes"
        with Method myMemOp ...
     } *)
  Admitted. (* TODO @joonwonc proof structure *)

  Definition mm(prog: kword instrMemSizeLg -> kword 32): Modules.
  (* pseudo-Kami-code:
  MODULE {
    Method "memOp" (a : Struct RqFromProc): Struct RsToProc :=
      LET addr <- #a!RqFromProc@."addr";

      If (isMMIO _ addr) then (** mmio *)
        Call rs <- mmioExec(#a);
        Ret #rs
      else
        forward the request to mm_without_MMIO
   }. *)
  Admitted. (* TODO @joonwonc proof structure *)

  Definition p4mm(prog: kword instrMemSizeLg -> kword 32): Modules.
    refine (ProcMemCorrect.p4stf
              _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _
              ++ mm prog)%kami.
  Admitted. (* TODO @joonwonc proof structure *)

  Lemma splitKamiSpecProcStepsIntoProgramLoadAndExec: forall mFinal t,
      Multistep kamiProc (initRegs (getRegInits kamiProc)) mFinal t ->
      exists mStart,
        Multistep kamiProc (initRegs (getRegInits kamiProc)) mStart nil /\
        Multistep kamiProc mStart mFinal t.
  Proof.
    (* TODO @joonwonc proof structure
       This lemma can also look totally different or be inlined, anything is fine as long as
       riscv_to_kamiImplProcessor works *)
  Admitted.

  Definition someInitialRegs: Registers :=
    map.putmany_of_tuple (HList.tuple.unfoldn Z.succ 31 1)
                         (HList.tuple.unfoldn Datatypes.id 31 (word.of_Z 42))
                         map.empty.

  Lemma equivalentLabelSeq_preserves_KamiLabelSeqR: forall t1 t2 t,
      equivalentLabelSeq (liftToMap1 (idElementwise (A:={x : SignatureT & SignT x}))) t1 t2 ->
      KamiLabelSeqR t2 t ->
      KamiLabelSeqR t1 t.
  Proof.
    (* TODO @joonwonc proof structure
       No need to prove it if it's annoying to do so but please check if you think it's true *)
  Admitted.

  Lemma riscv_to_kamiImplProcessor:
    forall (traceProp: list Event -> Prop)
           (* --- hypotheses which will be proven by the compiler --- *)
           (RvInv: RiscvMachine -> Prop)
           (prg: kword instrMemSizeLg -> kword 32)
           (establishRvInv:
              forall (m0RV: RiscvMachine) (otherMem: mem),
                m0RV.(getMem) = map.putmany otherMem (convertInstrMem _ prg) -> (* rhs overrides lhs *)
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
      Behavior (p4mm prg) mFinal t ->
      (* --- conclusion ---
         The trace produced by the kami implementation can be mapped to an MMIO trace
         (this guarantees that the only external behavior of the kami implementation is MMIO)
         and moreover, this MMIO trace satisfies some desirable property. *)
      exists (t': list Event), KamiLabelSeqR t t' /\ traceProp t'.
  Proof.
    intros.
    pose proof (@proc_correct instrMemSizeLg memInit) as P.
    unfold traceRefines in P.
    replace (@KamiProc.p4mm instrMemSizeLg memInit)
      with (p4mm prg) in P by case TODO. (* TODO @joonwonc proof structure *)
    specialize P with (1 := H).
    destruct P as (mFinal' & t' & B & E).
    inversion B. subst.
    pose proof kamiMultiStep_sound as P.
    specialize P with (1 := preserveRvInv).
    unfold kamiProc in P.
    apply splitKamiSpecProcStepsIntoProgramLoadAndExec in HMultistepBeh.
    destruct HMultistepBeh as (mStart & MSInit & MSRun).
    inversion_clear MSInit; subst.
    specialize P with (1 := Kami.SemFacts.reachable_init _).
    specialize P with (1 := MSRun).
    specialize P with (t0 := nil).
    setoid_rewrite List.app_nil_r in P.
    set (otherMem := map.empty: mem). (* <-- TODO adapt *)
    specialize (P {| getMachine :=
                       {| (* TODO will need to be the actual value corresponding
                             to Kami in order for the proof to work *)
                         RiscvMachine.getRegs := someInitialRegs;
                         RiscvMachine.getPc := word.of_Z 0;
                         RiscvMachine.getNextPc := word.of_Z 4;
                         RiscvMachine.getMem := map.putmany otherMem
                                                            (convertInstrMem _ prg);
                         RiscvMachine.getXAddrs := nil; (* <-- TODO adapt *)
                         RiscvMachine.getLog := nil; (* <-- intended to be nil *) |};
                     getMetrics := MetricLogging.EmptyMetricLog; |}).
    destruct P as (mF & t'' & R & Rel & Inv).
    - (* TODO @joonwonc proof structure
         prove that program initialization (MSInit) on the kami spec processor
         worked correctly according to this states_related predicate in the goal *)
      case TODO.
    - eapply establishRvInv; simpl.
      + reflexivity.
      + reflexivity.
      + (* TODO @joonwonc proof structure *)
        (* will not be someInitialRegs but what Kami computed *)
        case TODO.
      + reflexivity.
    - specialize (useRvInv _ Inv).
      inversion Rel. subst. clear Rel.
      simpl in useRvInv.
      destruct useRvInv as (t''' & R' & p).
      eexists. split; [|exact p].
      eapply equivalentLabelSeq_preserves_KamiLabelSeqR.
      1: eassumption.
      pose proof (traces_related_unique R' H2). subst t'''.
      assumption.
  Qed.

End Equiv.
