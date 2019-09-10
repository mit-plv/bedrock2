Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.Utility.
Require Import coqutil.Word.LittleEndian.
Require Import coqutil.Word.Properties.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.Machine.
Require riscv.Platform.Memory.
Require Import riscv.Spec.PseudoInstructions.
Require Import riscv.Proofs.EncodeBound.
Require Import riscv.Proofs.DecodeEncode.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.MkMachineWidth.
Require Import riscv.Utility.Monads. Import MonadNotations.
Require Import riscv.Utility.runsToNonDet.
Require Import coqutil.Datatypes.PropSet.
Require Import riscv.Utility.MMIOTrace.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Spec.MetricPrimitives.
Require Import compiler.RunInstruction.
Require Import compiler.RiscvEventLoop.
Require Import compiler.ForeverSafe.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.Simp.
Require Import processor.KamiWord.
Require Import processor.KamiRiscv.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import compiler.PipelineWithRename.
Require Import compiler.examples.MMIO.
Require Import compiler.FlatToRiscvDef.

Local Open Scope Z_scope.


Instance FlatToRiscvDefParams: FlatToRiscvDef.parameters := {
  FlatToRiscvDef.W := KamiWordsInst;
  FlatToRiscvDef.compile_ext_call := compile_ext_call;
  FlatToRiscvDef.compile_ext_call_length := compile_ext_call_length';
  FlatToRiscvDef.compile_ext_call_emits_valid := compile_ext_call_emits_valid;
}.

Section Connect.

  Context {Registers: map.map Register Utility.word}
          {Registers_ok: map.ok Registers}
          {mem: map.map Utility.word Utility.byte}
          {mem_ok: map.ok mem}
          {stringname_env : forall T : Type, map.map string T}
          {stringname_env_ok: forall T, map.ok (stringname_env T)}
          {NGstate : Type}
          {NG : NameGen string NGstate}
          {src2imp : map.map string Register}
          {src2imp_ops : RegAlloc.map.ops src2imp}.

  Instance mmio_params: MMIO.parameters := {
    byte_ok := KamiWord.word8ok;
    word_ok := @KamiWord.wordWok _ (or_introl eq_refl);
  }.

  Existing Instance MetricMinimalMMIO.MetricMinimalMMIOPrimitivesParams.

  Instance pipeline_params: PipelineWithRename.Pipeline.parameters := {
    Pipeline.FlatToRiscvDef_params := FlatToRiscvDefParams;
    Pipeline.ext_spec := real_ext_spec;
    Pipeline.ext_guarantee mach := map.undef_on mach.(getMem) isMMIOAddr;
    Pipeline.M := (OStateND (@MetricRiscvMachine KamiWordsInst _ mem));
    Pipeline.PRParams := @MetricMinimalMMIO.MetricMinimalMMIOPrimitivesParams
                             _ _ _ (@riscv_ext_spec mmio_params);
    Pipeline.RVM := @MetricMinimalMMIO.IsMetricRiscvMachine _ _ _ riscv_ext_spec;
  }.

  Context {h: @PipelineWithRename.Pipeline.assumptions pipeline_params}.

  Definition KamiMachine: Type := KamiRiscv.KamiMachine.

  Context (instrMemSizeLg: Z) (dataMemSize: nat).
  Hypothesis (HbtbAddr: BinInt.Z.to_nat instrMemSizeLg =
                        (3 + (BinInt.Z.to_nat instrMemSizeLg - 3))%nat).

  Definition kamiStep := kamiStep instrMemSizeLg.
  Definition states_related := @states_related Pipeline.Registers mem instrMemSizeLg.

  Lemma split_ll_trace: forall {t2' t1' t},
      traces_related t (t2' ++ t1') ->
      exists t1 t2, t = t2 ++ t1 /\ traces_related t1 t1' /\ traces_related t2 t2'.
  Proof.
    induction t2'; intros.
    - exists t, nil. simpl in *. repeat constructor. assumption.
    - simpl in H. simp. specialize IHt2' with (1 := H4).
      destruct IHt2' as (t1 & t2 & E & R1 & R2). subst.
      exists t1. exists (e :: t2). simpl. repeat constructor; assumption.
  Qed.

  Lemma states_related_to_traces_related: forall m m' t,
      states_related (m, t) m' -> traces_related t m'.(getLog).
  Proof. intros. inversion H. simpl. assumption. Qed.

  (* for debugging f_equal *)
  Lemma cong_app: forall {A B: Type} (f f': A -> B) (a a': A),
      f = f' ->
      a = a' ->
      f a = f' a'.
  Proof. intros. congruence. Qed.

  (* to tell that we want string names Semantics.params, because there's also
     Z names Semantics.params lingering around *)
  Notation strname_sem := (FlattenExpr.mk_Semantics_params
                             (@Pipeline.FlattenExpr_parameters pipeline_params)).
  Notation cmd := (@cmd ((FlattenExpr.mk_Syntax_params
                            (@Pipeline.FlattenExpr_parameters pipeline_params)))).
  Context (prog: @Program strname_sem cmd)
          (spec: @ProgramSpec strname_sem)
          (sat: @ProgramSatisfiesSpec strname_sem cmd prog (@Semantics.exec strname_sem) spec)
          (ml: MemoryLayout Semantics.width)
          (memInit: Kami.Ex.SC.MemInit
                      (Z.to_nat width)
                      Kami.Ex.IsaRv32.rv32DataBytes).

  Hypotheses
    (HinstrMemBound: instrMemSizeLg <= width - 2)
    (Hinit: KamiProc.PgmInitNotMMIO
              (Kami.Ex.IsaRv32.rv32Fetch (Z.to_nat width) (Z.to_nat instrMemSizeLg))
              KamiProc.rv32MMIO).

  Definition p4mm(prg: kword instrMemSizeLg -> kword 32): Kami.Syntax.Modules.
    unshelve refine (processor.KamiRiscv.p4mm _ _ _ _ _ _ _ _ prg).
  Admitted.

  (* end to end, but still generic over the program
     TODO also write instantiations where the program is fixed, to reduce number of hypotheses *)
  Lemma end2end:
    forall (goodTrace: list Event -> Prop)
           (prg : kword instrMemSizeLg -> kword 32),
    (* TODO more hypotheses will be needed *)
    forall (t: Kami.Semantics.LabelSeqT) (mFinal: KamiImplMachine),
      (* IF the 4-stage pipelined processor steps to some final state mFinal, producing trace t,*)
      Kami.Semantics.Behavior (p4mm prg) mFinal t ->
      (* THEN the trace produced by the kami implementation can be mapped to an MMIO trace
         (this guarantees that the only external behavior of the kami implementation is MMIO)
         and moreover, this MMIO trace satisfies "not yet bad", as in, there exists at
         least one way to complete it to a good trace *)
      exists (t': list Event), KamiLabelSeqR t t' /\
                               exists (suffix: list Event), goodTrace (suffix ++ t').
  Proof.
    intros.
    (* stack of proofs, bottom-up: *)

    (* 1) Kami pipelined processor to riscv-coq *)
    pose proof (@riscv_to_kamiImplProcessor
                  (OStateND (@MetricRiscvMachine KamiWordsInst
                                                 (@Pipeline.Registers pipeline_params) mem))
                  Registers
                  mem
                  (@Primitives.mcomp_sat _ _ _ _)
                  _
                  (@MetricMinimalMMIO.IsMetricRiscvMachine _ _ _ riscv_ext_spec)
                  instrMemSizeLg HinstrMemBound HbtbAddr
               ) as P1.

    (* 2) riscv-coq to bedrock2 semantics *)

    (* 3) bedrock2 semantics to bedrock2 program logic *)

  Admitted.


  (* will have to be extended with a program logic proof at the top and with the kami refinement
     proof to the pipelined processor at the bottom: *)
  Lemma bedrock2Semantics_to_kamiSpecProcessor:
    forall (goodTrace: list Event -> Prop) (m1 m2: KamiMachine) klseq (t0: list Event)
           (m1': MetricRiscvMachine)
           (Hkreach: Semantics.reachable
                       m1 (KamiRiscv.kamiProc instrMemSizeLg memInit)),
      (* TODO many more hypotheses will be needed *)
      states_related (m1, t0) m1' ->
      Kami.Semantics.Multistep
        (KamiRiscv.kamiProc instrMemSizeLg memInit) m1 m2 klseq ->
      exists suffix t,
        KamiLabelSeqR klseq t /\
        goodTrace (suffix ++ t ++ t0).
  Proof.
    intros.
    pose proof (pipeline_proofs prog spec sat ml) as P.
    edestruct P as (Establish & Preserve & Use); clear P; [admit..|].
    pose proof @kamiMultiStep_sound as Q.
    specialize Q with
        (M := OStateND (@MetricRiscvMachine KamiWordsInst (@Pipeline.Registers pipeline_params) mem)) (m1 := m1) (m2 := m2) (m1' := m1') (klseq := klseq) (t0 := t0)
        (instrMemSizeLg := instrMemSizeLg).
    edestruct Q as (m2' & t & SeqR & Rel & InvFinal).
    - eapply HinstrMemBound.
    - assumption.
    - admit.
    - assumption.
    - eapply Preserve.
    - eassumption.
    - eassumption.
    - eassumption.
    - eapply Establish. admit.
    - apply states_related_to_traces_related in Rel.
      edestruct Use as (suffix & G). 1: exact InvFinal.

    (* TODO ?
    - apply states_related_to_traces_related in Rel.
      edestruct Use as (suffix & llTrace & Rel' & G). 1: exact InvFinal.
      apply split_ll_trace in Rel'.
      destruct Rel' as (llTrace1 & llTrace2 & E & Rel1' & Rel2'). subst.
      pose proof (traces_related_unique Rel Rel1'). subst.
      exists llTrace2. exact G. *)
  Admitted.

End Connect.
