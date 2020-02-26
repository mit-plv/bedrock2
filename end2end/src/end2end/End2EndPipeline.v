Require Import String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Logic.FunctionalExtensionality.
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
Require Import compilerExamples.MMIO.
Require Import riscv.Platform.FE310ExtSpec.
Require Import compiler.FlatToRiscvDef.
Require Import coqutil.Tactics.rdelta.
Require Import end2end.KamiRiscvWordProperties.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import compiler.CompilerInvariant.
Require Import compiler.ExprImpEventLoopSpec.

Local Open Scope Z_scope.

Local Axiom TODO_joonwon: False.

Require Import Coq.Classes.Morphisms.

Instance FlatToRiscvDefParams: FlatToRiscvDef.parameters :=
  { FlatToRiscvDef.W := @KamiWord.WordsKami KamiProc.width KamiProc.width_cases;
    FlatToRiscvDef.compile_ext_call := compile_ext_call;
    FlatToRiscvDef.compile_ext_call_length := compile_ext_call_length';
    FlatToRiscvDef.compile_ext_call_emits_valid := compile_ext_call_emits_valid;
  }.

Instance word_riscv_ok: @RiscvWordProperties.word.riscv_ok 32 KamiWord.wordW.
refine (@KamiRiscvWordProperties.kami_word_riscv_ok 5 _ _).
all: cbv; congruence.
Qed.

(* TODO_joonwon move/modify this if needed *)
Definition kami_mem_contains_bytes(bs: list Coq.Init.Byte.byte){memSizeLg}(from: Utility.word)
           (mem: Syntax.Vec (Syntax.ConstT (Syntax.Bit MemTypes.BitsPerByte)) memSizeLg): Prop :=
  forall b n,
    nth_error bs n = Some b ->
    Word.natToWord 8 (Byte.to_nat b)
    = Semantics.evalConstT (Syntax.ConstVector mem)
                           (Semantics.evalZeroExtendTrunc memSizeLg (Word.wplus from (Word.natToWord _ n))).

Section Connect.

  Context (instrMemSizeLg memSizeLg: Z).
  Context (memInit: Syntax.Vec (Syntax.ConstT (Syntax.Bit MemTypes.BitsPerByte))
                               (Z.to_nat memSizeLg)).

  Hypotheses (instrMemSizeLg_bounds: 3 <= instrMemSizeLg <= 30)
             (Hkmem: 2 + instrMemSizeLg < memSizeLg <= 32).

  Definition p4mm: Kami.Syntax.Modules :=
    KamiRiscv.p4mm instrMemSizeLg memSizeLg (proj1 instrMemSizeLg_bounds)
                   (proj2 instrMemSizeLg_bounds)
                   memInit.

  Context {Registers: map.map Register Utility.word}
          {Registers_ok: map.ok Registers}
          {mem: map.map Utility.word byte}
          {mem_ok: map.ok mem}.

  Instance mmio_params: MMIO.parameters.
    econstructor; try typeclasses eauto.
    - exact (@KamiWord.wordWok _ (or_introl eq_refl)).
    - exact SortedListString.ok.
  Defined.

  Goal True.
  epose (_ : PrimitivesParams (MinimalMMIO.free MetricMinimalMMIO.action MetricMinimalMMIO.result)
                              MetricRiscvMachine).
  Abort.

  Instance pipeline_params: PipelineWithRename.Pipeline.parameters := {|
    Pipeline.FlatToRiscvDef_params := compilation_params;
    Pipeline.ext_spec := FE310CSemantics.ext_spec;
  |}.

  Existing Instance MetricMinimalMMIO.MetricMinimalMMIOSatisfiesPrimitives.

  Instance pipeline_assumptions: @PipelineWithRename.Pipeline.assumptions pipeline_params.
    refine ({|
      Pipeline.PR := _ ; (*MetricMinimalMMIO.MetricMinimalMMIOSatisfiesPrimitives;*)
      Pipeline.FlatToRiscv_hyps := _; (*MMIO.FlatToRiscv_hyps*)
      Pipeline.Registers_ok := _;
    |}).
  - exact SortedListString.ok.
  - refine (MetricMinimalMMIO.MetricMinimalMMIOSatisfiesPrimitives).
  - refine (@MMIO.FlatToRiscv_hyps _).
  - pose proof FE310CSemantics.ext_spec_ok.
    cbv [FlatToRiscvCommon.Semantics_params FlatToRiscvCommon.ext_spec Pipeline.ext_spec pipeline_params].
    abstract (destruct H; split; eauto).
  Defined.

  Definition states_related :=
    @states_related Pipeline.Registers mem instrMemSizeLg memSizeLg
                    (proj1 instrMemSizeLg_bounds) (proj2 instrMemSizeLg_bounds).

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
  Context (spec: @ProgramSpec strname_sem)
          (ml: MemoryLayout)
          (mlOk: MemoryLayoutOk ml)
          (funimplsList: list (string * (list string * list string * cmd))).

  Hypothesis instrMemSizeLg_agrees_with_ml:
    word.sub ml.(code_pastend) ml.(code_start) = word.of_Z instrMemSizeLg.
  Hypothesis heap_start_agree: spec.(datamem_start) = ml.(heap_start).
  Hypothesis heap_pastend_agree: spec.(datamem_pastend) = ml.(heap_pastend).
  Hypothesis code_at_0: ml.(code_start) = word.of_Z 0.

  Hypothesis funimplsList_NoDup: NoDup (List.map fst funimplsList).

  (* goodTrace in terms of "exchange format" (list Event).
     Only holds at the beginning/end of each loop iteration,
     will be transformed into "exists suffix, ..." form later *)
  Definition goodTraceE(t: list Event): Prop :=
    exists bedrockTrace, traces_related t bedrockTrace /\ spec.(goodTrace) bedrockTrace.

  (* Definition kamiMemToBedrockMem: mem := *)
  (*   projT1 (riscvMemInit memInit). *)

  Definition bedrock2Inv := (fun t m l => forall mc, hl_inv spec t m l mc).

  Let funspecs := WeakestPrecondition.call (p := strname_sem) funimplsList.

  Hypothesis goodTrace_implies_related_to_Events: forall (t: list LogItem),
      spec.(goodTrace) t -> exists t': list Event, traces_related t' t.

  (* end to end, but still generic over the program *)
  Lemma end2end:
    (* Assumptions on the program logic level: *)
    forall init_code loop_body,
    map.get (map.of_list funimplsList) "init"%string = Some ([], [], init_code) ->
    (forall m, mem_available ml.(heap_start) ml.(heap_pastend) m -> WeakestPrecondition.cmd funspecs init_code [] m map.empty bedrock2Inv) ->
    map.get (map.of_list funimplsList) "loop"%string = Some ([], [], loop_body) ->
    (forall t m l, bedrock2Inv t m l ->
                   WeakestPrecondition.cmd funspecs loop_body t m l bedrock2Inv) ->
    (* Assumptions on the compiler level: *)
    forall (instrs: list Instruction) (positions: FlatToRiscvCommon.funname_env Z),
    compile_prog ml (map.of_list funimplsList) = Some (instrs, positions) ->
    ExprImp.valid_funs (map.of_list funimplsList) ->
    (* Assumptions on the Kami level: *)
    kami_mem_contains_bytes (instrencode instrs) ml.(code_start) memInit ->
    forall (t: Kami.Semantics.LabelSeqT) (mFinal: KamiImplMachine),
      (* IF the 4-stage pipelined processor steps to some final state mFinal, producing trace t,*)
      Kami.Semantics.Behavior p4mm mFinal t ->
      (* THEN the trace produced by the kami implementation can be mapped to an MMIO trace
         (this guarantees that the only external behavior of the kami implementation is MMIO)
         and moreover, this MMIO trace satisfies "not yet bad", as in, there exists at
         least one way to complete it to a good trace *)
      exists (t': list Event), KamiLabelSeqR t t' /\
                               exists (suffix: list Event), goodTraceE (suffix ++ t').
  Proof.
    intros *. intros GetInit Establish GetLoop Preserve. intros *. intros C V M. intros *. intros B.

    set (traceProp := fun (t: list Event) =>
                        exists (suffix: list Event), goodTraceE (suffix ++ t)).
    change (exists t' : list Event,
               KamiLabelSeqR t t' /\ traceProp t').

    (* stack of proofs, bottom-up: *)

    (* 1) Kami pipelined processor to riscv-coq *)
    pose proof @riscv_to_kamiImplProcessor as P1.
    specialize_first P1 traceProp.
    specialize_first P1 (ll_inv ml spec).
    specialize_first P1 B.
    specialize_first P1 (proj1 Hkmem).
    specialize_first P1 (proj2 Hkmem).
    (* destruct spec. TODO why "Error: sat is already used." ?? *)

    (* 2) riscv-coq to bedrock2 semantics *)
    pose proof compiler_invariant_proofs as P2.
    specialize_first P2 spec.
    specialize_first P2 ml.
    specialize_first P2 mlOk.
    destruct P2 as [ P2establish [P2preserve P2use] ].
    eapply P1; clear P1.
    - assumption.
    - (* establish *)
      intros.
      eapply P2establish.
      unfold initial_conditions.
      exists (map.of_list funimplsList), instrs, positions.
      destr_RiscvMachine m0RV.
      subst.
      ssplit.
      + (* 3) bedrock2 semantics to bedrock2 program logic *)
        econstructor.
        * exact V.
        * exact GetInit.
        * intros.
          eapply ExprImp.weaken_exec.
          --
             rewrite ?heap_start_agree, ?heap_pastend_agree in *.
             refine (WeakestPreconditionProperties.sound_cmd _ _ _ _ _ _ _ _ _);
               eauto using FlattenExpr.mk_Semantics_params_ok, FlattenExpr_hyps.

          -- simpl. clear. intros. unfold bedrock2Inv in *. eauto.
        * exact GetLoop.
        * intros. unfold bedrock2Inv in *.
          eapply ExprImp.weaken_exec.
          -- refine (WeakestPreconditionProperties.sound_cmd _ _ _ _ _ _ _ _ _);
               eauto using FlattenExpr.mk_Semantics_params_ok, FlattenExpr_hyps.
          -- simpl. clear. intros. eauto.
      + assumption.
      + clear -M.
        case TODO_joonwon. (* basically a correctness thm for riscvMemInit *)
      + case TODO_joonwon. (* all datamem addresses are defined *)
      + symmetry. exact code_at_0.
      + (* TODO add this hypothesis to KamiRiscv.riscv_to_kamiImplProcessor *)
        case TODO_joonwon.
      + unfold FlatToRiscvCommon.regs_initialized. intros.
        match goal with
        | |- exists _, ?x = Some _ => destr x; [eauto|exfalso]
        end.
        match goal with
        | H: forall _, _ -> _ <> None |- _ => eapply H; eauto
        end.
      + reflexivity.
      + simpl. split.
        * case TODO_joonwon. (* prove that riscvMemInit is undefined on the MMIO addresses *)
        * case TODO_joonwon. (* add this hypothesis to KamiRiscv.riscv_to_kamiImplProcessor *)
    - (* preserve *)
      intros.
      refine (P2preserve _ _). assumption.
    - (* use *)
      intros *. intro Inv.
      subst traceProp. simpl.
      specialize_first P2use Inv.
      destruct P2use as [suff Good].
      unfold goodTraceE.
      pose proof (goodTrace_implies_related_to_Events _ Good) as G.
      destruct G as [t' R].
      pose proof (split_ll_trace R). simp.
      eauto 10.
  Qed.

End Connect.

(*
About end2end.
Print Assumptions end2end.
*)
