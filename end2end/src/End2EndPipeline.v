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
Require Import coqutil.Tactics.rdelta.

Local Open Scope Z_scope.

Ltac specialize_first_num P Q :=
  first [ specialize P with (1 := Q)
        | specialize P with (2 := Q)
        | specialize P with (3 := Q)
        | specialize P with (4 := Q)
        | specialize P with (5 := Q)
        | specialize P with (6 := Q)
        | specialize P with (7 := Q)
        | specialize P with (8 := Q)
        | specialize P with (9 := Q)
        | fail 1 "no match found for" Q "within the first few hypotheses of" P ].

Ltac specialize_first_ident P a :=
  match type of P with
  | forall                                           (x: _), _ => specialize P with (x := a)
  | forall                                         _ (x: _), _ => specialize P with (x := a)
  | forall                                       _ _ (x: _), _ => specialize P with (x := a)
  | forall                                     _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                                   _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                                 _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                               _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                             _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                           _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                         _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                       _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                     _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                   _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall                 _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall               _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall             _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall           _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall         _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall       _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall     _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall   _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | forall _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ (x: _), _ => specialize P with (x := a)
  | _ => fail 1 "no match found for" a "within the first few arguments of" P
  end.

Ltac specialize_first P Q := specialize_first_num P Q || specialize_first_ident P Q.



Axiom TODO: False.

Definition funspecs_satisfy_funimpls: Prop. case TODO. Defined.

Require Import Coq.Classes.Morphisms.
Lemma program_logic_sound
      {p : Semantics.parameters}
      {Proper_ext_spec : forall trace m act args,
          Proper ((pointwise_relation _ (pointwise_relation _ Basics.impl)) ==> Basics.impl)
                 (Semantics.ext_spec trace m act args)}:
  forall (funspecs: Syntax.funname ->
                    (Semantics.trace -> mem -> list Semantics.word ->
                     (Semantics.trace -> mem -> list Semantics.word -> Prop) -> Prop))
         (s: funspecs_satisfy_funimpls)
         (funimpls: Semantics.env)
         (c: cmd) (t: Semantics.trace) (m: mem) (l: locals) (mc: MetricLogging.MetricLog)
         (post : Semantics.trace -> mem -> locals -> Prop),
    WeakestPrecondition.cmd funspecs c t m l post ->
    Semantics.exec funimpls c t m l mc (fun t' m' l' mc' => post t' m' l').
Proof.
  intros.
  assert (funimpls = map.empty) as E by case TODO. rewrite E.
  eapply WeakestPreconditionProperties.sound_nil.
  match goal with
  | _: WeakestPrecondition.cmd ?F' _ _ _ _ _ |- WeakestPrecondition.cmd ?F _ _ _ _ _ =>
    replace F with F' by case TODO
  end.
  assumption.
Qed.

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
          {src2imp : map.map string Register}
          {src2imp_ops : RegAlloc.map.ops src2imp}.

  Instance mmio_params: MMIO.parameters := {
    byte_ok := KamiWord.word8ok;
    word_ok := @KamiWord.wordWok _ (or_introl eq_refl);
  }.

  (* TODO why is this needed to make the Check below pass? *)
  Instance processor_mmio': MinimalMMIO.ExtSpec := @processor_mmio mmio_params.
  Check (_ : PrimitivesParams (MinimalMMIO.free MetricMinimalMMIO.action MetricMinimalMMIO.result)
                              MetricRiscvMachine).

  Instance pipeline_params: PipelineWithRename.Pipeline.parameters. refine ({|
    Pipeline.FlatToRiscvDef_params := compilation_params;
    Pipeline.ext_spec := bedrock2_interact;
    Pipeline.ext_guarantee mach := map.undef_on mach.(getMem) isMMIOAddr;
  |}).
  Defined.

  Existing Instance MetricMinimalMMIO.MetricMinimalMMIOSatisfiesPrimitives.

  Instance pipeline_assumptions: @PipelineWithRename.Pipeline.assumptions pipeline_params.
    refine ({|
      Pipeline.PR := _ ; (*MetricMinimalMMIO.MetricMinimalMMIOSatisfiesPrimitives;*)
      Pipeline.FlatToRiscv_hyps := _; (*MMIO.FlatToRiscv_hyps*)
      Pipeline.src2imp_ok := _;
      Pipeline.Registers_ok := _;
      (* wait until we know if ext_spec will be in monad style or postcond style *)
      Pipeline.ext_spec_ok := match TODO with end;
    |}).
  - case TODO.
  - refine (_ MetricMinimalMMIO.MetricMinimalMMIOSatisfiesPrimitives).
    match goal with
    | |- _ ?A -> _ ?B => assert (A = B)
    end.
    {
      unfold MetricMinimalMMIO.MetricMinimalMMIOPrimitivesParams, Pipeline.PRParams.
      unfold pipeline_params.
      unfold   MetricMinimalMMIO.MetricMinimalMMIOPrimitivesParams.
      reflexivity.
    }
    rewrite H.
    exact id.
  - case TODO.
  Defined.

  Definition KamiMachine: Type := KamiRiscv.KamiMachine.

  Context (instrMemSizeLg: Z).
  Hypothesis instrMemSizeLg_bounds: 3 <= instrMemSizeLg <= 30.

  Lemma HbtbAddr: BinInt.Z.to_nat instrMemSizeLg = (3 + (BinInt.Z.to_nat instrMemSizeLg - 3))%nat.
  Proof. PreOmega.zify; rewrite ?Z2Nat.id in *; blia. Qed.

  Lemma HinstrMemBound: instrMemSizeLg <= 30.
  Proof. exact (proj2 instrMemSizeLg_bounds). Qed.

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
          (otherMemInit: mem)
          (ml: MemoryLayout 32)
          (mlOk: MemoryLayoutOk ml).

  Hypothesis instrMemSizeLg_agrees_with_ml:
    word.sub ml.(code_pastend) ml.(code_start) = word.of_Z instrMemSizeLg.

  (* goodTrace in terms of "exchange format" (list Event).
     Only holds at the beginning/end of each loop iteration,
     will be transformed into "exists suffix, ..." form later *)
  Definition goodTraceE(t: list Event): Prop :=
    exists bedrockTrace, traces_related t bedrockTrace /\ spec.(goodTrace) bedrockTrace.

  (* compiles the section var "prog : Program cmd" from bedrock2 down to a kami instruction mem *)
  Definition compile_to_kami: kword instrMemSizeLg -> kword 32.
  Admitted.

  Definition kamiMemInit :=
    memInit instrMemSizeLg compile_to_kami otherMemInit.

  (* TODO can we do with fewer explicit implicit arguments? *)
  Definition p4mm: Kami.Syntax.Modules :=
    KamiRiscv.p4mm instrMemSizeLg (proj1 instrMemSizeLg_bounds)
                   (proj2 instrMemSizeLg_bounds)
                   compile_to_kami otherMemInit.

  Definition kamiMemToBedrockMem(km: SC.MemInit (Z.to_nat width) IsaRv32.rv32DataBytes): mem.
    case TODO.
  Defined.

  Definition bedrock2Inv := (fun t' m' l' => spec.(isReady) t' m' l' /\ spec.(goodTrace) t').

  (* end to end, but still generic over the program
     TODO also write instantiations where the program is fixed, to reduce number of hypotheses *)
  Lemma end2end:
    forall funspecs,
      (forall m l, WeakestPrecondition.cmd (p := strname_sem) funspecs prog.(init_code) [] m l
                   bedrock2Inv) ->
      (forall t m l,
          bedrock2Inv t m l ->
          WeakestPrecondition.cmd (p := strname_sem)
                                  funspecs prog.(loop_body) t m l bedrock2Inv) ->
    (* TODO more hypotheses might be needed *)
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
    intros *. intros Establish Preserve. intros *. intros B.

    set (traceProp := fun (t: list Event) =>
                        exists (suffix: list Event), goodTraceE (suffix ++ t)).
    change (exists t' : list Event,
               KamiLabelSeqR t t' /\ traceProp t').

    (* stack of proofs, bottom-up: *)

    (* 1) Kami pipelined processor to riscv-coq *)
    pose proof @riscv_to_kamiImplProcessor as P1.
    specialize_first P1 traceProp.
    specialize_first P1 (ll_inv spec ml).
    specialize_first P1 B.
    (* destruct spec. TODO why "Error: sat is already used." ?? *)

    (* 2) riscv-coq to bedrock2 semantics *)
    pose proof pipeline_proofs as P2.
    specialize_first P2 prog.
    specialize_first P2 spec.
    specialize_first P2 ml.
    edestruct P2 as [ P2establish [P2preserve P2use] ]. {
      (* 3) bedrock2 semantics to bedrock2 program logic *)
      constructor.
      - intros.
        pose proof (@program_logic_sound strname_sem) as P3init.
        specialize_first Establish (kamiMemToBedrockMem kamiMemInit).
        assert (initialLocals: @locals strname_sem) by case TODO. (* obtain from kami *)
        specialize_first Establish initialLocals.
        specialize_first P3init Establish.
        replace m0 with (kamiMemToBedrockMem kamiMemInit) by case TODO.
        replace l0 with initialLocals by case TODO.
        eapply P3init. 1,2: case TODO.
      - intros.
        pose proof (@program_logic_sound strname_sem) as P3loop.
        eapply P3loop.
        3: eapply Preserve.
        3: split; assumption.
        1,2: case TODO.
    }

    eapply P1.
    - apply (@MetricMinimalMMIO.MetricMinimalMMIOSatisfiesPrimitives
                (@Words32 mmio_params)
                (@MMIO.mem mmio_params) (@MMIO.locals mmio_params)).
    - (* establish *)
      intros.
      eapply P2establish.
      case TODO.
    - (* preserve *)
      intros.
      refine (P2preserve _ _). assumption.
    - (* use *)
      intros *. intro Inv.
      subst traceProp. simpl.
      specialize_first P2use Inv.
      destruct P2use as [suff Good].
      unfold goodTrace.
      (* given the bedrock2 trace "suff ++ getLog m", produce exchange format trace *)
      case TODO.

      Grab Existential Variables.
      1: exact m0RV.
  Qed.

End Connect.

(*
About end2end.
Print Assumptions end2end.
*)
