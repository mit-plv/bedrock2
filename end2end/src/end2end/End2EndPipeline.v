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
Require Import processor.KamiRiscvStep.
Require Import processor.KamiRiscv.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import compiler.PipelineWithRename.
Require Import compilerExamples.MMIO.
Require Import riscv.Platform.FE310ExtSpec.
Require Import compiler.FlatToRiscvDef.
Require Import coqutil.Tactics.rdelta.
Require Import end2end.KamiRiscvWordProperties.
Require Import bedrock2.WeakestPreconditionProperties.
Require Import compiler.SeparationLogic.
Require Import compiler.ToplevelLoop.
Require Import compiler.CompilerInvariant.
Require Import compiler.ExprImpEventLoopSpec.

Local Open Scope Z_scope.

Local Axiom TODO_initmem : False.

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

(* TODO these definitions should be in KamiRiscv.v: *)

Definition kami_mem_contains_bytes(bs: list Coq.Init.Byte.byte){memSizeLg}(from: Utility.word)
           (mem: Syntax.Vec (Syntax.ConstT (Syntax.Bit MemTypes.BitsPerByte)) memSizeLg): Prop :=
  forall b n,
    nth_error bs n = Some b ->
    Word.natToWord 8 (Byte.to_nat b)
    = Semantics.evalConstT (Syntax.ConstVector mem)
                           (Semantics.evalZeroExtendTrunc memSizeLg (Word.wplus from (Word.natToWord _ n))).

Section Move.
  Context {mem: map.map Utility.word byte}.
  Context (memSizeLg: Z).
  Context (memInit: Syntax.Vec (Syntax.ConstT (Syntax.Bit MemTypes.BitsPerByte))
                               (Z.to_nat memSizeLg)).

  Definition get_kamiMemInit(n: nat): Byte.byte :=
    byte.of_Z (Kami.Lib.Word.uwordToZ
                 (Kami.Semantics.evalConstT (kamiMemInit _ memInit) (Kami.Lib.Word.natToWord _ n))).

  Definition riscvMemInit_range(from len: nat): mem := map.of_list (List.map
    (fun i : nat => (word.of_Z (Z.of_nat i), get_kamiMemInit i))
    (seq from len)).

  Definition riscvMemInit_values(from len: nat): list byte :=
    List.map get_kamiMemInit (seq from len).

  Definition riscvMemInit: mem := riscvMemInit_range 0 (2 ^ Z.to_nat memSizeLg).
End Move.

(* TODO remove once moved to KamiRiscv.v *)
Goal @riscvMemInit = @KamiRiscv.riscvMemInit. Proof. reflexivity. Qed.

Section Connect.

  Context (instrMemSizeLg memSizeLg stack_size_in_bytes: Z).

  Definition ml: MemoryLayout := {|
    code_start := word.of_Z 0;
    code_pastend := word.of_Z (2 ^ (2 + instrMemSizeLg));
    heap_start := word.of_Z (2 ^ (2 + instrMemSizeLg));
    heap_pastend := word.of_Z (2 ^ memSizeLg - stack_size_in_bytes);
    stack_start := word.of_Z (2 ^ memSizeLg - stack_size_in_bytes);
    stack_pastend := word.of_Z (2 ^ memSizeLg);
  |}.

  Context (memInit: Syntax.Vec (Syntax.ConstT (Syntax.Bit MemTypes.BitsPerByte))
                               (Z.to_nat memSizeLg)).

  Hypotheses (instrMemSizeLg_bounds: 3 <= instrMemSizeLg <= 30)
             (Hkmem: 2 + instrMemSizeLg < memSizeLg <= 16).

  Lemma memSizeLg_width_trivial: memSizeLg <= 32. Proof. Lia.lia. Qed.

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

  Add Ring wring : (word.ring_theory (word := Utility.word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := Utility.word)),
       constants [word_cst]).

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
          (funimplsList: list (string * (list string * list string * cmd))).

  Hypothesis heap_start_agree: spec.(datamem_start) = ml.(heap_start).
  Hypothesis heap_pastend_agree: spec.(datamem_pastend) = ml.(heap_pastend).
  Hypothesis stack_size_div: stack_size_in_bytes mod bytes_per_word = 0.
  Hypothesis stack_size_bounds: 0 <= stack_size_in_bytes <= 2 ^ memSizeLg - 2 ^ (2 + instrMemSizeLg).

  Lemma mlOk: MemoryLayoutOk ml.
  Proof.
    constructor;
      unfold ml, code_start, code_pastend, heap_start, heap_pastend, stack_start, stack_pastend.
    - reflexivity.
    - rewrite word.unsigned_of_Z.
      unfold word.wrap.
      etransitivity. 1: exact (mod_2width_mod_bytes_per_word (2 ^ memSizeLg - stack_size_in_bytes)).
      change bytes_per_word with 4.
      apply mod4_0.mod4_0_sub.
      + replace memSizeLg with (memSizeLg - 2 + 2) by blia.
        rewrite Z.pow_add_r by blia.
        apply mod4_0.mod4_mul4_r.
      + exact stack_size_div.
    - rewrite word.unsigned_of_Z.
      unfold word.wrap.
      etransitivity. 1: exact (mod_2width_mod_bytes_per_word (2 ^ memSizeLg)).
      replace memSizeLg with (memSizeLg - 2 + 2) by blia.
      rewrite Z.pow_add_r by blia.
      apply mod4_0.mod4_mul4_r.
    - rewrite word.unsigned_of_Z. change (word.wrap 0) with 0.
      eapply proj1. eapply word.unsigned_range.
    - reflexivity.
    - rewrite ?word.unsigned_of_Z. unfold word.wrap.
      pose proof (Z.pow_nonneg 2 (2 + instrMemSizeLg)).
      change width with 32 in *.
      assert (2 ^ memSizeLg < 2 ^ 32). {
        apply Z.pow_lt_mono_r; blia.
      }
      rewrite ?Z.mod_small; try split; try apply Z.pow_nonneg; try blia.
    - reflexivity.
    - rewrite ?word.unsigned_of_Z. unfold word.wrap.
      pose proof (Z.pow_nonneg 2 (2 + instrMemSizeLg)).
      change width with 32 in *.
      assert (2 ^ memSizeLg < 2 ^ 32). {
        apply Z.pow_lt_mono_r; blia.
      }
      rewrite ?Z.mod_small; try split; try apply Z.pow_nonneg; try blia.
    Qed.

  Hypothesis funimplsList_NoDup: NoDup (List.map fst funimplsList).

  (* goodTrace in terms of "exchange format" (list Event).
     Only holds at the beginning/end of each loop iteration,
     will be transformed into "exists suffix, ..." form later *)
  Definition goodTraceE(t: list Event): Prop :=
    exists bedrockTrace, traces_related t bedrockTrace /\ spec.(goodTrace) bedrockTrace.

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
    word.unsigned (code_start ml) + Z.of_nat (Datatypes.length (instrencode instrs)) <=
      word.unsigned (code_pastend ml) ->
    Forall (fun i : Instruction => verify i iset) instrs ->
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
    intros *. intros GetInit Establish GetLoop Preserve. intros *. intros C L F V M. intros *. intros B.

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
    specialize_first P1 memSizeLg_width_trivial.
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
      + assumption.
      + assumption.
      + assumption.
      + assumption.
      + pose proof (mem_ok : @map.ok (@Semantics.word strname_sem) byte (@Semantics.mem strname_sem)).
        pose proof word.eqb_spec.
        cbv [imem mem_available].

        eapply Proper_iff1_iff1; [|reflexivity..|].
        { progress repeat rewrite ?sep_ex1_r, ?sep_ex1_l; reflexivity. }
        exists (riscvMemInit_values _ memInit (Z.to_nat (2 ^ memSizeLg - stack_size_in_bytes))
                                              (Z.to_nat stack_size_in_bytes)).
         eapply Proper_iff1_iff1; [|reflexivity..|].
        { progress repeat rewrite ?sep_ex1_r, ?sep_ex1_l; reflexivity. }
        exists (riscvMemInit_values _ memInit (Z.to_nat (2 ^ (2 + instrMemSizeLg)))
                       (Z.to_nat (2 ^ memSizeLg - stack_size_in_bytes - 2 ^ (2 + instrMemSizeLg)))).
        eapply Proper_iff1_iff1; [|reflexivity..|].
        { progress repeat rewrite ?sep_ex1_r, ?sep_ex1_l; reflexivity. }
        exists (riscvMemInit_values _ memInit (Datatypes.length (instrencode instrs))
                       (Z.to_nat (2 ^ (2 + instrMemSizeLg)) - (Datatypes.length (instrencode instrs)))).
        eapply Proper_iff1_iff1; [|reflexivity..|].
        { progress repeat rewrite ?sep_emp_2, ?sep_emp_l, ?sep_emp_r; reflexivity. }
        eapply sep_emp_l; split.
        2: eapply sep_assoc; eapply sep_emp_l; split.
        3: eapply Proper_iff1_iff1; [|reflexivity..|].
        3: { progress repeat rewrite ?sep_assoc, ?sep_emp_2, ?sep_emp_l, ?sep_emp_r; reflexivity. }
        3: eapply sep_emp_l; split.

        all : cycle 3.
        Unshelve.
        all : case TODO_initmem .

      + change (word.unsigned (code_start ml)) with 0.
        assert (Hend: code_pastend ml = word.of_Z (2 ^ (2 + instrMemSizeLg))) by reflexivity.
        setoid_rewrite Hend.
        rewrite word.unsigned_of_Z.
        cbv [word.wrap].
        rewrite Z.mod_small by (split; [apply Z.pow_nonneg; Lia.lia
                                       |apply Z.pow_lt_mono_r; cbn; Lia.lia]).
        assumption.
      + reflexivity.
      + reflexivity.
      + unfold FlatToRiscvCommon.regs_initialized. intros.
        match goal with
        | |- exists _, ?x = Some _ => destr x; [eauto|exfalso]
        end.
        match goal with
        | H: forall _, _ -> _ <> None |- _ => eapply H; eauto
        end.
      + reflexivity.
      + simpl. split.
        * apply riscv_init_memory_undef_on_MMIO with (instrMemSizeLg0:= instrMemSizeLg).
          { apply instrMemSizeLg_bounds. }
          { apply Hkmem. }
          { cbv [KamiProc.width]; Lia.lia. }
          { apply Hkmem. }
          { assumption. }
        * assumption.
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
