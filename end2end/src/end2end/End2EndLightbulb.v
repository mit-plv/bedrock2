Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.forward.
Require Import bedrock2.Syntax.
Require Import compiler.PipelineWithRename.
Require Import bedrock2Examples.lightbulb bedrock2Examples.lightbulb_spec.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.
Require Import compiler.Simp.
Require Import compiler.ExprImpEventLoopSpec.
Require Import compiler.MemoryLayout.
Require Import end2end.End2EndPipeline.
Require Import end2end.Bedrock2SemanticsForKami. (* TODO why is the ok instance in that file not needed? *)
Require        riscv.Utility.InstructionNotations.
Require        bedrock2.Hexdump.

Open Scope Z_scope.
Open Scope string_scope.

Definition instrMemSizeLg: Z := 10. (* TODO is this enough? *)
Lemma instrMemSizeLg_bounds : 3 <= instrMemSizeLg <= 30. Proof. cbv. intuition discriminate. Qed.
Definition dataMemSize: Z := (16-4)*2^10.

(* TODO adjust these numbers *)
Definition ml: MemoryLayout Semantics.width := {|
  MemoryLayout.code_start    := word.of_Z 0;
  MemoryLayout.code_pastend  := word.of_Z (4*2^10);
  MemoryLayout.heap_start    := word.of_Z (4*2^10);
  MemoryLayout.heap_pastend  := word.of_Z (8*2^10);
  MemoryLayout.stack_start   := word.of_Z (8*2^10);
  MemoryLayout.stack_pastend := word.of_Z (16*2^10);
|}.

Definition buffer_addr: Z := word.unsigned ml.(heap_start).

Local Instance parameters : FE310CSemantics.parameters := ltac:(esplit; exact _).

Definition traceOfBoot (t : list (lightbulb_spec.OP Semantics.word)) : Prop :=
  lightbulb_boot_success FE310CSemantics.parameters.word t
  \/  lan9250_boot_timeout FE310CSemantics.parameters.word t
  \/ (any +++ spi_timeout Semantics.word) t.

Definition traceOfOneInteraction: list (lightbulb_spec.OP Semantics.word) -> Prop :=
  (fun t => exists packet cmd, (lan9250_recv _ packet +++ gpio_set _ 23 cmd) t /\
                               lightbulb_packet_rep cmd packet) |||
  (fun t => exists packet, lan9250_recv _ packet t /\
                           ~ (exists cmd : bool, lightbulb_packet_rep cmd packet)) |||
  (lightbulb_spec.lan9250_recv_no_packet _) |||
  (lightbulb_spec.lan9250_recv_packet_too_long _) |||
  (any +++ (lightbulb_spec.spi_timeout _)).

Definition goodHlTrace: list (lightbulb_spec.OP Semantics.word) -> Prop :=
  traceOfBoot +++ traceOfOneInteraction ^*.

Definition spec: ProgramSpec := {|
  datamem_start := ml.(heap_start);
  datamem_pastend := ml.(heap_pastend);
  goodTrace iol := exists ioh, SPI.mmio_trace_abstraction_relation ioh iol /\
                               goodHlTrace ioh;
  isReady t m := exists buf R,
    (Separation.sep (Array.array Scalars.scalar8 (word.of_Z 1) (word.of_Z buffer_addr) buf) R) m /\
    Z.of_nat (Datatypes.length buf) = 1520;
|}.

Lemma mlOk: MemoryLayoutOk ml.
Proof.
  constructor; try reflexivity; try (cbv; discriminate).
Qed.

Definition p4mm memSizeLg (memInit: Syntax.Vec (Syntax.ConstT (Syntax.Bit MemTypes.BitsPerByte))
                                               (Z.to_nat memSizeLg)): Kami.Syntax.Modules :=
  p4mm instrMemSizeLg _ memInit instrMemSizeLg_bounds.

From coqutil Require Import Z_keyed_SortedListMap.

Local Existing Instance SortedListString.map.
Local Existing Instance SortedListString.ok.

Instance pipeline_params: PipelineWithRename.Pipeline.parameters :=
  @End2EndPipeline.pipeline_params
    (Zkeyed_map FE310CSemantics.parameters.word)
    (Zkeyed_map_ok FE310CSemantics.parameters.word)
    FE310CSemantics.parameters.mem
    FE310CSemantics.parameters.mem_ok.

Instance semantics_parameters_ok : Semantics.parameters_ok
  (FlattenExprDef.FlattenExpr.mk_Semantics_params
     PipelineWithRename.Pipeline.FlattenExpr_parameters).
Proof.
  eapply @FlattenExprDef.FlattenExpr.mk_Semantics_params_ok.
  eapply @PipelineWithRename.FlattenExpr_hyps.
  eapply @pipeline_assumptions; try exact _.
Qed.

Local Definition parameters_match :
  (FlattenExprDef.FlattenExpr.mk_Semantics_params
    PipelineWithRename.Pipeline.FlattenExpr_parameters)
  = FE310CSemantics.semantics_parameters := eq_refl.

Open Scope string_scope.

Definition init :=
  ("init", ([]: list string, []: list string,
           (cmd.call ["err"] "lightbulb_init" []))).

Definition loop :=
  ("loop", ([]: list string, []: list string,
           (cmd.call ["err"] "lightbulb_loop" [expr.literal buffer_addr]))).

Definition funimplsList := init :: loop :: lightbulb.function_impls.
Definition prog := map.of_list funimplsList.

Definition lightbulb_insts_unevaluated: option (list Decode.Instruction * FlatToRiscvCommon.funname_env Z) :=
  CompilerInvariant.compile_prog ml prog.

(* Before running this command, it might be a good idea to do
   "Print Assumptions lightbulb_insts_unevaluated."
   and to check if there are any axioms which could block the computation. *)
Definition lightbulb_insts: list Decode.Instruction.
  let r := eval cbv in lightbulb_insts_unevaluated in set (res := r).
  match goal with
  | res := Some (?x, _) |- _ => exact x
  end.
Defined.

Definition function_positions: FlatToRiscvCommon.funname_env Z.
  let r := eval cbv in lightbulb_insts_unevaluated in set (res := r).
  match goal with
  | res := Some (_, ?x) |- _ => exact x
  end.
Defined.

Definition compilation_result:
  CompilerInvariant.compile_prog ml prog = Some (lightbulb_insts, function_positions).
Proof. reflexivity. Qed.

Module PrintProgram.
  Import riscv.Utility.InstructionNotations.
  Import bedrock2.NotationsCustomEntry.
  Import bedrock2.Hexdump.
  Local Open Scope hexdump_scope.
  Set Printing Width 108.

  Goal True.
    pose (SortedList.value function_positions) as symbols.
    cbv in symbols.

    pose lightbulb_insts as p.
    unfold lightbulb_insts in p.

    let x := eval cbv in (instrencode lightbulb_insts) in idtac (* x *).
  Abort.
  Unset Printing Width.
End PrintProgram.

Lemma iohi_to_iolo: forall ioh (iomid: list RiscvMachine.LogItem),
    Forall2 SPI.mmio_event_abstraction_relation ioh iomid ->
    exists iolo : list KamiRiscv.Event, KamiRiscv.traces_related iolo iomid.
Proof.
  induction ioh; intros.
  - simp. exists nil. constructor.
  - destruct iomid; try solve [inversion H].
    simp.
    specialize IHioh with (1 := H5). simp. clear H5.
    unfold SPI.mmio_event_abstraction_relation in *.
    destruct H3; simp; eexists; constructor; try eassumption; constructor.
Qed.

Lemma funs_valid: ExprImp.valid_funs (map.of_list funimplsList).
Proof.
  unfold ExprImp.valid_funs, ExprImp.valid_fun.
  intros.
  set (funnames := (List.map fst funimplsList)). cbv in funnames.
  destruct (List.In_dec String.string_dec f funnames).
  - subst funnames. simpl in i.
    repeat destruct i as [i | i]; try contradiction; subst f; vm_compute in H; simp; split;
      repeat constructor; intro C; simpl in C; intuition discriminate.
  - exfalso. apply n; clear n.  change funnames with (List.map fst funimplsList).
    clear funnames.
    generalize dependent funimplsList. induction l; intros.
    + simpl in H. discriminate.
    + destruct a. unfold map.of_list in H. rewrite map.get_put_dec in H.
      destruct_one_match_hyp.
      * simp. subst. simpl. auto.
      * simpl. right. eapply IHl. exact H.
Qed.

Lemma end2end_lightbulb:
  forall (memInit: Syntax.Vec (Syntax.ConstT (Syntax.Bit MemTypes.BitsPerByte))
                              (Z.to_nat KamiProc.width))
         (t: Kami.Semantics.LabelSeqT) (mFinal: KamiRiscv.KamiImplMachine),
    kami_mem_contains_bytes (instrencode lightbulb_insts) (code_start ml) memInit ->
    Semantics.Behavior (p4mm _ memInit) mFinal t ->
    exists t': list KamiRiscv.Event,
      KamiRiscv.KamiLabelSeqR t t' /\
      (exists (suffix : list KamiRiscv.Event) (bedrockTrace : list RiscvMachine.LogItem),
          KamiRiscv.traces_related (suffix ++ t') bedrockTrace /\
          (exists ioh : list (lightbulb_spec.OP _),
              SPI.mmio_trace_abstraction_relation(p:=parameters) ioh bedrockTrace /\ goodHlTrace ioh)).
Proof.
  (* Fail eapply @end2end. unification only works after some specialization *)
  pose proof @end2end as Q.
  specialize_first Q spec.
  specialize_first Q mlOk.
  specialize_first Q instrMemSizeLg_bounds.
  intros *. intro KB.
  specialize_first Q memInit.
  specialize_first Q funimplsList.
  specialize_first Q open_constr:(eq_refl).
  specialize_first Q open_constr:(eq_refl).
  specialize_first Q open_constr:(eq_refl).
  specialize_first Q KB.
  specialize_first Q compilation_result.

  unfold bedrock2Inv, goodTraceE, isReady, goodTrace, spec in *.
  eapply Q; clear Q.
  - cbv. repeat constructor; cbv; intros; intuition congruence.
  - intros. clear KB memInit. simp.
    unfold SPI.mmio_trace_abstraction_relation in *.
    unfold id in *.
    eauto using iohi_to_iolo.
  - reflexivity.
  - (* establish invariant *)
    repeat ProgramLogic.straightline.
    refine (WeakestPreconditionProperties.Proper_call _ _ _ _ _ _ _ _ _);
      [|exact (link_lightbulb_init m nil)].

    intros ? ? ? ?.
    repeat ProgramLogic.straightline.
    unfold mem_available, hl_inv, isReady, goodTrace, goodHlTrace, traceOfBoot, buffer_addr, ml, code_start, heap_start, heap_pastend in *; Simp.simp.

    split.
    1: {
      change (BinIntDef.Z.of_nat (Datatypes.length anybytes) = 4096) in Hl.
      rewrite word.of_Z_unsigned.
      rewrite <-(firstn_skipn 1520 anybytes) in Hr.
      SeparationLogic.seprewrite_in @Array.bytearray_append Hr.
      SeparationLogic.seprewrite_in @SeparationLogic.sep_emp_True_r Hr0.
      eexists _, _; split;
        [exact Hr1|rewrite List.length_firstn_inbounds; blia]. }
    subst a; rewrite app_nil_r.
    eexists; split; eauto.
    change x1 with (List.app nil x1).
    eapply concat_app, kleene_empty.
    destruct H4; Simp.simp; eauto.
    destruct H; Simp.simp; eauto.

  - reflexivity.
  - (* preserve invariant *)
    intros.
    specialize (H ltac:(repeat constructor)).
    unfold hl_inv, isReady, goodTrace, goodHlTrace, traceOfOneInteraction in *.
    Simp.simp.
    repeat ProgramLogic.straightline.
    pose proof link_lightbulb_loop as P.
    cbv [spec_of_lightbulb_loop] in P.
    specialize_first P Hll.
    specialize_first P t0.
    specialize_first P Hlr.
    refine (WeakestPreconditionProperties.Proper_call _ _ _ _ _ _ _ _ _);
      [|exact P]; clear P.

    intros ? ? ? ?.
    Simp.simp.
    repeat ProgramLogic.straightline.
    split; eauto.
    destruct Hrr0rr; Simp.simp;
      (eexists; split; [eapply Forall2_app; eauto|]).
    1,2: apply concat_kleene_r_app; eauto; Simp.simp.
    { left. left. left. left. eauto. }
    destruct H; Simp.simp.
    { left. left. left. right. eauto. }
    destruct H; Simp.simp.
    { left. left. right. eauto. }
    destruct H; Simp.simp.
    { left. right. eauto. }
    right. eauto.

  - exact funs_valid.
Time Qed. (* takes more than 25s *)
