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
Local Axiom TODO_andres: False.

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

Lemma relate_concat: forall ioh1 ioh2 iol1 iol2,
    SPI.mmio_trace_abstraction_relation ioh1 iol1 ->
    SPI.mmio_trace_abstraction_relation ioh2 iol2 ->
    SPI.mmio_trace_abstraction_relation  (ioh2 ++ ioh1) (iol2 ++ iol1)%list.
Proof.
  cbv [SPI.mmio_trace_abstraction_relation SPI.mmio_trace_abstraction_relation id].
  eauto using Forall2_app.
Qed.

Lemma relate_nil:  SPI.mmio_trace_abstraction_relation [] [].
Proof.
  cbv [SPI.mmio_trace_abstraction_relation id].
  eauto using Forall2_nil.
Qed.

Lemma goodHlTrace_addOne: forall iohNew ioh,
    traceOfOneInteraction iohNew ->
    goodHlTrace ioh ->
    goodHlTrace (iohNew ++ ioh).
Proof.
  cbv [goodHlTrace].
  intros ? ? ? (?&?&?&?&?); subst.
  rewrite app_assoc.
  eapply concat_app, kleene_app; eauto.
  rewrite <-app_nil_l; eauto using kleene_step, kleene_empty.
Qed.

Ltac destr :=
  repeat match goal with
         | A: exists x, _ |- _ => let x' := fresh x in destruct A as [x' ?]
         | A: _ /\ _ |- _ => destruct A as [? ?]
         end.

Definition p4mm memSizeLg (memInit: Syntax.Vec (Syntax.ConstT (Syntax.Bit MemTypes.BitsPerByte))
                                               (Z.to_nat memSizeLg)): Kami.Syntax.Modules :=
  p4mm instrMemSizeLg _ memInit instrMemSizeLg_bounds.

From coqutil Require Import Z_keyed_SortedListMap.

Local Existing Instance SortedListString.map.
Local Existing Instance SortedListString.ok.

Instance pipeline_params: PipelineWithRename.Pipeline.parameters.
eapply @End2EndPipeline.pipeline_params; try exact _.
Defined.

Instance semantics_parameters_ok : Semantics.parameters_ok
  (FlattenExprDef.FlattenExpr.mk_Semantics_params
     PipelineWithRename.Pipeline.FlattenExpr_parameters).
Proof.
  eapply @FlattenExprDef.FlattenExpr.mk_Semantics_params_ok.
  eapply @PipelineWithRename.FlattenExpr_hyps.
  eapply @pipeline_assumptions; try exact _.
Qed.

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
  specialize_first Q compilation_result.
  specialize_first Q spec.
  specialize_first Q mlOk.
  specialize_first Q instrMemSizeLg_bounds.
  intros *. intro KB.
  specialize_first Q memInit.
  specialize_first Q KB.

  unfold bedrock2Inv, goodTraceE, isReady, goodTrace, spec in *.
  eapply Q; clear Q.
  - reflexivity.
  - cbv. repeat constructor; cbv; intros; intuition congruence.
  - intros. clear KB memInit. simp.
    unfold SPI.mmio_trace_abstraction_relation in *.
    unfold id in *.
    eauto using iohi_to_iolo.
  - reflexivity.
  - (* establish invariant *)
    intros.
    repeat ProgramLogic.straightline.
    subst args.
    eapply WeakestPreconditionProperties.Proper_call.
    2: {
      pose proof link_lightbulb_init as P.
      cbv [spec_of_lightbulb_init] in P.
      specialize (P m nil).
      (*
      subst a.
      Time rewrite app_nil_r. (* 1.7s*)
      eexists _; split; [eassumption|].
      rename x1 into TRACE.
      cbv [relate_lightbulb_trace_to_bedrock goodHlTrace id].
      assert (traceOfBoot TRACE) by
        (cbv [traceOfBoot]; destruct H3 as [[]|[[]|[]]]; eauto); clear H3.
      revert H; case TODO_andres.
      *)
      case TODO_andres. (* bridge between "init" and "init_loop" *)
    }
    intros ? ? ? ?.
    case TODO_andres.
  - reflexivity.
  - (* preserve invariant *)
    intros.
    unfold hl_inv, goodTrace, isReady in *. specialize (H (bedrock2.MetricLogging.mkMetricLog 0 0 0 0)).
    (* TODO make Simp.simp work here *)
    destruct H as [ [ buf [R [Sep L] ] ] H ].
    destruct H as [ioh [Rel G] ].
    pose proof link_lightbulb_loop as P.
    cbv [spec_of_lightbulb_loop] in P.
    specialize_first P Sep.
    specialize_first P L.
    repeat ProgramLogic.straightline.
    refine (WeakestPreconditionProperties.Proper_call _ _ _ _ _ _ _ _ _); cycle 1.
    + eapply P.
    + cbv [Morphisms.Proper Morphisms.pointwise_relation Morphisms.respectful Basics.impl].
      intros ? ? ? ?.
      (*
      destruct H3 as [ C | [C | [C | [C | C ] ] ] ]; (split; [|reflexivity]);
        destr; eexists (ioh0 ++ ioh)%list;
          (split;
           [ eapply relate_concat; assumption
           | apply goodHlTrace_addOne;
             [unfold traceOfOneInteraction, choice; eauto 10
             | exact G]]). *)
      case TODO_andres.
  - exact funs_valid.

    Unshelve.
    all: try intros; exact True.
Time Qed. (* takes more than 150s *)
