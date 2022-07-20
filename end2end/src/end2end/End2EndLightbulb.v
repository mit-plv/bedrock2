Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.forward.
Require Import bedrock2.Syntax.
Require Import compiler.Pipeline.
Require Import bedrock2Examples.lightbulb bedrock2Examples.lightbulb_spec.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.
Require Import coqutil.Tactics.Simp.
Require Import compiler.ExprImpEventLoopSpec.
Require Import compiler.MemoryLayout.
Require Import end2end.End2EndPipeline.
Require Import end2end.Bedrock2SemanticsForKami. (* TODO why is the ok instance in that file not needed? *)
Require        riscv.Utility.InstructionNotations.
Require        bedrock2.Hexdump.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import Ltac2.Ltac2. Set Default Proof Mode "Classic".

Open Scope Z_scope.
Open Scope string_scope.

Definition instrMemSizeLg: Z := 10. (* means 2^12 bytes *) (* TODO is this enough? *)
Lemma instrMemSizeLg_bounds : 3 <= instrMemSizeLg <= 30. Proof. cbv. intuition discriminate. Qed.

Definition memSizeLg: Z := 13.
Lemma memSizeLg_valid : instrMemSizeLg + 2 < memSizeLg <= 16.
Proof. cbv. intuition discriminate. Qed.

Definition stack_size_in_bytes: Z := 2 ^ 11.

Definition ml: MemoryLayout :=
  End2EndPipeline.ml instrMemSizeLg memSizeLg stack_size_in_bytes.

Remark this_is_the_value_of_ml: ml = {|
  MemoryLayout.code_start    := word.of_Z 0;
  MemoryLayout.code_pastend  := word.of_Z (2 ^ 12);
  MemoryLayout.heap_start    := word.of_Z (2 ^ 12);
  MemoryLayout.heap_pastend  := word.of_Z (2 ^ 12 + 2 ^ 11);
  MemoryLayout.stack_start   := word.of_Z (2 ^ 12 + 2 ^ 11);
  MemoryLayout.stack_pastend := word.of_Z (2 ^ 13);
|}.
Proof. reflexivity. Qed.

Definition buffer_addr: Z := word.unsigned ml.(heap_start).

Definition spec: ProgramSpec := {|
  datamem_start := ml.(heap_start);
  datamem_pastend := ml.(heap_pastend);
  goodTrace iol := exists ioh, SPI.mmio_trace_abstraction_relation ioh iol /\
                               goodHlTrace _ ioh;
  isReady t m := exists buf R,
    (Separation.sep (Array.array Scalars.scalar8 (word.of_Z 1) (word.of_Z buffer_addr) buf) R) m /\
    Z.of_nat (Datatypes.length buf) = 1520;
|}.

Lemma mlOk: MemoryLayoutOk ml.
Proof.
  constructor; try reflexivity; try (cbv; discriminate).
Qed.

Definition p4mm (memInit: Syntax.Vec (Syntax.ConstT (Syntax.Bit MemTypes.BitsPerByte))
                                     (Z.to_nat memSizeLg)): Kami.Syntax.Modules :=
  p4mm instrMemSizeLg _ memInit instrMemSizeLg_bounds.

Open Scope string_scope.

(* note: this function is totally redundant now *)
(* I spent an hour trying to short-circuit it, but failed because loop is not redundant, and loop is not in the enviroenment in which lightbulb_init is proven, and Pipeline wants init proven in the extended environment that includes loop *)
Definition init :=
  ("init", ([]: list string, []: list string,
           (cmd.call [] "lightbulb_init" []))).

Definition loop :=
  ("loop", ([]: list string, []: list string,
           (cmd.call ["err"] "lightbulb_loop" [expr.literal buffer_addr]))).

Definition funimplsList := init :: loop :: lightbulb.function_impls.
Definition prog := map.of_list funimplsList.

(* Before running this command, it might be a good idea to do
   "Print Assumptions lightbulb_insts_unevaluated."
   and to check if there are any axioms which could block the computation. *)
Definition lightbulb_compiled: list Decode.Instruction * SortedListString.map Z * Z.
  let r := eval cbv in (ToplevelLoop.compile_prog MMIO.compile_ext_call ml prog) in
  lazymatch r with
  | Success ?x => exact x
  end.
Defined.

Definition lightbulb_insts: list Decode.Instruction.
  let r := eval cbv delta [lightbulb_compiled] in lightbulb_compiled in
  lazymatch r with
  | (?x, _, _) => exact x
  end.
Defined.

Definition function_positions: SortedListString.map Z.
  let r := eval cbv delta [lightbulb_compiled] in lightbulb_compiled in
  lazymatch r with
  | (_, ?x, _) => exact x
  end.
Defined.

Definition required_stack_space: Z.
  let r := eval cbv delta [lightbulb_compiled] in lightbulb_compiled in
  lazymatch r with
  | (_, _, ?x) => exact x
  end.
Defined.

Definition compilation_result:
  ToplevelLoop.compile_prog MMIO.compile_ext_call ml prog =
  Success (lightbulb_insts, function_positions, required_stack_space).
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

Lemma iohi_to_iolo: forall ioh (iomid: list (RiscvMachine.LogItem (Mem := mem))),
    Forall2 SPI.mmio_event_abstraction_relation ioh iomid ->
    exists iolo : list KamiRiscvStep.Event, KamiRiscvStep.traces_related iolo iomid.
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

Arguments goodHlTrace {_}.

Lemma kami_and_lightbulb_abstract_bedrockTrace_the_same_way:
  forall bedrockTrace (kamiTrace lightbulbTrace : list (string * word * word)),
    SPI.mmio_trace_abstraction_relation lightbulbTrace bedrockTrace ->
    KamiRiscvStep.traces_related kamiTrace bedrockTrace ->
    kamiTrace = lightbulbTrace.
Proof.
  intro l. unfold SPI.mmio_trace_abstraction_relation. induction l; intros.
  - simp. reflexivity.
  - simp. f_equal. 2: eauto.
    inversion H4; inversion H3; simp; reflexivity || discriminate.
Qed.

Definition bytes_at(bs: list Init.Byte.byte)(addr: Z)
           (m: Syntax.Vec (Syntax.ConstT (Syntax.Bit MemTypes.BitsPerByte)) (Z.to_nat memSizeLg)): Prop :=
  @kami_mem_contains_bytes bs 13 (word.of_Z addr) m.

(* it's a prefix in the temporal sense -- since traces grow on the left,
   this definition looks more like a suffix *)
Definition prefix_of{A: Type}(l: list A)(P: list A -> Prop): Prop :=
  exists completion, P (completion ++ l)%list.

Theorem end2end_lightbulb: forall mem0 t state,
  bytes_at (instrencode lightbulb_insts) 0 mem0 ->
  Semantics.Behavior (p4mm mem0) state t ->
  exists t': list (string * word * word),
    KamiRiscv.KamiLabelSeqR t t' /\
    prefix_of t' goodHlTrace.
Proof.
  (* Fail eapply @end2end. unification only works after some specialization *)
  pose proof @end2end as Q.
  specialize_first Q spec.
  specialize_first Q instrMemSizeLg_bounds.
  intros *. intro KB.
  specialize Q with (stack_size_in_bytes := stack_size_in_bytes).
  specialize_first Q mem0.
  specialize_first Q funimplsList.
  specialize_first Q open_constr:(eq_refl).
  specialize_first Q open_constr:(eq_refl).
  specialize_first Q open_constr:(eq_refl).
  specialize_first Q memSizeLg_valid.
  specialize_first Q (Zkeyed_map (KamiWord.word 32)).
  specialize_first Q (Zkeyed_map_ok (KamiWord.word 32)).
  specialize_first Q mem_ok.
  specialize Q with (13 := KB). (* TODO add bigger numbers to coqutil.Tactics.forward.specialize_first *)
  (* specialize_first Q KB. *)
  specialize_first Q compilation_result.

  unfold bedrock2Inv, goodTraceE, isReady, goodTrace, spec in *.
  enough (Semantics.Behavior (p4mm mem0) state t ->
          exists t': list KamiRiscvStep.Event,
            KamiRiscv.KamiLabelSeqR t t' /\
            (exists (suffix : list KamiRiscvStep.Event) (bedrockTrace : list RiscvMachine.LogItem),
                KamiRiscvStep.traces_related (suffix ++ t') bedrockTrace /\
                (exists ioh : list (lightbulb_spec.OP _),
                    SPI.mmio_trace_abstraction_relation ioh bedrockTrace /\
                    goodHlTrace ioh)))
    as A. {
    clear -A.
    intro B. specialize (A B); clear B.
    clear mem0.
    change (OP Consistency.word) with KamiRiscvStep.Event in *.
    unfold KamiRiscvStep.Event, prefix_of in *.
    simp.
    eexists. split. 1: exact Ap0.
    exists suffix.
    erewrite kami_and_lightbulb_abstract_bedrockTrace_the_same_way; eassumption.
  }
  eapply Q; clear Q.
  - cbv. intuition discriminate.
  - clear. cbv.
    repeat econstructor; intro; repeat match goal with H: In _ _|-_=> destruct H end; discriminate.
  - intros. clear KB mem0. simp.
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
    unfold LowerPipeline.mem_available, hl_inv, isReady, goodTrace, goodHlTrace, buffer_addr, ml, End2EndPipeline.ml, code_start, heap_start, heap_pastend, Lift1Prop.ex1 in *; Simp.simp.
    eapply SeparationLogic.sep_emp_l in H.
    (* TODO why does Simp.simp not destruct H if I end the above line by semicolon instead of dot? *)
    Simp.simp.
    rename a0 into anybytes.

    split.
    1: {
      lazymatch goal with
      | A: BinIntDef.Z.of_nat (Datatypes.length anybytes) = ?c |- _ =>
        let c' := eval cbv in c in change (BinIntDef.Z.of_nat (Datatypes.length anybytes) = c') in A
      end.
      rewrite word.of_Z_unsigned.
      rewrite <-(firstn_skipn 1520 anybytes) in Hp1.
      unfold LowerPipeline.ptsto_bytes in Hp1.
      SeparationLogic.seprewrite_in @Array.bytearray_append Hp1.
      SeparationLogic.seprewrite_in @SeparationLogic.sep_emp_True_r Hp1.
      eexists _, _; split;
        [exact Hp1|rewrite List.length_firstn_inbounds; blia]. }
    subst a; rewrite app_nil_r.
    eexists; split; eauto.
    change x0 with (List.app nil x0).
    eapply concat_app, kleene_empty; eassumption.

  - reflexivity.
  - (* preserve invariant *)
    intros.
    specialize (H ltac:(repeat constructor)).
    unfold hl_inv, isReady, goodTrace, goodHlTrace in *.
    Simp.simp.
    repeat ProgramLogic.straightline.
    pose proof link_lightbulb_loop as P.
    cbv [spec_of_lightbulb_loop] in P.
    specialize_first P Hp0p0.
    specialize_first P t0.
    specialize_first P Hp0p1.
    refine (WeakestPreconditionProperties.Proper_call _ _ _ _ _ _ _ _ _);
      [|exact P]; clear P.

    intros ? ? ? ?.
    Simp.simp.
    repeat ProgramLogic.straightline.
    split; eauto.
    unfold existsl, Recv, LightbulbCmd in *.
    destruct Hp1p3p1; Simp.simp;
      (eexists; split; [eapply Forall2_app; eauto|]).
    1,2: apply concat_kleene_r_app; eauto; Simp.simp.
    { unfold "+++" in Hp0|-*. left. left. Simp.simp. eauto 10. }
    destruct H; Simp.simp.
    { left. right. left. left. eauto. }
    destruct H; Simp.simp.
    { right. unfold PollNone. eauto. }
    destruct H; Simp.simp.
    { left. right. left. right. eauto. }
    left. right. right. eauto.

  - vm_compute. intros. discriminate.
  - vm_compute. intros. discriminate.
  - (* Here we prove that all > 700 instructions are valid, using Ltac.
       If this becomes a bottleneck, we'll have to do this in Gallina in the compile function. *)
    unfold lightbulb_insts. repeat (apply Forall_cons || apply Forall_nil).
    all: vm_compute; try intuition discriminate.
  - exact funs_valid.
Time Qed. (* takes more than 25s *)
