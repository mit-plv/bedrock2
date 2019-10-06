Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.forward.
Require Import bedrock2.Syntax.
Require Import bedrock2Examples.lightbulb bedrock2Examples.lightbulb_spec.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.
Require Import compiler.ProgramSpec.
Require Import compiler.MemoryLayout.
Require Import end2end.End2EndPipeline.
Require Import end2end.Bedrock2SemanticsForKami. (* TODO why is the ok instance in that file not needed? *)
Require        riscv.Utility.InstructionNotations.
Require        bedrock2.Hexdump.

Open Scope Z_scope.
Open Scope string_scope.

Definition instrMemSizeLg: Z := 10. (* TODO is this enough? *)
Lemma instrMemSizeLg_bounds : 3 <= instrMemSizeLg <= 30. Proof. cbv. intuition discriminate. Qed.
Definition dataMemSize: Z := 4096.

Definition FunctionImpl: Type :=
  (list string * list string * @cmd (StringNamesSyntax.make BasicCSyntax.StringNames_params)).

Definition funimplsList: list (string * FunctionImpl).
  match type of link_lightbulb with
  | spec_of_iot ?L => exact L
  end.
Defined.

(* TODO adjust these numbers *)
Definition ml: MemoryLayout Semantics.width := {|
  MemoryLayout.code_start    := word.of_Z 0;
  MemoryLayout.code_pastend  := word.of_Z (4*2^10);
  MemoryLayout.heap_start    := word.of_Z (4*2^10);
  MemoryLayout.heap_pastend  := word.of_Z (8*2^10);
  MemoryLayout.stack_start   := word.of_Z (16*2^10);
  MemoryLayout.stack_pastend := word.of_Z (16*2^10);
|}.

Definition buffer_addr: Z := word.unsigned ml.(heap_start).

Definition  init_code := @cmd.skip Semantics.syntax.
Definition loop_body := @cmd.seq Semantics.syntax
     (@cmd.call Semantics.syntax ["res"] "iot" [expr.literal buffer_addr])
     (@cmd.unset Semantics.syntax "res").

Axiom TODO_andres: False.

Definition lightbulb_packet_rep: bool -> list Semantics.byte -> Prop.
  intros command bytes.
  refine (lightbulb_packet_rep command (_ bytes)).
  case TODO_andres.
Defined.

Definition traceOfOneInteraction: list (lightbulb_spec.OP Semantics.word) -> Prop :=
  (fun t => exists packet cmd, (lan9250_recv _ _ packet +++ gpio_set _ 23 cmd) t /\
                               lightbulb_packet_rep cmd packet) |||
  (fun t => exists packet, lan9250_recv _ _ packet t /\
                           ~ (exists cmd : bool, lightbulb_packet_rep cmd packet)) |||
  (lightbulb_spec.lan9250_recv_no_packet _ _) |||
  (lightbulb_spec.lan9250_recv_packet_too_long _ _) |||
  (any +++ (lightbulb_spec.spi_timeout _)).

Definition goodHlTrace: list (lightbulb_spec.OP Semantics.word) -> Prop :=
  traceOfOneInteraction ^*.

Definition relate_lightbulb_trace_to_bedrock(ioh: list (lightbulb_spec.OP Semantics.word))
                                            (iol : Semantics.trace): Prop.
  refine (SPI.mmio_trace_abstraction_relation (_ ioh) (_ iol)).
  all: case TODO_andres.
  (* this should not be needed any more once lightbulb proofs are for generic word *)
Defined.

Definition spec: ProgramSpec := {|
  datamem_start := ml.(heap_start);
  datamem_pastend := ml.(heap_pastend);
  goodTrace iol := exists ioh, relate_lightbulb_trace_to_bedrock ioh iol /\
                               goodHlTrace ioh;
  isReady t m l := exists buf R,
    (Separation.sep (Array.array Scalars.scalar8 (word.of_Z 1) (word.of_Z buffer_addr) buf) R) m /\
    Z.of_nat (Datatypes.length buf) = 1520;
|}.

Lemma mlOk: MemoryLayoutOk ml.
Proof.
  constructor; try reflexivity; try (cbv; discriminate).
Qed.

Lemma link_lightbulb_withCorrectWordInstance:
  forall (p_addr : Semantics.word) (buf : list Semantics.byte) (R : Semantics.mem -> Prop)
         (m : Semantics.mem) (t : Semantics.trace),
    Separation.sep (Array.array Separation.ptsto (word.of_Z 1) p_addr buf) R m ->
    Z.of_nat (Datatypes.length buf) = 1520 ->
    WeakestPrecondition.call
      [iot; recvEthernet; lightbulb; LAN9250.lan9250_readword; SPI.spi_xchg; SPI.spi_read;
         SPI.spi_write] "iot" t m [p_addr]
      (fun (t' : Semantics.trace) (m' : Semantics.mem) (rets : list Semantics.word) =>
      (exists buf, Separation.sep (Array.array Separation.ptsto (word.of_Z 1) p_addr buf) R m' /\
      Z.of_nat (length buf) = 1520) /\
         exists v : Semantics.word,
           rets = [v] /\
           (exists iol,
               t' = (iol ++ t)%list /\
               (exists ioh,
                   relate_lightbulb_trace_to_bedrock ioh iol /\
                   ((exists packet (cmd : bool),
                        (lan9250_recv _ _ packet +++ gpio_set Semantics.word 23 cmd) ioh /\
                        lightbulb_packet_rep cmd packet /\ word.unsigned v = 0) \/
                    (exists packet : list Semantics.byte,
                        lan9250_recv _ _ packet ioh /\
                        ~ (exists cmd : bool, lightbulb_packet_rep cmd packet) /\
                        word.unsigned v = 0) \/
                    (lan9250_recv_no_packet _ _ ioh /\ word.unsigned v = 0) \/
                    (lan9250_recv_packet_too_long _ _ ioh /\ word.unsigned v <> 0) \/
                    ((any +++ spi_timeout Semantics.word) ioh /\ word.unsigned v <> 0))))).
Proof.
  (* replace semantics with FE310CSemantics.parameters. silently fails *)
  Fail pattern semantics.
  pose proof link_lightbulb as P. unfold spec_of_iot in P.
  Fail apply P.
  case TODO_andres.
Qed.

Lemma weaken_call: forall funs fname t m args (post1 post2: _ -> _ -> _ -> Prop),
    WeakestPrecondition.call funs fname t m args post1 ->
    (forall t' m' l', post1 t' m' l' -> post2 t' m' l') ->
    WeakestPrecondition.call funs fname t m args post2.
Proof. case TODO_andres. Qed.

Lemma relate_concat: forall ioh1 ioh2 iol1 iol2,
    relate_lightbulb_trace_to_bedrock ioh1 iol1 ->
    relate_lightbulb_trace_to_bedrock ioh2 iol2 ->
    relate_lightbulb_trace_to_bedrock (ioh2 ++ ioh1) (iol2 ++ iol1)%list.
Proof. case TODO_andres. Qed.

Lemma relate_nil: relate_lightbulb_trace_to_bedrock [] [].
Proof. case TODO_andres. Qed.

Lemma goodHlTrace_addOne: forall iohNew ioh,
    traceOfOneInteraction iohNew ->
    goodHlTrace ioh ->
    goodHlTrace (iohNew ++ ioh).
Proof.
  intros. unfold goodHlTrace. apply kleene_app.
  - change iohNew with ([] ++ iohNew)%list.
    apply kleene_step. 1: assumption. apply kleene_empty.
  - assumption.
Qed.

Ltac destr :=
  repeat match goal with
         | A: exists x, _ |- _ => let x' := fresh x in destruct A as [x' ?]
         | A: _ /\ _ |- _ => destruct A as [? ?]
         end.

(* TODO why do we need to write this? *)
Instance src2imp : map.map string Decode.Register := SortedListString.map Z.

Definition p4mm (memInit: Syntax.Vec (Syntax.ConstT (MemTypes.Data IsaRv32.rv32DataBytes))
                                     (Z.to_nat KamiProc.width)): Kami.Syntax.Modules :=
  p4mm memInit instrMemSizeLg instrMemSizeLg_bounds.

Instance pipeline_params: PipelineWithRename.Pipeline.parameters.
unshelve refine pipeline_params.
- exact (@Semantics.mem semantics).
- exact (@Semantics.funname_env semantics).
- refine (@Semantics.mem_ok _ _).
- refine (@Semantics.funname_env_ok _ _).
Defined.

Definition prog :=
  @prog
    (Z_keyed_SortedListMap.Zkeyed_map (@Utility.word KamiRiscv.KamiWordsInst))
    (Z_keyed_SortedListMap.Zkeyed_map_ok (@Utility.word KamiRiscv.KamiWordsInst))
    (@Semantics.mem semantics)
    (@Semantics.mem_ok semantics ok)
    (@Semantics.funname_env semantics)
    (@Semantics.funname_env_ok semantics ok)
    src2imp
    init_code loop_body funimplsList.

Definition lightbulb_insts_unevaluated: list Decode.Instruction :=
  @PipelineWithRename.compile_prog pipeline_params prog ml.

(* Before running this command, it might be a good idea to do
   "Print Assumptions lightbulb_insts_unevaluated."
   and to check if there are any axioms which could block the computation. *)
(* TODO: These instructions will have to be fed to putProgram to get them into
   the bedrock2 memory, and we will have to make sure that the Kami processor
   contains the corresponding instructions too. *)
Definition lightbulb_insts: list Decode.Instruction := Eval cbv in lightbulb_insts_unevaluated.

Module PrintProgram.
  Import riscv.Utility.InstructionNotations.
  Import bedrock2.NotationsCustomEntry.
  Import bedrock2.Hexdump.
  Local Open Scope hexdump_scope.
  Set Printing Width 108.

  Goal True.
    pose (SortedList.value (PipelineWithRename.function_positions prog)) as symbols.
    cbv in symbols.

    pose lightbulb_insts as p.
    unfold lightbulb_insts in p.

    let x := eval cbv in (instrencode lightbulb_insts) in idtac (* x *).
  Abort.
  Unset Printing Width.
End PrintProgram.

Axiom TODO_sam_and_joonwon: False.

Lemma end2end_lightbulb:
  forall (memInit: Syntax.Vec (Syntax.ConstT (MemTypes.Data IsaRv32.rv32DataBytes))
                              (Z.to_nat KamiProc.width))
         (t: Kami.Semantics.LabelSeqT) (mFinal: KamiRiscv.KamiImplMachine),
    Semantics.Behavior (p4mm memInit) mFinal t ->
    exists t': list KamiRiscv.Event,
      KamiRiscv.KamiLabelSeqR t t' /\
      (exists (suffix : list KamiRiscv.Event) (bedrockTrace : list RiscvMachine.LogItem),
          KamiRiscv.traces_related (suffix ++ t') bedrockTrace /\
          (exists ioh : list (lightbulb_spec.OP _),
              relate_lightbulb_trace_to_bedrock ioh bedrockTrace /\ goodHlTrace ioh)).
Proof.
  (* Fail eapply @end2end. unification only works after some specialization *)
  pose proof @end2end as Q.
  specialize_first Q init_code.
  specialize_first Q loop_body.
  specialize_first Q funimplsList.
  specialize_first Q spec.
  specialize_first Q ml.
  specialize_first Q mlOk.
  specialize_first Q instrMemSizeLg_bounds.
  intro memInit.
  specialize_first Q memInit.

  unfold bedrock2Inv, goodTraceE, isReady, goodTrace, spec in *.
  eapply Q; clear Q; cycle 2.
  - (* preserve invariant *)
    intros.
    (* TODO make Simp.simp work here *)
    destruct H as [ [ buf [R [Sep L] ] ] [ [ioh [Rel G] ] ? ] ]. subst l.
    pose proof link_lightbulb_withCorrectWordInstance as P.
    unfold spec_of_iot in *.
    specialize_first P Sep.
    specialize_first P L.
    cbv [loop_body funimplsList prog
         WeakestPrecondition.cmd WeakestPrecondition.cmd_body].
    eexists. split; [reflexivity|].
    eapply weaken_call; [eapply P|clear P].
    cbv beta.
    intros.
    destr.
    subst.
    eexists. split; [reflexivity|].
    split.
    + eauto.
    + destruct H3 as [ C | [C | [C | [C | C ] ] ] ]; (split; [|reflexivity]);
        destr; eexists (ioh0 ++ ioh)%list; (split;
        [ eapply relate_concat; assumption
        | apply goodHlTrace_addOne;
          [unfold traceOfOneInteraction, choice; eauto 10
          | exact G]]).
  - cbv. repeat constructor; cbv; intros; intuition congruence.
  - (* establish invariant *)
    intros.
    unfold init_code, prog.
    hnf. split; [|split].
    + case TODO_sam_and_joonwon. (* how can we relate m to Kami's mem and constrain it? *)
    + exists []. split.
      * apply relate_nil.
      * unfold goodHlTrace. apply kleene_empty.
    + reflexivity.
  Unshelve.
  all: typeclasses eauto.
Qed. (* takes more than 30s *)
