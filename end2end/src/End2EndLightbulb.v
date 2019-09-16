Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import bedrock2.Syntax.
Require Import bedrock2.Examples.lightbulb.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.
Require Import compiler.ProgramSpec.
Require Import compiler.MemoryLayout.
Require Import end2end.End2EndPipeline.
Require Import end2end.Bedrock2SemanticsForKami.

Open Scope Z_scope.
Open Scope string_scope.

Axiom TODO: False.

Instance mapops: RegAlloc.map.ops (SortedListString.map Z). refine (
  {| RegAlloc.map.intersect (s1 s2 : SortedListString.map Z) :=
    {| SortedList.value := ListLib.list_intersect (fun '(k,v) '(k',v') => andb (_ k k') (_ v v')) (SortedList.value s1) (SortedList.value s2);
       SortedList._value_ok := match TODO with end |};
     RegAlloc.map.default_value := 666;
  |}).
- exact String.eqb.
- exact Z.eqb.
Defined.

Definition instrMemSizeLg: Z := 10. (* TODO is this enough? *)
Definition dataMemSize: Z := 4096.

Definition funnamesList: list string.
  match type of link_lightbulb with
  | spec_of_iot ?L => let r := eval cbv in (List.map fst L) in exact r
  end.
Defined.

Definition funimplsMap: Semantics.env.
  match type of link_lightbulb with
  | spec_of_iot ?L =>
    let keys := eval cbv in (List.map fst L) in
    let values := eval cbv in (List.map snd L) in
    let o := eval cbv in (@map.of_list _ _ Semantics.env keys values) in
    lazymatch o with
    | Some ?m => exact m
    end
  end.
Defined.

Definition buffer_addr: Z. Admitted.

(* TODO is it ok to overwrite a register with "res"? *)
Definition loopbody := @cmd.call Semantics.syntax ["res"] "iot" [expr.literal buffer_addr].

Definition prog := {|
  funnames := funnamesList;
  funimpls := funimplsMap;
  init_code := @cmd.skip Semantics.syntax;
  loop_body := @cmd.call Semantics.syntax ["res"] "iot" [expr.literal buffer_addr];
|}.

Definition traceOfOneInteraction: list (lightbulb_spec.OP Semantics.word) -> Prop :=
  (existsl (fun bytes => lightbulb_spec.lan9250_recv _ _ bytes)) |||
  (lightbulb_spec.lan9250_recv_no_packet _ _) |||
  (lightbulb_spec.lan9250_recv_packet_too_long _ _) |||
  (any +++ (lightbulb_spec.spi_timeout _)).

Definition goodHlTrace: list (lightbulb_spec.OP Semantics.word) -> Prop :=
  traceOfOneInteraction ^*.

Definition relate_lightbulb_trace_to_bedrock(ioh: list (lightbulb_spec.OP Semantics.word))
                                            (iol : Semantics.trace): Prop.
  refine (SPI.mmio_trace_abstraction_relation (_ ioh) (_ iol)).
  all: case TODO.
  (* this should not be needed any more once lightbulb proofs are for generic word *)
Defined.

Definition spec: ProgramSpec := {|
  datamem_start := match TODO with end;
  datamem_pastend := match TODO with end;
  goodTrace iol := exists ioh, relate_lightbulb_trace_to_bedrock ioh iol /\
                               goodHlTrace ioh;
  isReady t m l := exists buf R,
    (Separation.sep (Array.array Scalars.scalar8 (word.of_Z 1) (word.of_Z buffer_addr) buf) R) m /\
    length buf = 1520%nat;
|}.

Definition ml: MemoryLayout 32. Admitted.

Lemma mlOk: MemoryLayoutOk ml.
Proof.
  constructor.
Admitted.

Definition memInit: SC.MemInit (BinIntDef.Z.to_nat Semantics.width) IsaRv32.rv32DataBytes.
Admitted.

Lemma instrMemSizeLg_agrees_with_ml:
  word.sub (code_pastend ml) (code_start ml) = word.of_Z instrMemSizeLg.
Admitted.

Lemma end2end_lightbulb: False.
Proof.
  pose proof link_lightbulb as P.
  unfold spec_of_iot in *.

  pose proof @end2end as Q.
  specialize_first Q mapops.
  specialize_first Q prog.
  specialize_first Q instrMemSizeLg_agrees_with_ml.
  specialize_first Q spec.
  specialize_first Q mlOk.
  specialize_first Q memInit.

Abort.
