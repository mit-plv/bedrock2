Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Interface.
Require Import coqutil.Map.Interface.
Require Import end2end.End2EndPipeline.
Require Import bedrock2.Syntax.
Require Import bedrock2.Examples.lightbulb.
Require Import bedrock2.TracePredicate. Import TracePredicateNotations.
Require Import compiler.examples.integration.
Require Import compiler.ProgramSpec.
Require Import compiler.MemoryLayout.

Open Scope Z_scope.
Open Scope string_scope.

Axiom TODO: False.

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

Definition spec: ProgramSpec := {|
  datamem_start := match TODO with end;
  datamem_pastend := match TODO with end;
  goodTrace iol := exists ioh, SPI.mmio_trace_abstraction_relation ioh iol /\
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

Goal @Naive.rep 32 = Word.word 32.
  (* TODO does not hold: bedrock2 separation logic word <> kami word !! *)
Abort.

Lemma end2end_lightbulb: False.
Proof.
  pose proof link_lightbulb as P.
  unfold spec_of_iot in *.

  pose proof @end2end as Q.
  specialize_first Q integration.mapops.

  Fail specialize Q with (prog := prog).

(*
 instrMemSizeLg
 dataMemSize
 prog
 spec
 ml
 mlOk
 memInit
 instrMemSizeLg_agrees_with_ml
*)

Abort.
