Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Map.Interface.
Require Import end2end.End2EndPipeline.
Require Import bedrock2.Syntax.
Require Import bedrock2.Examples.lightbulb.
Require Import compiler.examples.integration.
Require Import compiler.ProgramSpec.

Open Scope Z_scope.
Open Scope string_scope.

Definition instrMemSizeLg: Z := 10. (* TODO is this enough? *)
Definition dataMemSize: Z := 4096.

Definition funnamesList: list string.
  match type of link_lightbulb with
  | spec_of_iot ?L => let r := eval cbv in (List.map fst L) in exact r
  end.
Defined.

Definition buffer_addr: Z. Admitted.

(* TODO is it ok to overwrite a register with "res"? *)
Definition loopbody := @cmd.call Semantics.syntax ["res"] "iot" [expr.literal buffer_addr].

Fail Check {|
  funnames := funnamesList;
  init_code := cmd.skip;
  loop_body := @cmd.call Semantics.syntax ["res"] "iot" [expr.literal buffer_addr];

|}.

(*
Definition prog: Program := {|
  funnames := functionNames;
  funimpls := Interface.map.of_list
  init_code :=
  loop_body :=

Definition spec
Definition ml
Definition mlOk
Definition memInit
Definition instrMemSizeLg_agrees_with_ml

*)

Lemma end2end_lightbulb: False.
Proof.
  pose proof link_lightbulb as P.
  unfold spec_of_iot in *.


  pose proof @end2end as Q.
  specialize_first Q integration.mapops.

Abort.
