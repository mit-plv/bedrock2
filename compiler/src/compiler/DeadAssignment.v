Require Import compiler.util.Common.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Require Import compiler.DeadAssignmentDef.
Require Import bedrock2.MetricLogging.

Local Notation var := String.string (only parsing).

Section WithArguments.
  Context {width : Z}.
  Context {BW :  Bitwidth.Bitwidth width }.
  Context {word :  word width } {word_ok : word.ok word}.
  Context {env :  map.map string (list var * list var * stmt var) } {env_ok : map.ok env}.
  Context {mem :  map.map word (Init.Byte.byte : Type) } {mem_ok: map.ok mem}.
  Context {locals :  map.map string word } {locals_ok: map.ok locals}.
  Context {ext_spec : Semantics.ExtSpec} {ext_spec_ok: Semantics.ext_spec.ok ext_spec}.

  Local Hint Constructors exec: core.
(*
  Lemma deadassignment_correct_aux:
    forall eH eL,
       deadassignment_functions eH = Success eL ->
       forall sH t m mcH lH post,
       exec eH sH t m lH mcH post ->
       exec eL (??? sH) t m lH mcH post.
  Proof.
    induction 2.
    (* most cases stay the same *)
    all: try solve [simpl; eauto].
  Admitted. *)
End WithArguments.
