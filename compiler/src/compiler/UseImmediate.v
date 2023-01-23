Require Import compiler.util.Common.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Require Import compiler.UseImmediateDef.

Section WithArguments.
  Context {width : Z}.
  Context {BW :  Bitwidth.Bitwidth width }.
  Context {word :  word width }.
  Context {env :  map.map string (list string * list string * stmt string) }.
  Context {mem :  map.map word (Init.Byte.byte : Type) }.
  Context {locals :  map.map string word }.
  Context {ext_spec : Semantics.ExtSpec}.
  Context (is5BitImmediate : Z -> bool).
  Context (is12BitImmediate  : Z -> bool).
  Local Hint Constructors exec: core.
  Lemma useImmediateCorrect :
    forall e st t m l mc post, exec e st t m l mc post -> exec e (useImmediate is5BitImmediate is12BitImmediate st) t m l mc post.
  Proof.
    intros.
    induction H; simpl; eauto.
    destr s1; destr s2; try eauto; simpl in *; clear H H1.
    destr z.
    (* 1: { destr op.
      { destr (is12BitImmediate v).
        { destr ((x =? v0)%string).
          { inversion IHexec. clear IHexec H H1 H2 H3 H4 H5 H6.  specialize H0 with (t' := t) (m' := m) (l' := (map.put l v0 (word.of_Z v))) (mc' := (MetricLogging.addMetricLoads 8 (MetricLogging.addMetricInstructions 8 mc))). apply H0 in H7. clear H0.*)
    (* 2: { inversion IHexec. clear H H1 H2 H3 H4 H5 H6 IHexec.  specialize H0 with (t' := t) (m' := m) (l' := (map.put l x (word.of_Z v))) (mc' := (MetricLogging.addMetricLoads 8 (MetricLogging.addMetricInstructions 8 mc))). apply H0 in H7. clear H0. *)

End WithArguments.
