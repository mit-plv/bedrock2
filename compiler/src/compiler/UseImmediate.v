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

    destr (useImmediate is5BitImmediate is12BitImmediate s1); destr (useImmediate is5BitImmediate is12BitImmediate s2); try eauto.
    destr (map.get l y); destr z; destr op; progress inversion IHexec.
    { destr (is12BitImmediate v).
      { destr (x =? v0)%string.
        { specialize H1 with (t' :=  t) (m' := m) (l' := (map.put l v0 (word.of_Z v))) (mc' := (MetricLogging.addMetricLoads 8 (MetricLogging.addMetricInstructions 8 mc))). clear H2 H3 H4 H5 H6 H7 H8. apply H0 in H9 as H2. apply H1 in H9 as H3.

End WithArguments.
