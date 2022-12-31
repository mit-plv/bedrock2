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
    11: { eapply exec.if_false. { assumption.  } {assumption. } }
    
      intros; simpl; try assumption.
    destruct st1; simpl. destruct st2; simpl. 
  Qed.

End WithArguments.
    
  
