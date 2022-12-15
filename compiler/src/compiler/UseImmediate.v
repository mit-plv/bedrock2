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
  
  Lemma useImmediateCorrect :
    forall e st t m l mc post, exec e st t m l mc post -> exec e (useImmediate st) t m l mc post.
  Proof.
    induction st; intros; simpl; try assumption.
    destruct st1; simpl; destruct st2; simpl. 
  Qed.

End WithArguments.
    
  
