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
  Context {word :  word width } {word_ok : word.ok word}.
  Context {env :  map.map string (list string * list string * stmt string) } {env_ok : map.ok env}.
  Context {mem :  map.map word (Init.Byte.byte : Type) } {mem_ok: map.ok mem}.
  Context {locals :  map.map string word } {locals_ok: map.ok locals}.
  Context {ext_spec : Semantics.ExtSpec} {ext_spec_ok: Semantics.ext_spec.ok ext_spec}.
  Context (is5BitImmediate : Z -> bool).
  Context (is12BitImmediate  : Z -> bool).

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
        constants [word_cst]).

  Lemma word_and_comm:
     forall x y : word, word.and x y = word.and y x.
  Proof.
    intros. eapply word.unsigned_inj. rewrite word.unsigned_and_nowrap. rewrite word.unsigned_and_nowrap. apply Z.land_comm.
  Qed.

  Lemma word_or_comm:
    forall x y : word, word.or x y = word.or y x.
  Proof.
    intros. eapply word.unsigned_inj. rewrite word.unsigned_or_nowrap. rewrite word.unsigned_or_nowrap. apply Z.lor_comm.
  Qed.

  Lemma word_xor_comm:
    forall x y : word, word.xor x y = word.xor y x.
  Proof.
    intros. eapply word.unsigned_inj. rewrite word.unsigned_xor_nowrap. rewrite word.unsigned_xor_nowrap. apply Z.lxor_comm.
  Qed.


  Ltac destr_exec :=
    match goal with
    | [ |- exec _ (match ?x with | _ => _ end) _ _ _ _ _ ] => destr x
    | [ |- exec _ (if ?x then _ else _ ) _ _ _ _ _ ] => destr x
    end.

  Ltac apply_exec :=
   match goal with
   | [ |- exec _ (SSeq _ _) _ _ _ _ _ ] => apply exec.seq_cps
   | [ |- exec _ (SLit _ _) _ _ _ _ _ ] => apply exec.lit
   end.

  Ltac inversion_exec :=
    match goal with
    | [ H: exec _ _ _ _ _ _ _ |- _ ] => inversion H
    end.

  Local Hint Constructors exec: core.
  Lemma useImmediateCorrect :
    forall e st t m l mc post, exec e st t m l mc post -> exec e (useImmediate is5BitImmediate is12BitImmediate st) t m l mc post.
  Proof.
  intros;
  match goal with
  | [ H: exec _ _ _ _ _ _ _  |- _ ] => induction H
  end;
  simpl in *; repeat destr_exec; eauto; inversion_exec;
  match goal with
  | [ H: ?P _ _ _ _, H0: forall t m l mc, ?P t m l mc -> _ |- _ ] => apply H0 in H; inversion H
  end;
  repeat apply_exec;
  simpl in *;
  match goal with
  | [ H: map.get (map.put _ ?x _) ?x = _ |- _ ] => rewrite map.get_put_same in H; fwd
  end;
  eapply exec.op;  simpl;
  eauto.

  { replace (word.add z' (word.of_Z v))  with  (word.add (word.of_Z v) z') by ring. assumption. }
  { replace (word.add y' (word.of_Z (- v)))  with  (word.sub  y' (word.of_Z v)) by ring. assumption. }
  { rewrite word_and_comm. assumption. }
  { rewrite word_or_comm. assumption. }
  { rewrite word_xor_comm. assumption. }
  Qed.

End WithArguments.
