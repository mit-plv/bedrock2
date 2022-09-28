Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique coqutil.Byte.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.fwd coqutil.Tactics.Tactics.
Require Import bedrock2.Notations bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.Memory.
Require Import bedrock2.Semantics.

Require Import Coq.Lists.List.

Section semantics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * cmd)}.
  Context {ext_spec: ExtSpec}.

  Lemma frame_load: forall mSmall mBig mAdd a r (v: word),
      map.split mBig mSmall mAdd ->
      load a mSmall r = Some v ->
      load a mBig r = Some v.
  Proof.
  Admitted.

  Lemma frame_store: forall sz (mSmall mSmall' mBig mAdd: mem) a v,
      map.split mBig mSmall mAdd ->
      store sz mSmall a v = Some mSmall' ->
      exists mBig', map.split mBig' mSmall' mAdd /\ store sz mBig a v = Some mBig'.
  Proof.
  Admitted.

  Lemma frame_eval_expr: forall l e mSmall mBig mAdd mc (v: word) mc',
      map.split mBig mSmall mAdd ->
      eval_expr mSmall l e mc = Some (v, mc') ->
      eval_expr mBig l e mc = Some (v, mc').
  Proof.
    induction e; cbn; intros; fwd; try reflexivity;
      erewrite ?IHe by eassumption;
      erewrite ?IHe1 by eassumption;
      try match goal with
        | |- context[word.eqb ?L ?R] => destr (word.eqb L R)
        end;
      erewrite ?IHe2 by eassumption;
      erewrite ?IHe3 by eassumption;
      erewrite ?frame_load by eassumption;
      rewrite_match;
      try reflexivity.
  Qed.

  Lemma frame_evaluate_call_args_log: forall l mSmall mBig mAdd arges
                                             mc (args: list word) mc',
      map.split mBig mSmall mAdd ->
      evaluate_call_args_log mSmall l arges mc = Some (args, mc') ->
      evaluate_call_args_log mBig   l arges mc = Some (args, mc').
  Proof.
    induction arges; cbn; intros.
    - assumption.
    - fwd. erewrite frame_eval_expr by eassumption. erewrite IHarges.
      1: reflexivity. all: assumption.
  Qed.

  Axiom TODO: False.

  Lemma frame_exec: forall e c t mSmall l mc P,
      exec e c t mSmall l mc P ->
      forall mBig mAdd,
        map.split mBig mSmall mAdd ->
        exec e c t mBig l mc (fun t' mBig' l' mc' =>
          exists mSmall', map.split mBig' mSmall' mAdd /\ P t' mSmall' l' mc').
  Proof.
    induction 1; intros;
      try match goal with
        | H: store _ _ _ _ = _ |- _ => eapply frame_store in H; [ | eassumption]
        end;
      fwd;
      try solve [econstructor; eauto using frame_eval_expr].
    { eapply exec.stackalloc. 1: eassumption.
      intros.
      rename mCombined into mCombinedBig.
      specialize H1 with (1 := H3).
      assert (map.split (map.putmany mSmall mStack) mSmall mStack) as Sp by case TODO.
      specialize H1 with (1 := Sp).
      specialize (H1 mCombinedBig mAdd).
      assert (map.split mCombinedBig (map.putmany mSmall mStack) mAdd) as Sp' by case TODO.
      specialize (H1 Sp').
      eapply exec.weaken. 1: eapply H1.
      cbv beta. intros. fwd.
      assert (map.split m' (map.putmany mSmall'0 mAdd) mStack') as Sp'' by case TODO.
      eexists. exists mStack'. ssplit.
      1,2: eassumption.
      eexists; split. 2: eassumption.
      assert (map.split (map.putmany mSmall'0 mAdd) mSmall'0 mAdd) by case TODO.
      assumption. }
    { eapply exec.seq. 1: eapply IHexec; eassumption.
      cbv beta. intros. fwd. eapply H1. 1: eassumption. assumption. }
    { eapply exec.while_true.
      1: eauto using frame_eval_expr.
      1: eassumption.
      { eapply IHexec. 1: eassumption. }
      cbv beta. intros. fwd. eauto. }
    { (* call *)
      case TODO. }
    { (* interact *)
      assert (map.split mBig (map.putmany mKeep mAdd) mGive) as Sp by case TODO.
      econstructor. 1: exact Sp.
      { eauto using frame_evaluate_call_args_log. }
      1: eassumption.
      intros.
      specialize H2 with (1 := H4). fwd.
      eexists. split. 1: eassumption.
      intros.
      assert (exists mSmall', map.split mSmall' mKeep mReceive) by case TODO.
      fwd. exists mSmall'.
      assert (map.split m' mSmall' mAdd) by case TODO.
      split.
      1: assumption.
      eapply H2p1. assumption.
    }
  Qed.

End semantics.
