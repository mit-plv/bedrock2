Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface coqutil.Word.Properties.
Require Import coqutil.Word.Bitwidth.
Require Import bedrock2.MetricLogging.
Require bedrock2.MetricWeakestPrecondition.

Require Import Coq.Classes.Morphisms.

Section MetricWeakestPrecondition.
  Context {width} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: Semantics.ExtSpec}.

  Ltac ind_on X :=
    intros;
    (* Note: Comment below dates from when we were using a parameter record p *)
    (* Note: "before p" means actually "after p" when reading from top to bottom, because,
       as the manual points out, "before" and "after" are with respect to the direction of
       the move, and we're moving hypotheses upwards here.
       We need to make sure not to revert/clear p, because the other lemmas depend on it.
       If we still reverted/cleared p, we'd get errors like
       "Error: Proper_load depends on the variable p which is not declared in the context."
       when trying to use Proper_load, or, due to COQBUG https://github.com/coq/coq/issues/11487,
       we'd get a typechecking failure at Qed time. *)
    repeat match goal with x : ?T |- _ => first
       [ constr_eq T X; move x before ext_spec
       | constr_eq T X; move x before locals
       | constr_eq T X; move x at top
       | revert x ] end;
    match goal with x : X |- _ => induction x end;
    intros.

  Local Hint Mode word.word - : typeclass_instances.

  (* we prove weakening lemmas for all WP definitions in a syntax-directed fashion,
   * moving from postcondition towards precondition one logical connective at a time. *)
  Global Instance Proper_literal : Proper (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))) MetricWeakestPrecondition.literal.
  Proof using. clear. cbv [MetricWeakestPrecondition.literal]; cbv [Proper respectful pointwise_relation Basics.impl dlet.dlet]. eauto. Qed.

  Global Instance Proper_get : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) MetricWeakestPrecondition.get.
  Proof using. clear. cbv [MetricWeakestPrecondition.get]; cbv [Proper respectful pointwise_relation Basics.impl]; intros * ? (?&?&?); eauto. Qed.

  Global Instance Proper_load : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))))) MetricWeakestPrecondition.load.
  Proof using. clear. cbv [MetricWeakestPrecondition.load]; cbv [Proper respectful pointwise_relation Basics.impl]; intros * ? (?&?&?); eauto. Qed.

  Global Instance Proper_store : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))))) MetricWeakestPrecondition.store.
  Proof using. clear. cbv [MetricWeakestPrecondition.store]; cbv [Proper respectful pointwise_relation Basics.impl]; intros * ? (?&?&?); eauto. Qed.

  Global Instance Proper_expr : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))))) MetricWeakestPrecondition.expr.
  Proof using.
    clear.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on Syntax.expr.expr;
      cbn in *; intuition (try typeclasses eauto with core).
    { eapply Proper_literal; eauto. }
    { eapply Proper_get; eauto. }
    { eapply IHa1; eauto; intuition idtac. destruct a4. eapply Proper_load; eauto using Proper_load. }
    { eapply IHa1; eauto; intuition idtac. destruct a4. eapply Proper_load; eauto using Proper_load. }
    { eapply IHa1_1; eauto. destruct a1. eapply IHa1_2; eauto. destruct a1. eauto. }
    {eapply IHa1_1; eauto; intuition idtac. destruct a1. Tactics.destruct_one_match; eauto using Proper_load . }
  Qed.

  Global Instance Proper_list_map {A B} :
   Proper ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl))) ==> pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl))) (MetricWeakestPrecondition.list_map (A:=A) (B:=B)).
  Proof using.
    clear.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on (list A);
      cbn in *; intuition (try typeclasses eauto with core).
    eapply H; eauto. destruct a2. eapply IHa; eauto. destruct a2; eauto.
  Qed.

  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Global Instance Proper_cmd :
    Proper 
        (pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl)))) ==>
       Basics.impl))))))) MetricWeakestPrecondition.cmd.  
  Proof using ext_spec_ok locals_ok mem_ok word_ok.
    pose proof I. (* to keep naming *)
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl]; ind_on Syntax.cmd.cmd;
      cbn in *; cbv [dlet.dlet] in *; intuition (try typeclasses eauto with core).
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      1: eapply Proper_expr.
      1: cbv [pointwise_relation Basics.impl]; intuition eauto 2.
      all: eauto. }
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      { eapply Proper_expr.
        { cbv [pointwise_relation Basics.impl]; intuition eauto 2. }
        { eauto. } }
      { destruct H2 as (?&?&?&?). eexists. eexists. split.
        { eapply Proper_expr.
          { cbv [pointwise_relation Basics.impl]; intuition eauto 2. }
          { eauto. } }
        { eapply Proper_store; eauto; cbv [pointwise_relation Basics.impl]; eauto. } } }

    { eapply H1. 2: eapply H3; eassumption. intros ? ? ? ? (?&?&?&?&?). eauto 7. }
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      { eapply Proper_expr.
        { cbv [pointwise_relation Basics.impl]; intuition eauto 2. }
        { eauto. } }
      { intuition eauto 6. } }
    { eapply MetricSemantics.exec.weaken; eassumption. }
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      { eapply Proper_list_map; eauto; try exact H4; cbv [respectful pointwise_relation Basics.impl]; intuition eauto 2.
        eapply Proper_expr; eauto. }
      { eapply MetricSemantics.weaken_call. 1: eassumption. cbv beta.
        (* COQBUG (performance), measured in Coq 8.9:
           "firstorder eauto" works, but takes ~100s and increases memory usage by 1.8GB.
           On the other hand, the line below takes just 5ms *)
        cbv beta; intros ? ? ? ? (?&?&?); eauto. } }
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      { eapply Proper_list_map; eauto; try exact H4; cbv [respectful pointwise_relation Basics.impl].
        { eapply Proper_expr; eauto. }
        { eauto. } }
      { destruct H2 as (mKeep & mGive & ? & ?).
        exists mKeep. exists mGive.
        split; [assumption|].
        eapply Semantics.ext_spec.weaken; [|solve[eassumption]].
        intros ? ? (?&?&?); eauto 10. } }
  Qed.

  Global Instance Proper_call :
    Proper (
     (pointwise_relation _ (
     (pointwise_relation _ (
     (pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation  _ Basics.impl)))) ==>
     Basics.impl)))))))))) MetricWeakestPrecondition.call.
  Proof using word_ok mem_ok locals_ok ext_spec_ok.
    cbv [Proper respectful pointwise_relation Basics.impl].
    intros. eapply MetricSemantics.weaken_call; eassumption.
  Qed.

Global Instance Proper_program :
    Proper (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl)))) ==>
     Basics.impl))))))) MetricWeakestPrecondition.program.
   Proof using word_ok mem_ok locals_ok ext_spec_ok.
    cbv [Proper respectful pointwise_relation Basics.impl  MetricWeakestPrecondition.program]; intros.
    eapply Proper_cmd;
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  MetricWeakestPrecondition.func];
    try solve [typeclasses eauto with core].
  Qed.

  Ltac t :=
      repeat match goal with
             | |- forall _, _ => progress intros
             | H: exists _, _ |- _ => destruct H
             | H: and _ _ |- _ => destruct H
             | H: eq _ ?y |- _ => subst y
             | H: False |- _ => destruct H
             | _ => progress cbn in *
             | _ => progress cbv [dlet.dlet MetricWeakestPrecondition.dexpr MetricWeakestPrecondition.dexprs MetricWeakestPrecondition.store] in *
        end; eauto.
  
Lemma expr_sound m l e mc post (H : MetricWeakestPrecondition.expr m l e mc post)
    : exists v mc', MetricSemantics.eval_expr m l e mc = Some (v, mc') /\ post (v, mc').
Proof using BW ext_spec ext_spec_ok locals
locals_ok mem mem_ok width word word_ok.
    ind_on Syntax.expr; t. { destruct H. destruct H. eexists. eexists. rewrite H. eauto. }
    { eapply IHe in H; t. cbv [MetricWeakestPrecondition.load] in H0; t. rewrite H. rewrite H0. eauto. }
    { eapply IHe in H; t. cbv [MetricWeakestPrecondition.load] in H0; t. rewrite H. rewrite H0.
      eexists. eexists. split; eauto. }
    { eapply IHe1 in H; t. eapply IHe2 in H0; t. rewrite H, H0; eauto. }
    { eapply IHe1 in H; t. rewrite H. Tactics.destruct_one_match.
      { apply IHe3; t. }
      { eapply IHe2 in H0; t. } }
  Qed.

  Import ZArith coqutil.Tactics.Tactics.

  Lemma expr_complete: forall m l e mc v mc',
    MetricSemantics.eval_expr m l e mc = Some (v, mc') ->
    MetricWeakestPrecondition.dexpr m l e mc (v, mc').
  Proof using word_ok.
    induction e; cbn; intros.
    - inversion_clear H. reflexivity.
    - eexists; eexists; destruct (map.get l x); try inversion H; try reflexivity.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      eapply Proper_expr.
      2: { eapply IHe. rewrite E. reflexivity. }
      intros (addr, oldmc) ?. apply pair_equal_spec in H0; destruct H0.
      subst r m0. unfold MetricWeakestPrecondition.load. eexists; split; eauto.
      apply Option.eq_of_eq_Some in H. auto.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      eapply Proper_expr.
      2: { eapply IHe. rewrite E. reflexivity. }
      intros (addr, oldmc) ?. apply pair_equal_spec in H0; destruct H0.
      subst r m0. unfold MetricWeakestPrecondition.load. eexists; split; eauto.
      apply Option.eq_of_eq_Some in H; auto.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      eapply Proper_expr.
      2: { eapply IHe1. rewrite E. reflexivity. }
      intros (v1, oldmc1) ?. apply pair_equal_spec in H0; destruct H0.
      subst r m0. 
      eapply Proper_expr.
      2: { eapply IHe2. rewrite E0. reflexivity. }
      intros (v2, oldmc2)  ?. apply pair_equal_spec in H0; destruct H0.
      subst r0 m1. congruence.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      eapply Proper_expr.
      2: { eapply IHe1. rewrite E. reflexivity. }
      intros (vc, oldmc) ?. apply pair_equal_spec in H0; destruct H0.
      subst r m0.
      destr (word.eqb vc (word.of_Z 0)).
      + eapply IHe3. eassumption.
      + eapply IHe2. eassumption.
  Qed.


Lemma sound_args : forall m l args mc P,
      MetricWeakestPrecondition.list_map (MetricWeakestPrecondition.expr m l) args mc P ->
      exists x mc', MetricSemantics.eval_call_args m l args mc = Some (x, mc') /\ P (x, mc').
Proof using BW ext_spec ext_spec_ok locals locals_ok mem mem_ok
width word word_ok.
    induction args; cbn; repeat (subst; t).
    eapply expr_sound in H; t; rewrite H.
    eapply IHargs in H0; t; rewrite H0.
    eauto.
  Qed.

  Lemma sound_getmany l a mc P :
    MetricWeakestPrecondition.list_map (MetricWeakestPrecondition.get l) a mc P
    -> exists vs mc', map.getmany_of_list l a = Some vs /\ P (vs, mc').
  Proof.
    cbv [map.getmany_of_list] in *.
    revert P l mc; induction a; cbn; repeat (subst; t).
    cbv [MetricWeakestPrecondition.get] in H; t.
    epose proof (IHa _ l _ _); clear IHa; t.
    rewrite H. erewrite H1. eexists; eexists; split; eauto.
    Unshelve.
    3: exact H0.
    all: cbv [respectful pointwise_relation Basics.impl MetricWeakestPrecondition.get]; intros; cbv beta; t.
  Qed.

  Local Hint Constructors MetricSemantics.exec : core.
  Lemma sound_cmd e c t m l mc post (H: MetricWeakestPrecondition.cmd e c t m l mc post) : MetricSemantics.exec e c t m l mc post.
  Proof.
    ind_on Syntax.cmd; repeat (t; try match reverse goal with H: MetricWeakestPrecondition.expr _ _ _ _ _ |- _ => eapply expr_sound in H end).
    { destruct (BinInt.Z.eq_dec (Interface.word.unsigned x) (BinNums.Z0)) as [Hb|Hb]; cycle 1; apply pair_equal_spec in H1; destruct H1; econstructor; t. }
    { inversion H0. inversion H.
      apply pair_equal_spec in H3; destruct H3.
      apply pair_equal_spec in H4; destruct H4. subst x0.
      econstructor; t.
      Admitted.

  Lemma weaken_cmd: forall e c t m l mc (post1 post2: _->_->_->_->Prop),
      MetricWeakestPrecondition.cmd e c t m l mc post1 ->
      (forall t m l mc, post1 t m l mc -> post2 t m l mc) ->
      MetricWeakestPrecondition.cmd e c t m l mc post2.
  Proof. Admitted.

   Lemma complete_args : forall m l args mc vs,
      MetricSemantics.eval_call_args m l args mc = Some vs ->
      MetricWeakestPrecondition.dexprs m l args mc vs.
  Proof using word_ok. Admitted.

  Lemma complete_cmd: forall e c t m l mc post,
      MetricSemantics.exec e c t m l mc post ->
      MetricWeakestPrecondition.cmd e c t m l mc post.
  Proof. Admitted.

  Lemma start_func: forall e fname fimpl t m args mc post,
      map.get e fname = Some fimpl ->
      MetricWeakestPrecondition.func e fimpl t m args mc post ->
      MetricWeakestPrecondition.call e fname t m args mc post.
  Proof. Admitted.

  (** Ad-hoc lemmas here? *)

  Import bedrock2.Syntax bedrock2.MetricSemantics bedrock2.MetricWeakestPrecondition.

  (*
  Lemma interact_nomem call action binds arges t m l post
        args (Hargs : dexprs m l arges args)
        (Hext : ext_spec t map.empty binds args (fun mReceive (rets : list word) =>
           mReceive = map.empty /\
           exists l0 : locals, map.putmany_of_list_zip action rets l = Some l0 /\
           post (cons (map.empty, binds, args, (map.empty, rets)) t) m l0))
    : WeakestPrecondition.cmd call (cmd.interact action binds arges) t m l post.
  Proof using word_ok mem_ok ext_spec_ok.
    exists args; split; [exact Hargs|].
    exists m.
    exists map.empty.
    split; [eapply Properties.map.split_empty_r; exact eq_refl|].
    eapply ext_spec.weaken; [|eapply Hext]; intros ? ? [? [? []]]. subst a; subst.
    eexists; split; [eassumption|].
    intros. eapply Properties.map.split_empty_r in H. subst. assumption.
  Qed.*)

  Lemma intersect_expr: forall m l e mc (post1 post2: word * MetricLog -> Prop),
      MetricWeakestPrecondition.expr m l e mc post1 ->
      MetricWeakestPrecondition.expr m l e mc post2 ->
      MetricWeakestPrecondition.expr m l e mc (fun v => post1 v /\ post2 v).
  Proof using word_ok. Admitted. 

  Lemma dexpr_expr (m : mem) l e mc P
    (H : MetricWeakestPrecondition.expr m l e mc P)
    : exists v, MetricWeakestPrecondition.dexpr m l e mc v /\ P v.
  Proof using word_ok. Admitted.
  
End MetricWeakestPrecondition.
