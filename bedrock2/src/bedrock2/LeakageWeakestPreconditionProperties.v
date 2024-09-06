Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface coqutil.Word.Properties.
Require Import coqutil.Word.Bitwidth.
Require bedrock2.LeakageWeakestPrecondition.

Require Import Coq.Classes.Morphisms.

Section WeakestPrecondition.
  Context {width} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: LeakageSemantics.ExtSpec} {pick_sp: LeakageSemantics.PickSp}.

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
      [  constr_eq T X; move x before pick_sp
       | constr_eq T X; move x before ext_spec
       | constr_eq T X; move x before locals
       | constr_eq T X; move x at top
       | revert x ] end;
    match goal with x : X |- _ => induction x end;
    intros.

  Local Hint Mode word.word - : typeclass_instances.

  (* we prove weakening lemmas for all WP definitions in a syntax-directed fashion,
   * moving from postcondition towards precondition one logical connective at a time. *)
  Global Instance Proper_literal : Proper (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)) LeakageWeakestPrecondition.literal.
  Proof using. clear. cbv [LeakageWeakestPrecondition.literal]; cbv [Proper respectful pointwise_relation Basics.impl dlet.dlet]. eauto. Qed.

  Global Instance Proper_get : Proper (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))) LeakageWeakestPrecondition.get.
  Proof using. clear. cbv [LeakageWeakestPrecondition.get]; cbv [Proper respectful pointwise_relation Basics.impl]; intros * ? (?&?&?); eauto. Qed.

  Global Instance Proper_load : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) LeakageWeakestPrecondition.load.
  Proof using. clear. cbv [LeakageWeakestPrecondition.load]; cbv [Proper respectful pointwise_relation Basics.impl]; intros * ? (?&?&?); eauto. Qed.

  Global Instance Proper_store : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))))) LeakageWeakestPrecondition.store.
  Proof using. clear. cbv [LeakageWeakestPrecondition.store]; cbv [Proper respectful pointwise_relation Basics.impl]; intros * ? (?&?&?); eauto. Qed.

  Global Instance Proper_expr : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ (pointwise_relation _ Basics.impl) ==> Basics.impl)))))) LeakageWeakestPrecondition.expr.
  Proof using.
    clear.
    cbv [Proper respectful pointwise_relation Basics.impl LeakageSemantics.leak_binop]; ind_on Syntax.expr.expr;
      cbn in *; intuition (try typeclasses eauto with core).
    { eapply Proper_literal; eauto. cbv [pointwise_relation Basics.impl]. auto. }
    { eapply Proper_get; eauto. cbv [pointwise_relation Basics.impl]. auto. }
    { eapply IHa2; eauto; intuition idtac. eapply Proper_load; eauto using Proper_load.
      cbv [pointwise_relation Basics.impl]. auto. }
    { eapply IHa2; eauto; intuition idtac. eapply Proper_load; eauto using Proper_load.
      cbv [pointwise_relation Basics.impl]. auto. }
    { eapply IHa2_1; eauto; intuition idtac.
      Tactics.destruct_one_match; eauto using Proper_load. }
  Qed.

  Global Instance Proper_list_map {A B} :
    Proper ((pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) ==> pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) (LeakageWeakestPrecondition.list_map (A:=A) (B:=B)).
  Proof using.
    clear.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on (list A);
      cbn in *; intuition (try typeclasses eauto with core).
  Qed.

  Global Instance Proper_list_map' {A B T} :
    Proper ((pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl) ==> Basics.impl)) ==> pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl) ==> Basics.impl)))) (LeakageWeakestPrecondition.list_map' (A:=A) (B:=B) (T:=T)).
  Proof using.
    clear.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on (list A);
      cbn in *; intuition (try typeclasses eauto with core).
  Qed.

  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : LeakageSemantics.ext_spec.ok ext_spec}.

  Global Instance Proper_cmd :
    Proper (
     (pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl)))) ==>
     Basics.impl)))))))) LeakageWeakestPrecondition.cmd.
  Proof using ext_spec_ok locals_ok mem_ok word_ok.
    pose proof I. (* to keep naming *)
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl]; ind_on Syntax.cmd.cmd;
      cbn in *; cbv [dlet.dlet] in *; intuition eauto.
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      1: eapply Proper_expr.
      1: cbv [pointwise_relation Basics.impl]; intuition eauto 2.
      all: eauto. all: destruct H3; auto. }
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      { eapply Proper_expr; eauto; cbv [pointwise_relation Basics.impl]; eauto. }
      { destruct H2 as (?&?&?&?). eexists. eexists. split.
        { eapply Proper_expr; eauto; cbv [pointwise_relation Basics.impl]; eauto. }
        { eapply Proper_store; eauto; cbv [pointwise_relation Basics.impl]; eauto. } } }
    { eapply H1. 2: eapply H3; eassumption.
      intros ? ? ? ? (?&?&?&?&?). eauto 7. }
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      { eapply Proper_expr; eauto; cbv [pointwise_relation Basics.impl]; eauto. }
      { intuition eauto 6. } }
    { eapply H4; eauto. simpl. intros. eauto. }
    { eapply LeakageSemantics.exec.weaken; eassumption. }
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      { eapply Proper_list_map'; eauto; try exact H4; cbv [respectful pointwise_relation Basics.impl]; intuition eauto 2.
        eapply Proper_expr; eauto. }
      { eapply LeakageSemantics.weaken_call. 1: eassumption. cbv beta.
        (* COQBUG (performance), measured in Coq 8.9:
           "firstorder eauto" works, but takes ~100s and increases memory usage by 1.8GB.
           On the other hand, the line below takes just 5ms *)
        cbv beta; intros ? ? ? ? (?&?&?); eauto. } }
    { destruct H1 as (?&?&?&?). eexists. eexists. split.
      { eapply Proper_list_map'; eauto; try exact H4; cbv [respectful pointwise_relation Basics.impl].
        { eapply Proper_expr; eauto. }
        { eauto. } }
      { destruct H2 as (mKeep & mGive & ? & ?).
        exists mKeep. exists mGive.
        split; [assumption|].
        eapply LeakageSemantics.ext_spec.weaken; [|solve[eassumption]].
        intros ? ? ? (?&?&?); eauto 10. } }
  Qed.

  Global Instance Proper_call :
    Proper (
     (pointwise_relation _ (
     (pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl)))) ==>
     Basics.impl))))))))) LeakageWeakestPrecondition.call.
  Proof using word_ok mem_ok locals_ok ext_spec_ok.
    cbv [Proper respectful pointwise_relation Basics.impl].
    intros. eapply LeakageSemantics.weaken_call; eassumption.
  Qed.

  Global Instance Proper_program :
    Proper (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl)))) ==>
     Basics.impl))))))) LeakageWeakestPrecondition.program.
  Proof using word_ok mem_ok locals_ok ext_spec_ok.
    cbv [Proper respectful pointwise_relation Basics.impl  LeakageWeakestPrecondition.program]; intros.
    eapply Proper_cmd;
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  LeakageWeakestPrecondition.func];
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
             | _ => progress cbv [dlet.dlet LeakageWeakestPrecondition.dexpr LeakageWeakestPrecondition.dexprs LeakageWeakestPrecondition.store] in *
             end; eauto.

  Lemma expr_sound: forall m l e k post (H : LeakageWeakestPrecondition.expr m l k e post),
    exists v k', LeakageSemantics.eval_expr m l e k = Some (v, k') /\ post k' v.
  Proof using word_ok.
    induction e; t.
    { destruct H. destruct H. eexists. eexists. rewrite H. eauto. }
    { eapply IHe in H; t. cbv [LeakageWeakestPrecondition.load] in H0; t. rewrite H. rewrite H0. eauto. }
    { eapply IHe in H; t. cbv [LeakageWeakestPrecondition.load] in H0; t. rewrite H. rewrite H0. eauto. }
    { eapply IHe1 in H; t. eapply IHe2 in H0; t. rewrite H, H0; eauto. }
    { eapply IHe1 in H; t. rewrite H. Tactics.destruct_one_match.
      { eapply IHe3 in H0; t. }
      { eapply IHe2 in H0; t. } }
  Qed.

  Import ZArith coqutil.Tactics.Tactics.

  Lemma expr_complete: forall m l e k v k',
    LeakageSemantics.eval_expr m l e k = Some (v, k') ->
    LeakageWeakestPrecondition.dexpr m l k e v k'.
  Proof using word_ok.
    induction e; cbn; intros.
    - inversion_clear H. split; reflexivity.
    - destruct_one_match_hyp. 2: discriminate. inversion H. subst.
      eexists. eauto.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      inversion H. subst. eapply Proper_expr.
      2: { eapply IHe. eassumption. }
      intros addr ? (?&?). subst. unfold LeakageWeakestPrecondition.load. eauto.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      inversion H. subst. eapply Proper_expr.
      2: { eapply IHe. eassumption. }
      intros addr ? (?&?). subst. unfold LeakageWeakestPrecondition.load. eauto.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      inversion H. subst. eapply Proper_expr.
      2: { eapply IHe1. eassumption. }
      intros v1 ? (?&?). subst.
      eapply Proper_expr.
      2: { eapply IHe2. eassumption. }
      intros v2 ? (?&?). subst.
      auto.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      inversion H. subst. eapply Proper_expr.
      2: { eapply IHe1. eassumption. }
      intros vc ? (?&?). subst.
      destr (word.eqb a (word.of_Z 0)).
      + eapply IHe3. eassumption.
      + eapply IHe2. eassumption.
  Qed.

  Lemma sound_args : forall m l args k P,
      LeakageWeakestPrecondition.list_map' (LeakageWeakestPrecondition.expr m l) k args P ->
      exists x k', LeakageSemantics.eval_call_args m l args k = Some (x, k') /\ P k' x.
  Proof using word_ok.
    induction args; cbn; repeat (subst; t).
    eapply expr_sound in H; t; rewrite H.
    eapply IHargs in H0. t; rewrite H0.
    eauto.
  Qed.

  Lemma sound_getmany l a P :
    LeakageWeakestPrecondition.list_map (LeakageWeakestPrecondition.get l) a P
    -> exists vs, map.getmany_of_list l a = Some vs /\ P vs.
  Proof using.
    cbv [map.getmany_of_list] in *.
    revert P l; induction a; cbn; repeat (subst; t).
    cbv [LeakageWeakestPrecondition.get] in H; t.
    epose proof (IHa _ l _); clear IHa; t.
    rewrite H. erewrite H1. eexists; split; eauto. exact H2.
    Unshelve.
    eapply Proper_list_map; try exact H0.
    all : cbv [respectful pointwise_relation Basics.impl LeakageWeakestPrecondition.get]; intros; cbv beta; t.
  Qed.

  Local Hint Constructors LeakageSemantics.exec : core.
  Lemma sound_cmd e c k t m l post (H: LeakageWeakestPrecondition.cmd e c k t m l post)
    : LeakageSemantics.exec e c k t m l post.
  Proof.
    ind_on Syntax.cmd; repeat (t; try match reverse goal with H : LeakageWeakestPrecondition.expr _ _ _ _ _ |- _ => eapply expr_sound in H end).
    { destruct (BinInt.Z.eq_dec (Interface.word.unsigned x) (BinNums.Z0)) as [Hb|Hb]; cycle 1.
      { econstructor; t. }
      { eapply LeakageSemantics.exec.if_false; t. } }
    { inversion H0. t. eapply sound_args in H; t. }
    { eapply sound_args in H; t. }
  Qed.

  Lemma weaken_cmd: forall e c k t m l (post1 post2: _->_->_->_->Prop),
      LeakageWeakestPrecondition.cmd e c k t m l post1 ->
      (forall k t m l, post1 k t m l -> post2 k t m l) ->
      LeakageWeakestPrecondition.cmd e c k t m l post2.
  Proof.
    intros.
    eapply Proper_cmd. 2: eassumption.
    cbv [RelationClasses.Reflexive Morphisms.pointwise_relation
         Morphisms.respectful Basics.impl].
    assumption.
  Qed.

  Lemma complete_args : forall m l args k vs k',
      LeakageSemantics.eval_call_args m l args k = Some (vs, k') ->
      LeakageWeakestPrecondition.dexprs m l k args vs k'.
  Proof using word_ok.
    induction args; cbn; repeat (subst; t).
    1: inversion H; auto.
    destruct_one_match_hyp. 2: discriminate.
    do 2 destruct_one_match_hyp. 2: discriminate.
    destruct_one_match_hyp.
    inversion H. subst. clear H.
    eapply Proper_expr. 2: eapply expr_complete. 2: eassumption.
    intros x ? (?&?). subst.
    eapply Proper_list_map'. 3: eapply IHargs; eassumption.
    { eapply Proper_expr. }
    { intros ? ? (?&?). subst. split; reflexivity. }
  Qed.

  Lemma complete_cmd: forall e c k t m l post,
      LeakageSemantics.exec e c k t m l post ->
      LeakageWeakestPrecondition.cmd e c k t m l post.
  Proof.
    induction 1.
    { eassumption. }
    { eapply expr_complete in H. eexists. eexists. split. 1: exact H.
      eassumption. }
    { eauto. }
    { eapply expr_complete in H.
      eapply expr_complete in H0.
      eexists. eexists. split. 1: eassumption.
      eexists. eexists. split. 1: eassumption.
      eexists. eauto. }
    { split. 1: assumption.
      intros * HA HSp. specialize H1 with (1 := HA) (2 := HSp).
      unfold dlet.dlet. eapply weaken_cmd. 1: eapply H1. cbv beta.
      clear. intros * (? & ? & ? & ? & ?). eauto 8. }
    { eexists. eexists. ssplit; intros; eauto using expr_complete; congruence. }
    { eexists. eexists. ssplit; intros; eauto using expr_complete; congruence. }
    { cbn. eapply weaken_cmd.
      { eapply IHexec. }
      cbv beta. intros.
      eapply H1. eassumption. }
    { cbn. eapply LeakageSemantics.exec.while_false; eauto. }
    { rename IHexec into IH1, H3 into IH2.
      cbn. eapply LeakageSemantics.exec.while_true; eassumption. }
    { cbn. eexists. eexists. split.
      { eapply complete_args. eassumption. }
      unfold LeakageSemantics.call. do 4 eexists. 1: eassumption. do 2 eexists. 1: eassumption.
      eapply LeakageSemantics.exec.weaken.
      { eassumption. }
      cbv beta. intros.
      specialize H3 with (1 := H4). destruct H3 as (retvs & G & ? & ? & ?). eauto 8. }
    { cbn. eexists. eexists. split.
      { eapply complete_args. eassumption. }
      eexists _, _. split. 1: eassumption.
      eapply LeakageSemantics.ext_spec.weaken. 2: eassumption.
      intros m0 args0 k0 Hmid. specialize H2 with (1 := Hmid). destruct H2 as (? & ? & ?).
      eauto 8. }
  Qed.

  Lemma start_func: forall e fname fimpl k t m args post,
      map.get e fname = Some fimpl ->
      LeakageWeakestPrecondition.func e fimpl k t m args post ->
      LeakageWeakestPrecondition.call e fname k t m args post.
  Proof.
    intros * G. destruct fimpl as [[argnames retnames] body]. intros (? & ? & ?).
    do 4 eexists. 1: eassumption. do 2 eexists. 1: eassumption. eapply sound_cmd.
    eapply weaken_cmd. 1: eassumption. cbv beta. intros. eapply sound_getmany. assumption.
  Qed.

  (** Ad-hoc lemmas here? *)

  Import bedrock2.Syntax bedrock2.LeakageSemantics bedrock2.LeakageWeakestPrecondition.
  Lemma interact_nomem call action binds arges k t m l post
        args k' (Hargs : dexprs m l k arges args k')
        (Hext : ext_spec t map.empty binds args (fun mReceive (rets : list word) klist =>
           mReceive = map.empty /\
           exists l0 : locals, map.putmany_of_list_zip action rets l = Some l0 /\
           post (leak_list klist :: k')%list (cons (map.empty, binds, args, (map.empty, rets)) t) m l0))
    : LeakageWeakestPrecondition.cmd call (cmd.interact action binds arges) k t m l post.
  Proof using word_ok mem_ok ext_spec_ok.
    exists args, k'; split; [exact Hargs|].
    exists m.
    exists map.empty.
    split; [eapply Properties.map.split_empty_r; exact eq_refl|].
    eapply ext_spec.weaken; [|eapply Hext]; intros ? ? ? [? [? []]]. subst a; subst.
    eexists; split; [eassumption|].
    intros. eapply Properties.map.split_empty_r in H. subst. assumption.
  Qed.

  Lemma intersect_expr: forall m l e k (post1 post2: leakage -> word -> Prop),
      LeakageWeakestPrecondition.expr m l k e post1 ->
      LeakageWeakestPrecondition.expr m l k e post2 ->
      LeakageWeakestPrecondition.expr m l k e (fun k v => post1 k v /\ post2 k v).
  Proof using word_ok.
    induction e; cbn; unfold literal, dlet.dlet, LeakageWeakestPrecondition.get; intros.
    - eauto.
    - decompose [and ex] H. decompose [and ex] H0. assert (x0 = x1) by congruence. subst. eauto.
    - eapply Proper_expr.
      2: eapply IHe.
      2: eapply H.
      2: eapply H0.
      unfold Morphisms.pointwise_relation, Basics.impl.
      unfold load. intros. decompose [and ex] H1. assert (x0 = x) by congruence. subst. eauto.
    - eapply Proper_expr.
      2: eapply IHe.
      2: eapply H.
      2: eapply H0.
      unfold Morphisms.pointwise_relation, Basics.impl.
      unfold load. intros. decompose [and ex] H1. assert (x0 = x) by congruence. subst. eauto.
    - eapply Proper_expr.
      2: eapply IHe1.
      2: eapply H.
      2: eapply H0.
      unfold Morphisms.pointwise_relation, Basics.impl.
      unfold load. intros. decompose [and ex] H1.
      eapply IHe2; eassumption.
    - eapply Proper_expr.
      2: eapply IHe1.
      2: eapply H.
      2: eapply H0.
      unfold Morphisms.pointwise_relation, Basics.impl.
      intros ? ? [? ?]. Tactics.destruct_one_match; eauto using Proper_expr.
  Qed.

  Lemma dexpr_expr (m : mem) l e k P
    (H : LeakageWeakestPrecondition.expr m l k e P)
    : exists v k', LeakageWeakestPrecondition.dexpr m l k e v k' /\ P k' v.
  Proof using word_ok.
    generalize dependent P; revert k; induction e; cbn.
    { cbv [LeakageWeakestPrecondition.literal dlet.dlet]; cbn; eauto. }
    { cbv [LeakageWeakestPrecondition.get]; intros ? ? (?&?&?). eauto 7. }
    { intros k P H; case (IHe _ _ H) as (?&?&?&?&?&?); clear IHe H.
      cbv [LeakageWeakestPrecondition.dexpr] in *.
      eexists; eexists; split; [|eassumption].
      eapply Proper_expr; [|eauto].
      intros ? ? (?&?); subst.
      eexists; eauto. }
    { intros k P H; case (IHe _ _ H) as (?&?&?&?&?&?); clear IHe H.
      cbv [LeakageWeakestPrecondition.dexpr] in *.
      eexists; eexists; split; [|eassumption].
      eapply Proper_expr; [|eauto].
      intros ? ? (?&?); subst.
      eexists; eauto. }
    { intros k P H.
      case (IHe1 _ _ H) as (?&?&?&H'); case (IHe2 _ _ H') as (?&?&?&?);
      clear IHe1 IHe2 H H'.
      cbv [LeakageWeakestPrecondition.dexpr] in *.
      eexists; eexists; split; [|eassumption].
      eapply Proper_expr; [|eauto]; intros ? ? []. subst.
      eapply Proper_expr; [|eauto]; intros ? ? []. subst.
      auto.
    }
    { intros k P H.
      case (IHe1 _ _ H) as (?&?&?&H'). Tactics.destruct_one_match_hyp.
      { case (IHe3 _ _ H') as (?&?&?&?).
        clear IHe1 IHe2 H H'.
        cbv [LeakageWeakestPrecondition.dexpr] in *.
        eexists; eexists; split; [|eassumption].
        eapply Proper_expr; [|eauto]; intros ? ? []. subst.
        rewrite word.eqb_eq by reflexivity. assumption. }
      { case (IHe2 _ _ H') as (?&?&?&?).
        clear IHe1 IHe3 H H'.
        cbv [LeakageWeakestPrecondition.dexpr] in *.
        eexists; eexists; split; [|eassumption].
        eapply Proper_expr; [|eauto]; intros ? ? []. subst.
        Tactics.destruct_one_match. 1: contradiction. assumption. } }
  Qed.
End WeakestPrecondition.
