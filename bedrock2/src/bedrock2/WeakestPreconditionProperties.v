Require Import coqutil.Macros.subst coqutil.Macros.unique coqutil.Map.Interface coqutil.Word.Properties.
Require Import coqutil.Word.Bitwidth.
Require bedrock2.WeakestPrecondition.
Require Import bedrock2.WP.

Require Import Coq.Classes.Morphisms.

Section WeakestPrecondition.
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
  Global Instance Proper_literal : Proper (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)) WeakestPrecondition.literal.
  Proof using. clear. cbv [WeakestPrecondition.literal]; cbv [Proper respectful pointwise_relation Basics.impl dlet.dlet]. eauto. Qed.

  Global Instance Proper_get : Proper (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))) WeakestPrecondition.get.
  Proof using. clear. cbv [WeakestPrecondition.get]; cbv [Proper respectful pointwise_relation Basics.impl]; intros * ? (?&?&?); eauto. Qed.

  Global Instance Proper_load : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) WeakestPrecondition.load.
  Proof using. clear. cbv [WeakestPrecondition.load]; cbv [Proper respectful pointwise_relation Basics.impl]; intros * ? (?&?&?); eauto. Qed.

  Global Instance Proper_store : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))))) WeakestPrecondition.store.
  Proof using. clear. cbv [WeakestPrecondition.store]; cbv [Proper respectful pointwise_relation Basics.impl]; intros * ? (?&?&?); eauto. Qed.

  Global Instance Proper_expr : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) WeakestPrecondition.expr.
  Proof using.
    clear.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on Syntax.expr.expr;
      cbn in *; intuition (try typeclasses eauto with core).
    { eapply Proper_literal; eauto. }
    { eapply Proper_get; eauto. }
    { eapply IHa1; eauto; intuition idtac. eapply Proper_load; eauto using Proper_load. }
    { eapply IHa1; eauto; intuition idtac. eapply Proper_load; eauto using Proper_load. }
    { eapply IHa1_1; eauto; intuition idtac.
      Tactics.destruct_one_match; eauto using Proper_load. }
  Qed.

  Global Instance Proper_list_map {A B} :
    Proper ((pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) ==> pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) (WeakestPrecondition.list_map (A:=A) (B:=B)).
  Proof using.
    clear.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on (list A);
      cbn in *; intuition (try typeclasses eauto with core).
  Qed.

  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Global Instance Proper_cmd :
    Proper (
     (pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl))) ==>
     Basics.impl))))))) WeakestPrecondition.cmd.
  Proof using ext_spec_ok locals_ok mem_ok word_ok.
    pose proof I. (* to keep naming *)
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl]; ind_on Syntax.cmd.cmd;
      cbn in *; cbv [dlet.dlet] in *; intuition (try typeclasses eauto with core).
    { destruct H1 as (?&?&?). eexists. split.
      1: eapply Proper_expr.
      1: cbv [pointwise_relation Basics.impl]; intuition eauto 2.
      all: eauto. }
    { destruct H1 as (?&?&?). eexists. split.
      { eapply Proper_expr.
        { cbv [pointwise_relation Basics.impl]; intuition eauto 2. }
        { eauto. } }
      { destruct H2 as (?&?&?). eexists. split.
        { eapply Proper_expr.
          { cbv [pointwise_relation Basics.impl]; intuition eauto 2. }
          { eauto. } }
        { eapply Proper_store; eauto; cbv [pointwise_relation Basics.impl]; eauto. } } }
    { eapply H1. 2: eapply H3; eassumption.
      intros ? ? ? (?&?&?&?&?). eauto 7. }
    { destruct H1 as (?&?&?). eexists. split.
      { eapply Proper_expr.
        { cbv [pointwise_relation Basics.impl]; intuition eauto 2. }
        { eauto. } }
      { intuition eauto 6. } }
    { eapply weaken_wp_cmd; eassumption. }
    { destruct H1 as (?&?&?). eexists. split.
      { eapply Proper_list_map; eauto; try exact H4; cbv [respectful pointwise_relation Basics.impl]; intuition eauto 2.
        eapply Proper_expr; eauto. }
      { eapply weaken_wp_call. 2: eassumption. cbv beta.
        (* COQBUG (performance), measured in Coq 8.9:
           "firstorder eauto" works, but takes ~100s and increases memory usage by 1.8GB.
           On the other hand, the line below takes just 5ms *)
        cbv beta; intros ? ? ? (?&?&?); eauto. } }
    { destruct H1 as (?&?&?). eexists. split.
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
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl))) ==>
     Basics.impl)))))))) WeakestPrecondition.call.
  Proof using word_ok mem_ok locals_ok ext_spec_ok.
    cbv [Proper respectful pointwise_relation Basics.impl].
    intros. eapply weaken_wp_call; eassumption.
  Qed.

  Ltac t :=
      repeat match goal with
             | |- forall _, _ => progress intros
             | H: exists _, _ |- _ => destruct H
             | H: and _ _ |- _ => destruct H
             | H: eq _ ?y |- _ => subst y
             | H: False |- _ => destruct H
             | _ => progress cbn in *
             | _ => progress cbv [dlet.dlet WeakestPrecondition.dexpr WeakestPrecondition.dexprs WeakestPrecondition.store] in *
             end; eauto.

  Lemma expr_sound: forall m l e mc post (H : WeakestPrecondition.expr m l e post),
    exists v mc', Semantics.eval_expr m l e mc = Some (v, mc') /\ post v.
  Proof using word_ok.
    induction e; t.
    { destruct H. destruct H. eexists. eexists. rewrite H. eauto. }
    { eapply IHe in H; t. cbv [WeakestPrecondition.load] in H0; t. rewrite H. rewrite H0. eauto. }
    { eapply IHe in H; t. cbv [WeakestPrecondition.load] in H0; t. rewrite H. rewrite H0. eauto. }
    { eapply IHe1 in H; t. eapply IHe2 in H0; t. rewrite H, H0; eauto. }
    { eapply IHe1 in H; t. rewrite H. Tactics.destruct_one_match.
      { eapply IHe3 in H0; t. }
      { eapply IHe2 in H0; t. } }
  Qed.

  Import ZArith coqutil.Tactics.Tactics.

  Lemma expr_complete: forall m l e mc v mc',
    Semantics.eval_expr m l e mc = Some (v, mc') ->
    WeakestPrecondition.dexpr m l e v.
  Proof using word_ok.
    induction e; cbn; intros.
    - inversion_clear H. reflexivity.
    - destruct_one_match_hyp. 2: discriminate. inversion H. subst r.
      eexists. eauto.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      inversion H. subst r0 mc'. clear H.
      eapply Proper_expr.
      2: { eapply IHe. eassumption. }
      intros addr ?. subst r. unfold WeakestPrecondition.load. eauto.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      inversion H. subst r0 mc'. clear H.
      eapply Proper_expr.
      2: { eapply IHe. eassumption. }
      intros addr ?. subst r. unfold WeakestPrecondition.load. eauto.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      inversion H. subst v mc'. clear H.
      eapply Proper_expr.
      2: { eapply IHe1. eassumption. }
      intros v1 ?. subst r.
      eapply Proper_expr.
      2: { eapply IHe2. eassumption. }
      intros v2 ?. subst r0.
      reflexivity.
    - repeat (destruct_one_match_hyp; try discriminate; []).
      eapply Proper_expr.
      2: { eapply IHe1. eassumption. }
      intros vc ?. subst r.
      destr (word.eqb vc (word.of_Z 0)).
      + eapply IHe3. eassumption.
      + eapply IHe2. eassumption.
  Qed.

  Lemma eval_expr_change_start_metrics: forall m l e mc1 mc1' v,
      Semantics.eval_expr m l e mc1 = Some (v, mc1') ->
      forall mc2, exists mc2', Semantics.eval_expr m l e mc2 = Some (v, mc2').
  Proof.
    intros. eapply expr_complete in H. eapply expr_sound in H.
    destruct H as (? & mc2' & H & ?). subst v. exists mc2'. exact H.
  Qed.

  Lemma sound_args : forall m l args mc P,
      WeakestPrecondition.list_map (WeakestPrecondition.expr m l) args P ->
      exists x mc', Semantics.evaluate_call_args_log m l args mc = Some (x, mc') /\ P x.
  Proof using word_ok.
    induction args; cbn; repeat (subst; t).
    unfold Semantics.eval_expr in *.
    eapply expr_sound in H; t; rewrite H.
    eapply IHargs in H0; t; rewrite H0.
    eauto.
  Qed.

  Lemma sound_getmany l a P :
    WeakestPrecondition.list_map (WeakestPrecondition.get l) a P
    -> exists vs, map.getmany_of_list l a = Some vs /\ P vs.
  Proof using.
    cbv [map.getmany_of_list] in *.
    revert P l; induction a; cbn; repeat (subst; t).
    cbv [WeakestPrecondition.get] in H; t.
    epose proof (IHa _ l _); clear IHa; t.
    rewrite H. erewrite H1. eexists; split; eauto. exact H2.
    Unshelve.
    eapply Proper_list_map; try exact H0.
    all : cbv [respectful pointwise_relation Basics.impl WeakestPrecondition.get]; intros; cbv beta; t.
  Qed.

  Local Notation semantics_call := (fun e n t m args post =>
    exists params rets fbody, map.get e n = Some (params, rets, fbody) /\
    exists lf, map.putmany_of_list_zip params args map.empty = Some lf /\
    forall mc', Semantics.exec e fbody t m lf mc' (fun t' m' st1 mc'' =>
      exists retvs, map.getmany_of_list st1 rets = Some retvs /\
      post t' m' retvs)).

  Local Hint Constructors Semantics.exec : core.
  Lemma sound_cmd e c t m l mc post
        (H:WeakestPrecondition.cmd e c t m l post)
    : Semantics.exec e c t m l mc (fun t' m' l' mc' => post t' m' l').
  Proof.
    ind_on Syntax.cmd; repeat (t; try match reverse goal with H : WeakestPrecondition.expr _ _ _ _ |- _ => eapply expr_sound in H end).
    { destruct (BinInt.Z.eq_dec (Interface.word.unsigned x) (BinNums.Z0)) as [Hb|Hb]; cycle 1.
      { econstructor; t. }
      { eapply Semantics.exec.if_false; t. } }
    { eapply invert_wp_cmd. assumption. }
    { eapply invert_wp_call in H0. t. eapply sound_args in H; t.
      eapply invert_wp_cmd in H2. t. }
    { eapply sound_args in H; t. }
  Qed.

  Lemma cmd_sound: forall e c t m l post,
      WeakestPrecondition.cmd e c t m l post -> wp_cmd e c t m l post.
  Proof. intros. eapply mk_wp_cmd. intros. eapply sound_cmd. assumption. Qed.

  Lemma sound_call' fs n t m args post (H : WeakestPrecondition.call fs n t m args post)
    : semantics_call fs n t m args post.
  Proof.
    cbv beta. eapply invert_wp_call in H.
    destruct H as (? & ? & ? & ? & ? & ? & ?).
    do 4 eexists. 1: eassumption.
    do 2 eexists. 1: eassumption.
    eapply invert_wp_cmd. eassumption.
  Qed.

  Lemma weaken_cmd: forall e c t m l (post1 post2: _->_->_->Prop),
      WeakestPrecondition.cmd e c t m l post1 ->
      (forall t m l, post1 t m l -> post2 t m l) ->
      WeakestPrecondition.cmd e c t m l post2.
  Proof.
    intros.
    eapply Proper_cmd. 2: eassumption.
    cbv [RelationClasses.Reflexive Morphisms.pointwise_relation
         Morphisms.respectful Basics.impl].
    assumption.
  Qed.

  Lemma complete_args : forall m l args mc mc' vs,
      Semantics.evaluate_call_args_log m l args mc = Some (vs, mc') ->
      WeakestPrecondition.dexprs m l args vs.
  Proof using word_ok.
    induction args; cbn; repeat (subst; t).
    1: inversion H; reflexivity.
    destruct_one_match_hyp. 2: discriminate.
    destruct p as (v, mc'').
    destruct_one_match_hyp. 2: discriminate.
    destruct p as (tail, mc''').
    inversion H. subst mc''' vs. clear H.
    eapply Proper_expr. 2: eapply expr_complete. 2: eassumption.
    intros x ?. subst x.
    eapply Proper_list_map. 3: eapply IHargs; eassumption.
    { eapply Proper_expr. }
    { intros ? ?. subst. reflexivity. }
  Qed.

  Lemma complete_cmd: forall e c t m l mc post,
      Semantics.exec e c t m l mc post ->
      WeakestPrecondition.cmd e c t m l (fun t' m' l' => exists mc', post t' m' l' mc').
  Proof.
    induction 1.
    { eexists. eassumption. }
    { eapply expr_complete in H. eexists. split. 1: exact H.
      eexists. eassumption. }
    { eexists. eauto. }
    { eapply expr_complete in H.
      eapply expr_complete in H0.
      eexists. split. 1: eassumption.
      eexists. split. 1: eassumption.
      eexists. eauto. }
    { split. 1: assumption.
      intros * HA HSp. specialize H1 with (1 := HA) (2 := HSp).
      unfold dlet.dlet. eapply weaken_cmd. 1: eapply H1. cbv beta.
      clear. intros * (? & ? & ? & ? & ? & ?). eauto 8. }
    { eexists. ssplit; intros; eauto using expr_complete; congruence. }
    { eexists. ssplit; intros; eauto using expr_complete; congruence. }
    { cbn. eapply weaken_cmd.
      { eapply IHexec. }
      cbv beta. intros *. intros (mc' & Hmid).
      eapply H1. eassumption. }
    { cbn. eapply mk_wp_cmd. intros.
      eapply eval_expr_change_start_metrics in H.
      destruct H as (mc2' & H).
      eapply Semantics.exec.while_false; eauto. }
    { rename IHexec into IH1, H3 into IH2.
      cbn. eapply mk_wp_cmd. intros.
      eapply eval_expr_change_start_metrics in H.
      destruct H as (mc2' & H).
      eapply Semantics.exec.while_true.
      1: eassumption.
      1: eassumption.
      { eapply sound_cmd. eapply IH1. (* round-trip just to change metrics *) }
      cbv beta. intros * (? & ?).
      eapply sound_cmd. eapply IH2. (* round-trip just to change metrics *) eassumption. }
    { cbn. eexists. split.
      { eapply complete_args. eassumption. }
      eapply mk_wp_call. 1,2: eassumption.
      eapply mk_wp_cmd. intros.
      eapply Semantics.exec.weaken.
      { eapply sound_cmd in IHexec. eapply IHexec. (* round-trip just to change metrics *) }
      cbv beta. intros * ? (? & Hmid).
      specialize H3 with (1 := Hmid). destruct H3 as (retvs & G & ? & ? & ?). eauto 8. }
    { cbn. eexists. split.
      { eapply complete_args. eassumption. }
      eexists _, _. split. 1: eassumption.
      eapply Semantics.ext_spec.weaken. 2: eassumption.
      intros m0 args0 Hmid. specialize H2 with (1 := Hmid). destruct H2 as (? & ? & ?).
      eauto 8. }
  Qed.

  Lemma cmd_complete: forall e c t m l post,
      wp_cmd e c t m l post -> WeakestPrecondition.cmd e c t m l post.
  Proof.
    intros. eapply invert_wp_cmd in H. eapply complete_cmd in H.
    eapply weaken_cmd. 1: exact H.
    cbv beta. intros * (_ & ?). assumption.
    Unshelve. repeat constructor.
  Qed.

  Lemma start_func: forall e fname fimpl t m args post,
      map.get e fname = Some fimpl ->
      WeakestPrecondition.func e fimpl t m args post ->
      wp_call e fname t m args post.
  Proof.
    intros * G. destruct fimpl as [[argnames retnames] body]. intros (? & ? & ?).
    eapply mk_wp_call. 1,2: eassumption. eapply cmd_sound.
    eapply weaken_cmd. 1: eassumption. cbv beta. intros. eapply sound_getmany. assumption.
  Qed.

  (** Ad-hoc lemmas here? *)

  Import bedrock2.Syntax bedrock2.Semantics bedrock2.WeakestPrecondition.
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
  Qed.

  Lemma intersect_expr: forall m l e (post1 post2: word -> Prop),
      WeakestPrecondition.expr m l e post1 ->
      WeakestPrecondition.expr m l e post2 ->
      WeakestPrecondition.expr m l e (fun v => post1 v /\ post2 v).
  Proof using word_ok.
    induction e; cbn; unfold literal, dlet.dlet, WeakestPrecondition.get; intros.
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
      intros ? [? ?]. Tactics.destruct_one_match; eauto using Proper_expr.
  Qed.

  Lemma dexpr_expr (m : mem) l e P
    (H : WeakestPrecondition.expr m l e P)
    : exists v, WeakestPrecondition.dexpr m l e v /\ P v.
  Proof using word_ok.
    revert dependent P; induction e; cbn.
    { cbv [WeakestPrecondition.literal dlet.dlet]; cbn; eauto. }
    { cbv [WeakestPrecondition.get]; intros ?(?&?&?); eauto. }
    { intros v H; case (IHe _ H) as (?&?&?&?&?); clear IHe H.
      cbv [WeakestPrecondition.dexpr] in *.
      eexists; split; [|eassumption].
      eapply Proper_expr; [|eauto].
      intros ? ?; subst.
      eexists; eauto. }
    { intros v H; case (IHe _ H) as (?&?&?&?&?); clear IHe H.
      cbv [WeakestPrecondition.dexpr] in *.
      eexists; split; [|eassumption].
      eapply Proper_expr; [|eauto].
      intros ? ?; subst.
      eexists; eauto. }
    { intros P H.
      case (IHe1 _ H) as (?&?&H'); case (IHe2 _ H') as (?&?&?);
      clear IHe1 IHe2 H H'.
      cbv [WeakestPrecondition.dexpr] in *.
      eexists; split; [|eassumption].
      eapply Proper_expr; [|eauto]; intros ? [].
      eapply Proper_expr; [|eauto]; intros ? [].
      trivial.
    }
    { intros P H.
      case (IHe1 _ H) as (?&?&H'). Tactics.destruct_one_match_hyp.
      { case (IHe3 _ H') as (?&?&?).
        clear IHe1 IHe2 H H'.
        cbv [WeakestPrecondition.dexpr] in *.
        eexists; split; [|eassumption].
        eapply Proper_expr; [|eauto]; intros ? [].
        rewrite word.eqb_eq by reflexivity. assumption. }
      { case (IHe2 _ H') as (?&?&?).
        clear IHe1 IHe3 H H'.
        cbv [WeakestPrecondition.dexpr] in *.
        eexists; split; [|eassumption].
        eapply Proper_expr; [|eauto]; intros ? [].
        Tactics.destruct_one_match. 1: contradiction. assumption. } }
  Qed.
End WeakestPrecondition.
