Require Import coqutil.sanity coqutil.Byte.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Z.Lia.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Bitwidth.
Require Export bedrock2.Memory.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.Semantics.
Require Import bedrock2.LeakageSemantics.
Require Import bedrock2.MetricSemantics.
Require Import bedrock2.MetricLeakageSemantics.

Section MetricLeakageToSomething.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec} {pick_sp: PickSp}.

  Lemma metricleakage_to_plain_eval_expr: forall m l e v,
      Semantics.eval_expr m l e = Some v ->
      forall k mc, exists k' mc', MetricLeakageSemantics.eval_expr m l e k mc = Some (v, k', mc').
  Proof.
    induction e; cbn; intros;
      repeat match goal with
        | H: Some _ = Some _ |- _ => eapply Option.eq_of_eq_Some in H; subst
        | IH: forall _, Some _ = Some _ -> _ |- _ => specialize IH with (1 := eq_refl)
        | IH: forall _ _, Semantics.eval_expr _ _ _ = Some _ -> _ |- _ =>
            specialize (IH _ _ ltac:(eassumption))
        | IH: forall _: leakage, forall _: MetricLog, exists _: leakage, exists _: MetricLog,
            MetricLeakageSemantics.eval_expr ?m ?l ?e _ _ = Some _
          |- context[MetricLeakageSemantics.eval_expr ?m ?l ?e ?k ?mc] => specialize (IH k mc)
        | |- _ => progress fwd
        | |- _ => Tactics.destruct_one_match
        end;
      eauto.
  Qed.

  Lemma metricleakage_to_metric_eval_expr: forall m l e mc v mc',
      MetricSemantics.eval_expr m l e mc = Some (v, mc') ->
      forall k, exists k', MetricLeakageSemantics.eval_expr m l e k mc = Some (v, k', mc').
  Proof.
    induction e; cbn; intros;
      repeat match goal with
        | H: Some _ = Some _ |- _ => eapply Option.eq_of_eq_Some in H; subst
        | IH: forall _, Some _ = Some _ -> _ |- _ => specialize IH with (1 := eq_refl)
        | IH: forall _ _ _, MetricSemantics.eval_expr _ _ _ _ = Some _ -> _ |- _
          => specialize (IH _ _ _ ltac:(eassumption))
        | IH: forall _: leakage, exists _: leakage, MetricLeakageSemantics.eval_expr ?m ?l ?e _ _ = Some _
          |- context[MetricLeakageSemantics.eval_expr ?m ?l ?e ?k ?mc] => specialize (IH k)
        | |- _ => progress fwd
        | |- _ => Tactics.destruct_one_match
        end;
      eauto.
  Qed.

  Lemma metricleakage_to_leakage_eval_expr: forall m l e k v k',
      LeakageSemantics.eval_expr m l e k = Some (v, k') ->
      forall mc, exists mc', MetricLeakageSemantics.eval_expr m l e k mc = Some (v, k', mc').
  Proof.
    induction e; cbn; intros;
      repeat match goal with
        | H: Some _ = Some _ |- _ => eapply Option.eq_of_eq_Some in H; subst
        | IH: forall _, Some _ = Some _ -> _ |- _ => specialize IH with (1 := eq_refl)
        | IH: forall _ _ _, LeakageSemantics.eval_expr _ _ _ _ = Some _ -> _ |- _
          => specialize (IH _ _ _ ltac:(eassumption))
        | IH: forall _: MetricLog, exists _: MetricLog, MetricLeakageSemantics.eval_expr ?m ?l ?e _ _ = Some _
          |- context[MetricLeakageSemantics.eval_expr ?m ?l ?e ?k ?mc] => specialize (IH mc)
        | |- _ => progress fwd
        | |- _ => Tactics.destruct_one_match
        end;
      eauto.
  Qed.

  Lemma metricleakage_to_plain_eval_call_args: forall m l arges args,
      Semantics.eval_call_args m l arges = Some args ->
      forall k mc, exists k' mc', eval_call_args m l arges k mc = Some (args, k', mc').
  Proof.
    induction arges; cbn; intros.
    - eapply Option.eq_of_eq_Some in H. subst. eauto.
    - fwd.
      eapply metricleakage_to_plain_eval_expr in E. destruct E as (k' & mc' & E). rewrite E.
      specialize IHarges with (1 := eq_refl). specialize (IHarges k' mc').
      destruct IHarges as (k'' & mc'' & IH). rewrite IH. eauto.
  Qed.

  Lemma metricleakage_to_metric_eval_call_args: forall m l arges mc args mc',
      MetricSemantics.eval_call_args m l arges mc = Some (args, mc') ->
      forall k, exists k', eval_call_args m l arges k mc = Some (args, k', mc').
  Proof.
    induction arges; cbn; intros.
    - inversion H. subst. eauto.
    - fwd.
      eapply metricleakage_to_metric_eval_expr in E. destruct E as (k' & E). rewrite E.
      specialize (IHarges _ _ _ ltac:(eassumption) k').
      destruct IHarges as (k'' & IH). rewrite IH. eauto.
  Qed.

  Lemma metricleakage_to_leakage_eval_call_args: forall m l arges k args k',
      LeakageSemantics.eval_call_args m l arges k = Some (args, k') ->
      forall mc, exists mc', eval_call_args m l arges k mc = Some (args, k', mc').
  Proof.
    induction arges; cbn; intros.
    - inversion H. subst. eauto.
    - fwd.
      eapply metricleakage_to_leakage_eval_expr in E. destruct E as (mc' & E). rewrite E.
      specialize (IHarges _ _ _ ltac:(eassumption) mc').
      destruct IHarges as (mc'' & IH). rewrite IH. eauto.
  Qed.

  Definition deleakaged_ext_spec : Semantics.ExtSpec :=
    fun t mGive a args post => ext_spec t mGive a args (fun mReceive resvals klist => post mReceive resvals).
  
  Lemma deleakaged_ext_spec_ok {ext_spec_ok: ext_spec.ok ext_spec}:
    Semantics.ext_spec.ok deleakaged_ext_spec.
  Proof.
    destruct ext_spec_ok. cbv [deleakaged_ext_spec]. constructor; eauto.
    intros. cbv [Morphisms.Proper Morphisms.respectful Morphisms.pointwise_relation Basics.impl] in *.
    intros. eapply weaken; eauto. intros. apply H. simpl in *. assumption.
  Qed.    

  Context (e: env).
  Existing Instance deleakaged_ext_spec.
  Existing Instance deleakaged_ext_spec_ok.

  Lemma metricleakage_to_plain_exec: forall c t m l post,
      Semantics.exec e c t m l post ->
      forall k mc, MetricLeakageSemantics.exec e c k t m l mc (fun _ t' m' l' _ => post t' m' l').
  Proof.
    induction 1; intros;
      repeat match reverse goal with
        | H: Semantics.eval_expr _ _ _ = Some _ |- _ =>
            eapply metricleakage_to_plain_eval_expr in H; destruct H as (? & ? & H)
        | H: Semantics.eval_call_args _ _ _ = Some _ |- _ =>
            eapply metricleakage_to_plain_eval_call_args in H; destruct H as (? & ? & H)
        end;
      try solve [econstructor; eauto].
  Qed.

  Lemma metricleakage_to_metric_exec: forall c t m l mc post,
      MetricSemantics.exec e c t m l mc post ->
      forall k, MetricLeakageSemantics.exec e c k t m l mc (fun _ t' m' l' mc' => post t' m' l' mc').
  Proof.
    induction 1; intros;
      repeat match reverse goal with
        | H: MetricSemantics.eval_expr _ _ _ _ = Some _ |- _ =>
            eapply metricleakage_to_metric_eval_expr in H; destruct H as (? & H)
        | H: MetricSemantics.eval_call_args _ _ _ _ = Some _ |- _ =>
            eapply metricleakage_to_metric_eval_call_args in H; destruct H as (? & H)
        end;
      try solve [econstructor; eauto].
  Qed.

  Lemma metricleakage_to_leakage_exec: forall c t m l k post,
      LeakageSemantics.exec e c k t m l post ->
      forall mc, MetricLeakageSemantics.exec e c k t m l mc (fun k' t' m' l' _ => post k' t' m' l').
  Proof.
    induction 1; intros;
      repeat match reverse goal with
        | H: LeakageSemantics.eval_expr _ _ _ _ = Some _ |- _ =>
            eapply metricleakage_to_leakage_eval_expr in H; destruct H as (? & H)
        | H: LeakageSemantics.eval_call_args _ _ _ _ = Some _ |- _ =>
            eapply metricleakage_to_leakage_eval_call_args in H; destruct H as (? & H)
        end;
      try solve [econstructor; eauto].
  Qed.

  Lemma metricleakage_to_plain_call: forall f t m args post,
      Semantics.call e f t m args post ->
      forall k mc, MetricLeakageSemantics.call e f k t m args mc (fun _ t' m' rets _ => post t' m' rets).
  Proof.
    unfold MetricLeakageSemantics.call, Semantics.call. intros. fwd. eauto 10 using metricleakage_to_plain_exec.
  Qed.

  Lemma metricleakage_to_metric_call: forall f t m args mc post,
      MetricSemantics.call e f t m args mc post ->
      forall k, MetricLeakageSemantics.call e f k t m args mc (fun _ t' m' rets mc' => post t' m' rets mc').
  Proof.
    unfold MetricLeakageSemantics.call, MetricSemantics.call. intros. fwd. eauto 10 using metricleakage_to_metric_exec.
  Qed.

  Lemma metricleakage_to_leakage_call: forall f k t m args post,
      LeakageSemantics.call e f k t m args post ->
      forall mc, MetricLeakageSemantics.call e f k t m args mc (fun k' t' m' rets _ => post k' t' m' rets).
  Proof.
    unfold MetricLeakageSemantics.call, LeakageSemantics.call. intros. fwd. eauto 10 using metricleakage_to_leakage_exec.
  Qed.
End MetricLeakageToSomething.

Section LeakageToSomething.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec} {pick_sp: PickSp}.

  Lemma leakage_to_plain_eval_expr: forall m l e v,
      Semantics.eval_expr m l e = Some v ->
      forall k, exists k', LeakageSemantics.eval_expr m l e k = Some (v, k').
  Proof.
    induction e; cbn; intros;
      repeat match goal with
        | H: Some _ = Some _ |- _ => eapply Option.eq_of_eq_Some in H; subst
        | IH: forall _, Some _ = Some _ -> _ |- _ => specialize IH with (1 := eq_refl)
        | IH: forall _, Semantics.eval_expr _ _ _ = Some _ -> _ |- _ =>
            specialize (IH _ ltac:(eassumption))
        | IH: forall _: leakage, exists _: leakage,
            LeakageSemantics.eval_expr ?m ?l ?e _ = Some _
          |- context[LeakageSemantics.eval_expr ?m ?l ?e ?k] => specialize (IH k)
        | |- _ => progress fwd
        | |- _ => Tactics.destruct_one_match
        end;
      eauto.
  Qed.

  Lemma leakage_to_metric_eval_expr: forall m l e mc v mc',
      MetricSemantics.eval_expr m l e mc = Some (v, mc') ->
      forall k, exists k', LeakageSemantics.eval_expr m l e k = Some (v, k').
  Proof.
    induction e; cbn; intros;
      repeat match goal with
        | H: Some _ = Some _ |- _ => eapply Option.eq_of_eq_Some in H; subst
        | IH: forall _, Some _ = Some _ -> _ |- _ => specialize IH with (1 := eq_refl)
        | IH: forall _ _ _, MetricSemantics.eval_expr _ _ _ _ = Some _ -> _ |- _
          => specialize (IH _ _ _ ltac:(eassumption))
        | IH: forall _: leakage, exists _: leakage, LeakageSemantics.eval_expr ?m ?l ?e _ = Some _
          |- context[LeakageSemantics.eval_expr ?m ?l ?e ?k] => specialize (IH k)
        | |- _ => progress fwd
        | |- _ => Tactics.destruct_one_match
        end;
      eauto.
  Qed.

  Lemma leakage_to_metricleakage_eval_expr: forall m l e k v k' mc mc',
      MetricLeakageSemantics.eval_expr m l e k mc = Some (v, k', mc') ->
      LeakageSemantics.eval_expr m l e k = Some (v, k').
  Proof.
    induction e; cbn; intros;
      repeat match goal with
        | H: Some _ = Some _ |- _ => eapply Option.eq_of_eq_Some in H; subst
        | IH: forall _, Some _ = Some _ -> _ |- _ => specialize IH with (1 := eq_refl)
        | IH: forall _ _ _ _ _, MetricLeakageSemantics.eval_expr _ _ _ _ _ = Some _ -> _ |- _
          => specialize (IH _ _ _ _ _ ltac:(eassumption))
        | |- _ => progress fwd
        | |- _ => Tactics.destruct_one_match
        end;
      eauto.
  Qed.

  Lemma leakage_to_plain_eval_call_args: forall m l arges args,
      Semantics.eval_call_args m l arges = Some args ->
      forall k, exists k', LeakageSemantics.eval_call_args m l arges k = Some (args, k').
  Proof.
    induction arges; cbn; intros.
    - eapply Option.eq_of_eq_Some in H. subst. eauto.
    - fwd.
      eapply leakage_to_plain_eval_expr in E. destruct E as (k' & E). rewrite E.
      specialize IHarges with (1 := eq_refl). specialize (IHarges k').
      destruct IHarges as (k'' & IH). rewrite IH. eauto.
  Qed.

  Lemma leakage_to_metric_eval_call_args: forall m l arges mc args mc',
      MetricSemantics.eval_call_args m l arges mc = Some (args, mc') ->
      forall k, exists k', LeakageSemantics.eval_call_args m l arges k = Some (args, k').
  Proof.
    induction arges; cbn; intros.
    - inversion H. subst. eauto.
    - fwd.
      eapply leakage_to_metric_eval_expr in E. destruct E as (k' & E). rewrite E.
      specialize (IHarges _ _ _ ltac:(eassumption) k').
      destruct IHarges as (k'' & IH). rewrite IH. eauto.
  Qed.

  Lemma leakage_to_metricleakage_eval_call_args: forall m l arges k mc args k' mc',
      MetricLeakageSemantics.eval_call_args m l arges k mc = Some (args, k', mc') ->
      LeakageSemantics.eval_call_args m l arges k = Some (args, k').
  Proof.
    induction arges; cbn; intros.
    - inversion H. subst. eauto.
    - fwd.
      eapply leakage_to_metricleakage_eval_expr in E. rewrite E.
      specialize (IHarges _ _ _ _ _ ltac:(eassumption)).
      rewrite IHarges. eauto.
  Qed.

  Context (e: env).
  Existing Instance deleakaged_ext_spec.
  Existing Instance deleakaged_ext_spec_ok.

  Lemma leakage_to_plain_exec: forall c t m l post,
      Semantics.exec e c t m l post ->
      forall k, LeakageSemantics.exec e c k t m l (fun _ t' m' l' => post t' m' l').
  Proof.
    induction 1; intros;
      repeat match reverse goal with
        | H: Semantics.eval_expr _ _ _ = Some _ |- _ =>
            eapply leakage_to_plain_eval_expr in H; destruct H as (? & H)
        | H: Semantics.eval_call_args _ _ _ = Some _ |- _ =>
            eapply leakage_to_plain_eval_call_args in H; destruct H as (? & H)
        end;
      try solve [econstructor; eauto].
  Qed.

  Lemma leakage_to_metric_exec: forall c t m l mc post,
      MetricSemantics.exec e c t m l mc post ->
      forall k, LeakageSemantics.exec e c k t m l (fun _ t' m' l' => exists mc', post t' m' l' mc').
  Proof.
    induction 1; intros;
      repeat match reverse goal with
        | H: MetricSemantics.eval_expr _ _ _ _ = Some _ |- _ =>
            eapply leakage_to_metric_eval_expr in H; destruct H as (? & H)
        | H: MetricSemantics.eval_call_args _ _ _ _ = Some _ |- _ =>
            eapply leakage_to_metric_eval_call_args in H; destruct H as (? & H)
        end;
      try solve [econstructor; eauto].
    all: try solve [econstructor; eauto; simpl; intros; fwd; eauto].
    - econstructor; eauto. intros. eapply LeakageSemantics.exec.weaken.
      1: eapply H1; solve[eauto]. simpl. intros. fwd. eexists. eexists. eauto.
    - econstructor; eauto. simpl. intros. fwd. apply H3 in H4. fwd. eauto 10.
    - econstructor; eauto. simpl. intros. apply H2 in H3. fwd. eauto.
  Qed.

  Lemma leakage_to_metricleakage_exec: forall c t m l k mc post,
      MetricLeakageSemantics.exec e c k t m l mc post ->
      LeakageSemantics.exec e c k t m l (fun k' t' m' l' => exists mc', post k' t' m' l' mc').
  Proof.
    induction 1; intros;
      repeat match reverse goal with
        | H: MetricLeakageSemantics.eval_expr _ _ _ _ _ = Some _ |- _ =>
            eapply leakage_to_metricleakage_eval_expr in H
        | H: MetricLeakageSemantics.eval_call_args _ _ _ _ _ = Some _ |- _ =>
            eapply leakage_to_metricleakage_eval_call_args in H
        end;
      try solve [econstructor; eauto].
    all: try solve [econstructor; eauto; simpl; intros; fwd; eauto].
    - econstructor; eauto. intros. eapply LeakageSemantics.exec.weaken.
      1: eapply H1; solve[eauto]. simpl. intros. fwd. eexists. eexists. eauto.
    - econstructor; eauto. simpl. intros. fwd. apply H3 in H4. fwd. eauto 10.
    - econstructor; eauto. simpl. intros. apply H2 in H3. fwd. eauto.
  Qed.

  Lemma leakage_to_plain_call: forall f t m args post,
      Semantics.call e f t m args post ->
      forall k, LeakageSemantics.call e f k t m args (fun _ t' m' rets => post t' m' rets).
  Proof.
    unfold LeakageSemantics.call, Semantics.call. intros. fwd. eauto 10 using leakage_to_plain_exec.
  Qed.

  Lemma leakage_to_metric_call: forall f t m args mc post,
      MetricSemantics.call e f t m args mc post ->
      forall k, LeakageSemantics.call e f k t m args (fun _ t' m' rets => exists mc', post t' m' rets mc').
  Proof.
    unfold LeakageSemantics.call, MetricSemantics.call. intros. fwd. do 3 eexists.
    intuition eauto. eexists. intuition eauto. eapply LeakageSemantics.exec.weaken.
    - eauto 10 using leakage_to_metric_exec.
    - simpl. intros. fwd. eauto.
  Qed.

  Lemma leakage_to_metricleakage_call: forall f k t m args mc post,
      MetricLeakageSemantics.call e f k t m args mc post ->
      LeakageSemantics.call e f k t m args (fun k' t' m' rets => exists mc', post k' t' m' rets mc').
  Proof.
    unfold LeakageSemantics.call, MetricLeakageSemantics.call. intros. fwd.
    do 3 eexists. intuition eauto. eexists. intuition eauto.
    eapply LeakageSemantics.exec.weaken.
    - eauto 10 using leakage_to_metricleakage_exec.
    - simpl. intros. fwd. eauto.
  Qed.
End LeakageToSomething.

Section MetricToSomething.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: Semantics.ExtSpec}.

  Lemma metric_to_plain_eval_expr: forall (m : mem) l e v,
      Semantics.eval_expr m l e = Some v ->
      forall mc, exists mc', MetricSemantics.eval_expr m l e mc = Some (v, mc').
  Proof.
    induction e; cbn; intros;
      repeat match goal with
        | H: Some _ = Some _ |- _ => eapply Option.eq_of_eq_Some in H; subst
        | IH: forall _, Some _ = Some _ -> _ |- _ => specialize IH with (1 := eq_refl)
        | IH: forall _, Semantics.eval_expr _ _ _ = Some _ -> _ |- _ =>
            specialize (IH _ ltac:(eassumption))
        | IH: forall _: MetricLog, exists _: MetricLog,
            MetricSemantics.eval_expr ?m ?l ?e _ = Some _
          |- context[MetricSemantics.eval_expr ?m ?l ?e ?mc] => specialize (IH mc)
        | |- _ => progress fwd
        | |- _ => Tactics.destruct_one_match
        end;
      eauto.
  Qed.

  Lemma metric_to_plain_eval_call_args: forall (m : mem) l arges args,
      Semantics.eval_call_args m l arges = Some args ->
      forall mc, exists mc', MetricSemantics.eval_call_args m l arges mc = Some (args, mc').
  Proof.
    induction arges; cbn; intros.
    - eapply Option.eq_of_eq_Some in H. subst. eauto.
    - fwd.
      eapply metric_to_plain_eval_expr in E. destruct E as (mc' & E). rewrite E.
      specialize IHarges with (1 := eq_refl). specialize (IHarges mc').
      destruct IHarges as (mc'' & IH). rewrite IH. eauto.
  Qed.

  Context (e: env).

  Lemma metric_to_plain_exec: forall c t (m : mem) l post,
      Semantics.exec e c t m l post ->
      forall mc, MetricSemantics.exec e c t m l mc (fun t' m' l' _ => post t' m' l').
  Proof.
    induction 1; intros;
      repeat match reverse goal with
        | H: Semantics.eval_expr _ _ _ = Some _ |- _ =>
            eapply metric_to_plain_eval_expr in H; destruct H as (? & H)
        | H: Semantics.eval_call_args _ _ _ = Some _ |- _ =>
            eapply metric_to_plain_eval_call_args in H; destruct H as (? & H)
        end;
      try solve [econstructor; eauto].
  Qed.
  
  Lemma metric_to_plain_call: forall f t m args post,
      Semantics.call e f t m args post ->
      forall mc, MetricSemantics.call e f t m args mc (fun t' m' rets _ => post t' m' rets).
  Proof.
    unfold MetricSemantics.call, Semantics.call. intros. fwd. eauto 10 using metric_to_plain_exec.
  Qed.
End MetricToSomething.

Section PlainToSomething.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: Semantics.ExtSpec}.

  Lemma plain_to_metric_eval_expr: forall (m : mem) l e mc v mc',
      MetricSemantics.eval_expr m l e mc = Some (v, mc') ->
      Semantics.eval_expr m l e = Some v.
  Proof.
    induction e; cbn; intros;
      repeat match goal with
        | H: Some _ = Some _ |- _ => eapply Option.eq_of_eq_Some in H; subst
        | IH: forall _, Some _ = Some _ -> _ |- _ => specialize IH with (1 := eq_refl)
        | IH: forall _ _ _, MetricSemantics.eval_expr _ _ _ _ = Some _ -> _ |- _ =>
            specialize (IH _ _ _ ltac:(eassumption))
        | |- _ => progress fwd
        | |- _ => Tactics.destruct_one_match
        end;
      eauto.
  Qed.

  Lemma plain_to_metric_eval_call_args: forall (m : mem) l arges mc args mc',
      MetricSemantics.eval_call_args m l arges mc = Some (args, mc') ->
      Semantics.eval_call_args m l arges = Some args.
  Proof.
    induction arges; cbn; intros.
    - eapply Option.eq_of_eq_Some in H. inversion H. subst. eauto.
    - fwd.
      eapply plain_to_metric_eval_expr in E. rewrite E.
      apply IHarges in E0. rewrite E0. reflexivity.
  Qed.

  Context (e: env).

  Lemma plain_to_metric_exec: forall c t (m : mem) l mc post,
      MetricSemantics.exec e c t m l mc post ->
      Semantics.exec e c t m l (fun t' m' l' => exists mc', post t' m' l' mc').
  Proof.
    induction 1; intros;
      repeat match reverse goal with
        | H: MetricSemantics.eval_expr _ _ _ _ = Some _ |- _ =>
            eapply plain_to_metric_eval_expr in H
        | H: MetricSemantics.eval_call_args _ _ _ _ = Some _ |- _ =>
            eapply plain_to_metric_eval_call_args in H
        end;
      try solve [econstructor; eauto].
    all: try solve [econstructor; eauto; simpl; intros; fwd; eauto].
    - econstructor; eauto. intros. eapply Semantics.exec.weaken.
      1: eapply H1; solve[eauto]. simpl. intros. fwd. eexists. eexists. eauto.
    - econstructor; eauto. simpl. intros. fwd. apply H3 in H4. fwd. eauto 10.
    - econstructor; eauto. simpl. intros. apply H2 in H3. fwd. eauto.
  Qed.

  Lemma plain_to_metric_call: forall f t m args mc post,
      MetricSemantics.call e f t m args mc post ->
      Semantics.call e f t m args (fun t' m' rets => exists mc', post t' m' rets mc').
  Proof.
    unfold MetricSemantics.call, Semantics.call. intros. fwd.
    do 3 eexists. intuition eauto. eexists. intuition eauto.
    eapply Semantics.exec.weaken.
    - eauto 10 using plain_to_metric_exec.
    - simpl. intros. fwd. eauto.
  Qed.
End PlainToSomething.

(* The reverse direction of [LeakageToSomething]: a proof about the leakage
   semantics gives a proof about the plain semantics whose postcondition
   forgets the leakage trace.

   This is only possible for code that does not use [cmd.stackalloc]:
   the leakage semantics runs the body of a stackalloc for the single address
   chosen by the [pick_sp] oracle, whereas the plain semantics requires the body
   to run for every address. So the lemmas take a syntactic side condition
   [stackalloc_free_wrt S c]: the command has no stackalloc and only calls
   functions in [S], and [stackalloc_free_env_wrt S e] says that every function
   in [S] has such a body. Plain callers whose environment is concrete (linking
   lemmas) discharge the side condition by computation, see
   [stackalloc_free_env_wrt_of_list]. See ProgramLogic.straightline_call_from_leakage
   for the tactic side. *)
Section StackallocFree.
  Fixpoint stackalloc_free_wrt (S : String.string -> bool) (c : cmd) : bool :=
    match c with
    | cmd.stackalloc _ _ _ => false
    | cmd.seq c1 c2 | cmd.cond _ c1 c2 => stackalloc_free_wrt S c1 && stackalloc_free_wrt S c2
    | cmd.while _ c => stackalloc_free_wrt S c
    | cmd.call _ f _ => S f
    | _ => true
    end.

  Definition stackalloc_free_env_wrt (S : String.string -> bool) (e : env) : Prop :=
    forall f args rets body, S f = true -> map.get e f = Some (args, rets, body) ->
                             stackalloc_free_wrt S body = true.

  Definition stackalloc_free_env : env -> Prop := stackalloc_free_env_wrt (fun _ => true).

  Lemma stackalloc_free_env_wrt_of_list: forall S (l : list (String.string * Syntax.func)),
      List.forallb (fun '(f, (_, _, body)) => negb (S f) || stackalloc_free_wrt S body)%bool l = true ->
      stackalloc_free_env_wrt S (map.of_list l).
  Proof.
    unfold stackalloc_free_env_wrt. induction l as [|[f [ [args rets] body] ] l IH];
      intros H f' args' rets' body' HS HG.
    - change (map.of_list nil) with (@map.empty _ _ env) in HG.
      rewrite map.get_empty in HG. discriminate.
    - change (map.of_list ((f, (args, rets, body)) :: l))
        with (@map.put _ _ env (map.of_list l) f (args, rets, body)) in HG.
      cbn [List.forallb] in H.
      eapply Bool.andb_true_iff in H. destruct H as [H1 H2]. specialize (IH H2).
      destruct (String.eqb_spec f f') as [<-|Hne].
      + rewrite map.get_put_same in HG. eapply Option.eq_of_eq_Some in HG. inversion HG; subst.
        rewrite HS, Bool.orb_false_l in H1. exact H1.
      + rewrite map.get_put_diff in HG by congruence. eauto.
  Qed.

  Lemma stackalloc_free_env_of_list: forall (l : list (String.string * Syntax.func)),
      List.forallb (fun '(_, (_, _, body)) => stackalloc_free_wrt (fun _ => true) body) l = true ->
      stackalloc_free_env (map.of_list l).
  Proof.
    intros l H. eapply stackalloc_free_env_wrt_of_list. cbn [negb orb]. exact H.
  Qed.
End StackallocFree.

Section PlainOfLeakage.
  Context {width: Z} {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec} {pick_sp: PickSp}.
  Context {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma plain_of_leakage_eval_expr: forall (m : mem) l e k v k',
      LeakageSemantics.eval_expr m l e k = Some (v, k') ->
      Semantics.eval_expr m l e = Some v.
  Proof.
    induction e; cbn; intros;
      repeat match goal with
        | H: Some _ = Some _ |- _ => eapply Option.eq_of_eq_Some in H; subst
        | IH: forall _, Some _ = Some _ -> _ |- _ => specialize IH with (1 := eq_refl)
        | IH: forall _ _ _, LeakageSemantics.eval_expr _ _ _ _ = Some _ -> _ |- _ =>
            specialize (IH _ _ _ ltac:(eassumption))
        | |- _ => progress fwd
        | |- _ => Tactics.destruct_one_match
        end;
      eauto.
  Qed.

  Lemma plain_of_leakage_eval_call_args: forall (m : mem) l arges k args k',
      LeakageSemantics.eval_call_args m l arges k = Some (args, k') ->
      Semantics.eval_call_args m l arges = Some args.
  Proof.
    induction arges; cbn; intros.
    - eapply Option.eq_of_eq_Some in H. inversion H. subst. eauto.
    - fwd.
      eapply plain_of_leakage_eval_expr in E. rewrite E.
      apply IHarges in E0. rewrite E0. reflexivity.
  Qed.

  Context (e: env).
  Existing Instance deleakaged_ext_spec.

  Lemma plain_of_leakage_exec: forall S, stackalloc_free_env_wrt S e ->
      forall c k t (m : mem) l post,
      stackalloc_free_wrt S c = true ->
      LeakageSemantics.exec e c k t m l post ->
      Semantics.exec e c t m l (fun t' m' l' => exists k', post k' t' m' l').
  Proof.
    intros S HS c k t m l post Hc Hex. revert Hc. induction Hex; intros; cbn [stackalloc_free_wrt] in *;
      repeat match reverse goal with
        | H: LeakageSemantics.eval_expr _ _ _ _ = Some _ |- _ =>
            eapply plain_of_leakage_eval_expr in H
        | H: LeakageSemantics.eval_call_args _ _ _ _ = Some _ |- _ =>
            eapply plain_of_leakage_eval_call_args in H
        | H: (_ && _)%bool = true |- _ => eapply Bool.andb_true_iff in H; destruct H
        end;
      try solve [econstructor; eauto].
    all: try solve [econstructor; eauto; simpl; intros; fwd; eauto].
    all: lazymatch goal with
      | |- Semantics.exec _ (cmd.stackalloc _ _ _) _ _ _ _ => discriminate
      | |- Semantics.exec _ (cmd.while _ _) _ _ _ _ =>
          eapply Semantics.exec.while_true; [eassumption|eassumption| |];
          [ eapply IHHex; assumption
          | simpl; intros; fwd; eauto ]
      | |- Semantics.exec _ (cmd.call _ _ _) _ _ _ _ =>
          eapply Semantics.exec.call; [eassumption|eassumption|eassumption| |];
          [ eapply IHHex; eapply HS; eassumption
          | simpl; intros; fwd;
            match goal with
            | HC: forall _ _ _ _, ?mid _ _ _ _ -> _, HM: ?mid _ _ _ _ |- _ => apply HC in HM
            end; fwd; eauto 10 ]
      | |- Semantics.exec _ (cmd.interact _ _ _) _ _ _ _ =>
          eapply Semantics.exec.interact with
            (mid := fun mReceive resvals => exists klist, mid mReceive resvals klist);
          [eassumption|eassumption| |];
          [ cbv [deleakaged_ext_spec]; eapply ext_spec.weaken; [|eassumption];
            cbv [Morphisms.pointwise_relation Basics.impl]; eauto
          | simpl; intros; fwd;
            match goal with
            | HC: forall _ _ _, ?mid _ _ _ -> _, HM: ?mid _ _ _ |- _ => apply HC in HM
            end; fwd; eauto ]
      end.
  Qed.

  Lemma plain_of_leakage_call: forall S, stackalloc_free_env_wrt S e ->
      forall f, S f = true ->
      forall k t m args post,
      LeakageSemantics.call e f k t m args post ->
      Semantics.call e f t m args (fun t' m' rets => exists k', post k' t' m' rets).
  Proof.
    unfold LeakageSemantics.call, Semantics.call. intros. fwd.
    do 3 eexists. intuition eauto. eexists. intuition eauto.
    eapply Semantics.exec.weaken.
    - eapply plain_of_leakage_exec; eauto.
    - simpl. intros. fwd. eauto.
  Qed.

  Lemma plain_of_leakage_call_env: stackalloc_free_env e ->
      forall f k t m args post,
      LeakageSemantics.call e f k t m args post ->
      Semantics.call e f t m args (fun t' m' rets => exists k', post k' t' m' rets).
  Proof. intros. eapply plain_of_leakage_call; eauto. Qed.
End PlainOfLeakage.
