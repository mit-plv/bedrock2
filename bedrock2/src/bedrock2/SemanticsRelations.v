Require Import coqutil.sanity coqutil.Byte.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Z.Lia.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Export bedrock2.Memory.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.Semantics.
Require Import bedrock2.LeakageSemantics.
Require Import bedrock2.MetricSemantics.
Require Import bedrock2.MetricLeakageSemantics.

Section MetricLeakageToSomething.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
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

  (* Lemma metricleakage_to_plain_exec: forall c q aep t m l post, *)
  (*     Semantics.exec e c t m l post -> *)
  (*     forall k mc, MetricLeakageSemantics.exec e c q aep k t m l mc (fun q' _ _ t' m' l' _ => *)
  (*                                                                 q' = true /\ post t' m' l'). *)
  (* Proof. *)
  (*   induction 1; intros; *)
  (*     repeat match reverse goal with *)
  (*       | H: Semantics.eval_expr _ _ _ = Some _ |- _ => *)
  (*           eapply metricleakage_to_plain_eval_expr in H; destruct H as (? & ? & H) *)
  (*       | H: Semantics.eval_call_args _ _ _ = Some _ |- _ => *)
  (*           eapply metricleakage_to_plain_eval_call_args in H; destruct H as (? & ? & H) *)
  (*       end; *)
  (*     solve [econstructor; eauto]. *)
  (* Qed. *)

  (* Lemma metricleakage_to_metric_exec: forall c t m l mc post, *)
  (*     MetricSemantics.exec e c t m l mc post -> *)
  (*     forall k, MetricLeakageSemantics.exec e c k t m l mc (fun _ t' m' l' mc' => post t' m' l' mc'). *)
  (* Proof. *)
  (*   induction 1; intros; *)
  (*     repeat match reverse goal with *)
  (*       | H: MetricSemantics.eval_expr _ _ _ _ = Some _ |- _ => *)
  (*           eapply metricleakage_to_metric_eval_expr in H; destruct H as (? & H) *)
  (*       | H: MetricSemantics.eval_call_args _ _ _ _ = Some _ |- _ => *)
  (*           eapply metricleakage_to_metric_eval_call_args in H; destruct H as (? & H) *)
  (*       end; *)
  (*     try solve [econstructor; eauto]. *)
  (* Qed. *)

  (* Lemma metricleakage_to_leakage_exec: forall c t m l k post, *)
  (*     LeakageSemantics.exec e c k t m l post -> *)
  (*     forall mc, MetricLeakageSemantics.exec e c k t m l mc (fun k' t' m' l' _ => post k' t' m' l'). *)
  (* Proof. *)
  (*   induction 1; intros; *)
  (*     repeat match reverse goal with *)
  (*       | H: LeakageSemantics.eval_expr _ _ _ _ = Some _ |- _ => *)
  (*           eapply metricleakage_to_leakage_eval_expr in H; destruct H as (? & H) *)
  (*       | H: LeakageSemantics.eval_call_args _ _ _ _ = Some _ |- _ => *)
  (*           eapply metricleakage_to_leakage_eval_call_args in H; destruct H as (? & H) *)
  (*       end; *)
  (*     try solve [econstructor; eauto]. *)
  (* Qed. *)

  (* Lemma metricleakage_to_plain_call: forall f t m args post, *)
  (*     Semantics.call e f t m args post -> *)
  (*     forall k mc, MetricLeakageSemantics.call e f k t m args mc (fun _ t' m' rets _ => post t' m' rets). *)
  (* Proof. *)
  (*   unfold MetricLeakageSemantics.call, Semantics.call. intros. fwd. eauto 10 using metricleakage_to_plain_exec. *)
  (* Qed. *)

  (* Lemma metricleakage_to_metric_call: forall f t m args mc post, *)
  (*     MetricSemantics.call e f t m args mc post -> *)
  (*     forall k, MetricLeakageSemantics.call e f k t m args mc (fun _ t' m' rets mc' => post t' m' rets mc'). *)
  (* Proof. *)
  (*   unfold MetricLeakageSemantics.call, MetricSemantics.call. intros. fwd. eauto 10 using metricleakage_to_metric_exec. *)
  (* Qed. *)

  (* Lemma metricleakage_to_leakage_call: forall f k t m args post, *)
  (*     LeakageSemantics.call e f k t m args post -> *)
  (*     forall mc, MetricLeakageSemantics.call e f k t m args mc (fun k' t' m' rets _ => post k' t' m' rets). *)
  (* Proof. *)
  (*   unfold MetricLeakageSemantics.call, LeakageSemantics.call. intros. fwd. eauto 10 using metricleakage_to_leakage_exec. *)
  (* Qed. *)
End MetricLeakageToSomething.

Section LeakageToSomething.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
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

  (* Lemma leakage_to_metricleakage_exec: forall c t m l k mc post, *)
  (*     MetricLeakageSemantics.exec e c k t m l mc post -> *)
  (*     LeakageSemantics.exec e c k t m l (fun k' t' m' l' => exists mc', post k' t' m' l' mc'). *)
  (* Proof. *)
  (*   induction 1; intros; *)
  (*     repeat match reverse goal with *)
  (*       | H: MetricLeakageSemantics.eval_expr _ _ _ _ _ = Some _ |- _ => *)
  (*           eapply leakage_to_metricleakage_eval_expr in H *)
  (*       | H: MetricLeakageSemantics.eval_call_args _ _ _ _ _ = Some _ |- _ => *)
  (*           eapply leakage_to_metricleakage_eval_call_args in H *)
  (*       end; *)
  (*     try solve [econstructor; eauto]. *)
  (*   all: try solve [econstructor; eauto; simpl; intros; fwd; eauto]. *)
  (*   - econstructor; eauto. intros. eapply LeakageSemantics.exec.weaken. *)
  (*     1: eapply H1; solve[eauto]. simpl. intros. fwd. eexists. eexists. eauto. *)
  (*   - econstructor; eauto. simpl. intros. fwd. apply H3 in H4. fwd. eauto 10. *)
  (*   - econstructor; eauto. simpl. intros. apply H2 in H3. fwd. eauto. *)
  (* Qed. *)

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

  (* Lemma leakage_to_metricleakage_call: forall f k t m args mc post, *)
  (*     MetricLeakageSemantics.call e f k t m args mc post -> *)
  (*     LeakageSemantics.call e f k t m args (fun k' t' m' rets => exists mc', post k' t' m' rets mc'). *)
  (* Proof. *)
  (*   unfold LeakageSemantics.call, MetricLeakageSemantics.call. intros. fwd. *)
  (*   do 3 eexists. intuition eauto. eexists. intuition eauto. *)
  (*   eapply LeakageSemantics.exec.weaken. *)
  (*   - eauto 10 using leakage_to_metricleakage_exec. *)
  (*   - simpl. intros. fwd. eauto. *)
  (* Qed. *)
End LeakageToSomething.

Section MetricToSomething.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
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
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
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
