Require Import coqutil.sanity coqutil.Byte.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Properties.
Require coqutil.Map.SortedListString.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Export bedrock2.Memory.
Require Import Coq.Lists.List.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.MetricCosts.
Require Import bedrock2.MetricSemantics.
Require Import bedrock2.Semantics.
Require Import bedrock2.LeakageSemantics.
Require Import Coq.Lists.List.

Local Notation UNK := String.EmptyString.

Section semantics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.

  Local Notation metrics := MetricLog.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).

    Local Notation "' x <- a ; f" := (match a with Some x => f | None => None end)
      (right associativity, at level 70, x pattern).

    (* TODO XXX possibly be a bit smarter about whether things are registers,
       for tighter metrics bounds at bedrock2 level *)
    Fixpoint eval_expr (e : expr) (k : leakage) (mc : metrics) : option (word * leakage * metrics) :=
      match e with
      | expr.literal v => Some (word.of_Z v, k, cost_lit isRegStr UNK mc)
      | expr.var x => 'v <- map.get l x; Some (v, k, cost_set isRegStr UNK x mc)
      | expr.inlinetable aSize t index =>
          '(index', k', mc') <- eval_expr index k mc;
          'v <- load aSize (map.of_list_word t) index';
          Some (v, leak_word index' :: k', cost_inlinetable isRegStr UNK UNK mc')
      | expr.load aSize a =>
          '(a', k', mc') <- eval_expr a k mc;
          'v <- load aSize m a';
          Some (v, leak_word a' :: k', cost_load isRegStr UNK UNK mc')
      | expr.op op e1 e2 =>
          '(v1, k', mc') <- eval_expr e1 k mc;
          '(v2, k'', mc'') <- eval_expr e2 k' mc';
          Some (interp_binop op v1 v2, leak_binop op v1 v2 ++ k'', cost_op isRegStr UNK UNK UNK mc'')
      | expr.ite c e1 e2 =>
          '(vc, k', mc') <- eval_expr c k mc;
          let b := word.eqb vc (word.of_Z 0) in
          eval_expr (if b then e2 else e1) (leak_bool b :: k')
                    (cost_if isRegStr UNK (Some UNK) mc')
      end.

    Fixpoint eval_call_args (arges : list expr) (k : leakage) (mc : metrics) :=
      match arges with
      | e :: tl =>
        '(v, k', mc') <- eval_expr e k mc;
        '(args, k'', mc'') <- eval_call_args tl k' mc';
        Some (v :: args, k'', mc'')
      | _ => Some (nil, k, mc)
      end.

  End WithMemAndLocals.
End semantics.

Module exec. Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec} {pick_sp: PickSp}.
  Section WithEnv.
  Context (e: env).

  Local Notation metrics := MetricLog.

  Implicit Types post : leakage -> trace -> mem -> locals -> metrics -> Prop. (* COQBUG: unification finds Type instead of Prop and fails to downgrade *)
  Inductive exec :
    cmd -> leakage -> trace -> mem -> locals -> metrics ->
    (leakage -> trace -> mem -> locals -> metrics -> Prop) -> Prop :=
  | skip
    k t m l mc post
    (_ : post k t m l mc)
    : exec cmd.skip k t m l mc post
  | set x e
    k t m l mc post
    v k' mc' (_ : eval_expr m l e k mc = Some (v, k', mc'))
    (_ : post k' t m (map.put l x v) (cost_set isRegStr x UNK mc'))
    : exec (cmd.set x e) k t m l mc post
  | unset x
    k t m l mc post
    (_ : post k t m (map.remove l x) mc)
    : exec (cmd.unset x) k t m l mc post
  | store sz ea ev
    k t m l mc post
    a k' mc' (_ : eval_expr m l ea k mc = Some (a, k', mc'))
    v k'' mc'' (_ : eval_expr m l ev k' mc' = Some (v, k'', mc''))
    m' (_ : store sz m a v = Some m')
    (_ : post (leak_word a :: k'') t m' l (cost_store isRegStr UNK UNK mc''))
    : exec (cmd.store sz ea ev) k t m l mc post
  | stackalloc x n body
    k t mSmall l mc post
    (_ : Z.modulo n (bytes_per_word width) = 0)
    (_ : forall mStack mCombined,
        let a := pick_sp k in
        anybytes a n mStack ->
        map.split mCombined mSmall mStack ->
        exec body (leak_unit :: k) t mCombined (map.put l x a) (cost_stackalloc isRegStr x mc)
          (fun k' t' mCombined' l' mc' =>
            exists mSmall' mStack',
              anybytes a n mStack' /\
              map.split mCombined' mSmall' mStack' /\
              post k' t' mSmall' l' mc'))
     : exec (cmd.stackalloc x n body) k t mSmall l mc post
  | if_true k t m l mc e c1 c2 post
    v k' mc' (_ : eval_expr m l e k mc = Some (v, k', mc'))
    (_ : word.unsigned v <> 0)
    (_ : exec c1 (leak_bool true :: k') t m l (cost_if isRegStr UNK (Some UNK) mc') post)
    : exec (cmd.cond e c1 c2) k t m l mc post
  | if_false e c1 c2
    k t m l mc post
    v k' mc' (_ : eval_expr m l e k mc = Some (v, k', mc'))
    (_ : word.unsigned v = 0)
    (_ : exec c2 (leak_bool false :: k') t m l (cost_if isRegStr UNK (Some UNK) mc') post)
    : exec (cmd.cond e c1 c2) k t m l mc post
  | seq c1 c2
    k t m l mc post
    mid (_ : exec c1 k t m l mc mid)
    (_ : forall k' t' m' l' mc', mid k' t' m' l' mc' -> exec c2 k' t' m' l' mc' post)
    : exec (cmd.seq c1 c2) k t m l mc post
  | while_false e c
    k t m l mc post
    v k' mc' (_ : eval_expr m l e k mc = Some (v, k', mc'))
    (_ : word.unsigned v = 0)
    (_ : post (leak_bool false :: k') t m l (cost_loop_false isRegStr UNK (Some UNK) mc'))
    : exec (cmd.while e c) k t m l mc post
  | while_true e c
      k t m l mc post
      v k' mc' (_ : eval_expr m l e k mc = Some (v, k', mc'))
      (_ : word.unsigned v <> 0)
      mid (_ : exec c (leak_bool true :: k') t m l mc' mid)
      (_ : forall k'' t' m' l' mc'', mid k'' t' m' l' mc'' ->
                                 exec (cmd.while e c) k'' t' m' l' (cost_loop_true isRegStr UNK (Some UNK) mc'') post)
    : exec (cmd.while e c) k t m l mc post
  | call binds fname arges
      k t m l mc post
      params rets fbody (_ : map.get e fname = Some (params, rets, fbody))
      args k' mc' (_ : eval_call_args m l arges k mc = Some (args, k', mc'))
      lf (_ : map.of_list_zip params args = Some lf)
      mid (_ : exec fbody (leak_unit :: k') t m lf mc' mid)
      (_ : forall k'' t' m' st1 mc'', mid k'' t' m' st1 mc'' ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post k'' t' m' l'  (cost_call PreSpill mc''))
    : exec (cmd.call binds fname arges) k t m l mc post
  | interact binds action arges
      k t m l mc post
      mKeep mGive (_: map.split m mKeep mGive)
      args k' mc' (_ :  eval_call_args m l arges k mc = Some (args, k', mc'))
      mid (_ : ext_spec t mGive action args mid)
      (_ : forall mReceive resvals klist, mid mReceive resvals klist ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (leak_list klist :: k') (cons ((mGive, action, args), (mReceive, resvals)) t) m' l'
            (cost_interact PreSpill mc'))
    : exec (cmd.interact binds action arges) k t m l mc post
  .

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma weaken: forall k t l m mc s post1,
      exec s k t m l mc post1 ->
      forall post2: _ -> _ -> _ -> _ -> _ -> Prop,
        (forall k' t' m' l' mc', post1 k' t' m' l' mc' -> post2 k' t' m' l' mc') ->
        exec s k t m l mc post2.
  Proof.
    induction 1; intros; try solve [econstructor; eauto].
    - eapply stackalloc. 1: assumption.
      intros.
      eapply H1; eauto.
      intros. fwd. eauto 10.
    - eapply call.
      4: eapply IHexec.
      all: eauto.
      intros.
      edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
      eauto 10.
    - eapply interact; try eassumption.
      intros.
      edestruct H2 as (? & ? & ?); [eassumption|].
      eauto 10.
  Qed.

  Lemma intersect: forall k t l m mc s post1,
      exec s k t m l mc post1 ->
      forall post2,
        exec s k t m l mc post2 ->
        exec s k t m l mc (fun k' t' m' l' mc' => post1 k' t' m' l' mc' /\ post2 k' t' m' l' mc').
  Proof.
    induction 1;
      intros;
      match goal with
      | H: exec _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H
      end;
      repeat match goal with
      | H1: ?e = Some (?x1, ?y1, ?z1), H2: ?e = Some (?x2, ?y2, ?z2) |- _ =>
        replace x2 with x1 in * by congruence;
          replace y2 with y1 in * by congruence;
          replace z2 with z1 in * by congruence;
          clear x2 y2 z2 H2
      end;
      repeat match goal with
             | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
               replace v2 with v1 in * by congruence; clear H2
             end;
      try solve [econstructor; eauto | exfalso; congruence].

    - econstructor. 1: eassumption.
      intros.
      rename H0 into Ex1, H13 into Ex2.
      eapply weaken. 1: eapply H1. 1,2: eassumption.
      1: eapply Ex2. 1,2: eassumption.
      cbv beta.
      intros. fwd.
      lazymatch goal with
      | A: map.split _ _ _, B: map.split _ _ _ |- _ =>
        specialize @map.split_diff with (4 := A) (5 := B) as P
      end.
      edestruct P; try typeclasses eauto. 2: subst; eauto 10.
      eapply anybytes_unique_domain; eassumption.
    - econstructor.
      + eapply IHexec. exact H5. (* not H *)
      + simpl. intros *. intros [? ?]. eauto.
    - eapply while_true. 1, 2: eassumption.
      + eapply IHexec. exact H9. (* not H1 *)
      + simpl. intros *. intros [? ?]. eauto.
    - eapply call. 1, 2, 3: eassumption.
      + eapply IHexec. exact H17. (* not H2 *)
      + simpl. intros *. intros [? ?].
        edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
        edestruct H18 as (? & ? & ? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
    - pose proof ext_spec.mGive_unique as P.
      specialize P with (1 := H) (2 := H7) (3 := H1) (4 := H15).
      subst mGive0.
      destruct (map.split_diff (map.same_domain_refl mGive) H H7) as (? & _).
      subst mKeep0.
      eapply interact. 1,2: eassumption.
      + eapply ext_spec.intersect; [ exact H1 | exact H15 ].
      + simpl. intros *. intros [? ?].
        edestruct H2 as (? & ? & ?); [eassumption|].
        edestruct H16 as (? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
  Qed.

  End WithEnv.

  Lemma extend_env: forall e1 e2,
      map.extends e2 e1 ->
      forall c k t m l mc post,
      exec e1 c k t m l mc post ->
      exec e2 c k t m l mc post.
  Proof. induction 2; try solve [econstructor; eauto]. Qed.

  End WithParams.
End exec. Notation exec := exec.exec.

Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec} {pick_sp: PickSp}.

  Implicit Types (l: locals) (m: mem).

  Definition call e fname k t m args mc post :=
    exists argnames retnames body,
      map.get e fname = Some (argnames, retnames, body) /\
      exists l, map.of_list_zip argnames args = Some l /\
        exec e body k t m l mc (fun k' t' m' l' mc' => exists rets,
          map.getmany_of_list l' retnames = Some rets /\ post k' t' m' rets mc').

  Lemma weaken_call: forall e fname k t m args mc post1,
      call e fname k t m args mc post1 ->
      forall (post2: leakage -> trace -> mem -> list word -> MetricLog -> Prop),
      (forall k' t' m' rets mc', post1 k' t' m' rets mc' -> post2 k' t' m' rets mc') ->
      call e fname k t m args mc post2.
  Proof.
    unfold call. intros. fwd.
    do 4 eexists. 1: eassumption.
    do 2 eexists. 1: eassumption.
    eapply exec.weaken. 1: eassumption.
    cbv beta. clear -H0. intros. fwd. eauto.
  Qed.

  Lemma extend_env_call: forall e1 e2,
      map.extends e2 e1 ->
      forall f k t m rets mc post,
      call e1 f k t m rets mc post ->
      call e2 f k t m rets mc post.
  Proof.
    unfold call. intros. fwd. repeat eexists.
    - eapply H. eassumption.
    - eassumption.
    - eapply exec.extend_env; eassumption.
  Qed.

  Lemma to_plain_eval_expr: forall m l e v,
      Semantics.eval_expr m l e = Some v ->
      forall k mc, exists k' mc', eval_expr m l e k mc = Some (v, k', mc').
  Proof.
    induction e; cbn; intros;
      repeat match goal with
        | H: Some _ = Some _ |- _ => eapply Option.eq_of_eq_Some in H; subst
        | IH: forall _, Some _ = Some _ -> _ |- _ => specialize IH with (1 := eq_refl)
        | IH: forall _ _, Semantics.eval_expr _ _ _ = Some _ -> _ |- _ =>
            specialize (IH _ _ ltac:(eassumption))
        | IH: forall _: leakage, forall _: MetricLog, exists _: leakage, exists _: MetricLog,
            eval_expr ?m ?l ?e _ _ = Some _
          |- context[eval_expr ?m ?l ?e ?k ?mc] => specialize (IH k mc)
        | |- _ => progress fwd
        | |- _ => Tactics.destruct_one_match
        end;
      eauto.
  Qed.

  Lemma to_metric_eval_expr: forall m l e mc v mc',
      MetricSemantics.eval_expr m l e mc = Some (v, mc') ->
      forall k, exists k', eval_expr m l e k mc = Some (v, k', mc').
  Proof.
    induction e; cbn; intros;
      repeat match goal with
        | H: Some _ = Some _ |- _ => eapply Option.eq_of_eq_Some in H; subst
        | IH: forall _, Some _ = Some _ -> _ |- _ => specialize IH with (1 := eq_refl)
        | IH: forall _ _ _, MetricSemantics.eval_expr _ _ _ _ = Some _ -> _ |- _
          => specialize (IH _ _ _ ltac:(eassumption))
        | IH: forall _: leakage, exists _: leakage, eval_expr ?m ?l ?e _ _ = Some _
          |- context[eval_expr ?m ?l ?e ?k ?mc] => specialize (IH k)
        | |- _ => progress fwd
        | |- _ => Tactics.destruct_one_match
        end;
      eauto.
  Qed.

  Lemma to_leakage_eval_expr: forall m l e k v k',
      LeakageSemantics.eval_expr m l e k = Some (v, k') ->
      forall mc, exists mc', eval_expr m l e k mc = Some (v, k', mc').
  Proof.
    induction e; cbn; intros;
      repeat match goal with
        | H: Some _ = Some _ |- _ => eapply Option.eq_of_eq_Some in H; subst
        | IH: forall _, Some _ = Some _ -> _ |- _ => specialize IH with (1 := eq_refl)
        | IH: forall _ _ _, LeakageSemantics.eval_expr _ _ _ _ = Some _ -> _ |- _
          => specialize (IH _ _ _ ltac:(eassumption))
        | IH: forall _: MetricLog, exists _: MetricLog, eval_expr ?m ?l ?e _ _ = Some _
          |- context[eval_expr ?m ?l ?e ?k ?mc] => specialize (IH mc)
        | |- _ => progress fwd
        | |- _ => Tactics.destruct_one_match
        end;
      eauto.
  Qed.

  Lemma to_plain_eval_call_args: forall m l arges args,
      Semantics.eval_call_args m l arges = Some args ->
      forall k mc, exists k' mc', eval_call_args m l arges k mc = Some (args, k', mc').
  Proof.
    induction arges; cbn; intros.
    - eapply Option.eq_of_eq_Some in H. subst. eauto.
    - fwd.
      eapply to_plain_eval_expr in E. destruct E as (k' & mc' & E). rewrite E.
      specialize IHarges with (1 := eq_refl). specialize (IHarges k' mc').
      destruct IHarges as (k'' & mc'' & IH). rewrite IH. eauto.
  Qed.

  Lemma to_metric_eval_call_args: forall m l arges mc args mc',
      MetricSemantics.eval_call_args m l arges mc = Some (args, mc') ->
      forall k, exists k', eval_call_args m l arges k mc = Some (args, k', mc').
  Proof.
    induction arges; cbn; intros.
    - inversion H. subst. eauto.
    - fwd.
      eapply to_metric_eval_expr in E. destruct E as (k' & E). rewrite E.
      specialize (IHarges _ _ _ ltac:(eassumption) k').
      destruct IHarges as (k'' & IH). rewrite IH. eauto.
  Qed.

  Lemma to_leakage_eval_call_args: forall m l arges k args k',
      LeakageSemantics.eval_call_args m l arges k = Some (args, k') ->
      forall mc, exists mc', eval_call_args m l arges k mc = Some (args, k', mc').
  Proof.
    induction arges; cbn; intros.
    - inversion H. subst. eauto.
    - fwd.
      eapply to_leakage_eval_expr in E. destruct E as (mc' & E). rewrite E.
      specialize (IHarges _ _ _ ltac:(eassumption) mc').
      destruct IHarges as (mc'' & IH). rewrite IH. eauto.
  Qed.

  Context (e: env).
  Context (sem_ext_spec : Semantics.ExtSpec := fun t mGive a args post => ext_spec t mGive a args (fun mReceive resvals klist => post mReceive resvals)).
  Existing Instance sem_ext_spec.

  Lemma to_plain_exec: forall c t m l post,
      Semantics.exec e c t m l post ->
      forall k mc, exec e c k t m l mc (fun _ t' m' l' _ => post t' m' l').
  Proof.
    induction 1; intros;
      repeat match reverse goal with
        | H: Semantics.eval_expr _ _ _ = Some _ |- _ =>
            eapply to_plain_eval_expr in H; destruct H as (? & ? & H)
        | H: Semantics.eval_call_args _ _ _ = Some _ |- _ =>
            eapply to_plain_eval_call_args in H; destruct H as (? & ? & H)
        end;
      try solve [econstructor; eauto].
  Qed.

  Lemma to_metric_exec: forall c t m l mc post,
      MetricSemantics.exec e c t m l mc post ->
      forall k, exec e c k t m l mc (fun _ t' m' l' mc' => post t' m' l' mc').
  Proof.
    induction 1; intros;
      repeat match reverse goal with
        | H: MetricSemantics.eval_expr _ _ _ _ = Some _ |- _ =>
            eapply to_metric_eval_expr in H; destruct H as (? & H)
        | H: MetricSemantics.eval_call_args _ _ _ _ = Some _ |- _ =>
            eapply to_metric_eval_call_args in H; destruct H as (? & H)
        end;
      try solve [econstructor; eauto].
  Qed.

  Lemma to_leakage_exec: forall c t m l k post,
      LeakageSemantics.exec e c k t m l post ->
      forall mc, exec e c k t m l mc (fun k' t' m' l' _ => post k' t' m' l').
  Proof.
    induction 1; intros;
      repeat match reverse goal with
        | H: LeakageSemantics.eval_expr _ _ _ _ = Some _ |- _ =>
            eapply to_leakage_eval_expr in H; destruct H as (? & H)
        | H: LeakageSemantics.eval_call_args _ _ _ _ = Some _ |- _ =>
            eapply to_leakage_eval_call_args in H; destruct H as (? & H)
        end;
      try solve [econstructor; eauto].
  Qed.

  Lemma to_plain_call: forall f t m args post,
      Semantics.call e f t m args post ->
      forall k mc, call e f k t m args mc (fun _ t' m' rets _ => post t' m' rets).
  Proof.
    unfold call, Semantics.call. intros. fwd. eauto 10 using to_plain_exec.
  Qed.

  Lemma to_metric_call: forall f t m args mc post,
      MetricSemantics.call e f t m args mc post ->
      forall k, call e f k t m args mc (fun _ t' m' rets mc' => post t' m' rets mc').
  Proof.
    unfold call, MetricSemantics.call. intros. fwd. eauto 10 using to_metric_exec.
  Qed.

  Lemma to_leakage_call: forall f k t m args post,
      LeakageSemantics.call e f k t m args post ->
      forall mc, call e f k t m args mc (fun k' t' m' rets _ => post k' t' m' rets).
  Proof.
    unfold call, LeakageSemantics.call. intros. fwd. eauto 10 using to_leakage_exec.
  Qed.
End WithParams.
