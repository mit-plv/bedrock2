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
Require Import bedrock2.Semantics.
Require Import Coq.Lists.List.

Local Notation UNK := String.EmptyString.

Section semantics.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.

  Local Notation metrics := MetricLog.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).

    Local Notation "' x <- a | y ; f" := (match a with x => f | _ => y end)
      (right associativity, at level 70, x pattern).

    (* TODO XXX possibly be a bit smarter about whether things are registers,
       for tighter metrics bounds at bedrock2 level *)
    Fixpoint eval_expr (e : expr) (mc : metrics) : option (word * metrics) :=
      match e with
      | expr.literal v => Some (word.of_Z v, cost_lit isRegStr UNK mc)
      | expr.var x => match map.get l x with
                      | Some v => Some (v, cost_set isRegStr UNK x mc)
                      | None => None
                      end
      | expr.inlinetable aSize t index =>
          'Some (index', mc') <- eval_expr index mc | None;
          'Some v <- load aSize (map.of_list_word t) index' | None;
          Some (v, cost_inlinetable isRegStr UNK UNK mc')
      | expr.load aSize a =>
          'Some (a', mc') <- eval_expr a mc | None;
          'Some v <- load aSize m a' | None;
          Some (v, cost_load isRegStr UNK UNK mc')
      | expr.op op e1 e2 =>
          'Some (v1, mc') <- eval_expr e1 mc | None;
          'Some (v2, mc'') <- eval_expr e2 mc' | None;
          Some (interp_binop op v1 v2, cost_op isRegStr UNK UNK UNK mc'')
      | expr.ite c e1 e2 =>
          'Some (vc, mc') <- eval_expr c mc | None;
          eval_expr (if word.eqb vc (word.of_Z 0) then e2 else e1)
                    (cost_if isRegStr UNK (Some UNK) mc')
      end.

    Fixpoint eval_call_args (arges : list expr) (mc : metrics) :=
      match arges with
      | e :: tl =>
        'Some (v, mc') <- eval_expr e mc | None;
        'Some (args, mc'') <- eval_call_args tl mc' | None;
        Some (v :: args, mc'')
      | _ => Some (nil, mc)
      end.

  End WithMemAndLocals.
End semantics.

Module exec. Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.
  Section WithEnv.
  Context (e: env).

  Local Notation metrics := MetricLog.

  Implicit Types post : trace -> mem -> locals -> metrics -> Prop. (* COQBUG: unification finds Type instead of Prop and fails to downgrade *)
  Inductive exec :
    cmd -> trace -> mem -> locals -> metrics ->
    (trace -> mem -> locals -> metrics -> Prop) -> Prop :=
  | skip
    t m l mc post
    (_ : post t m l mc)
    : exec cmd.skip t m l mc post
  | set x e
    t m l mc post
    v mc' (_ : eval_expr m l e mc = Some (v, mc'))
    (_ : post t m (map.put l x v) (cost_set isRegStr x UNK mc'))
    : exec (cmd.set x e) t m l mc post
  | unset x
    t m l mc post
    (_ : post t m (map.remove l x) mc)
    : exec (cmd.unset x) t m l mc post
  | store sz ea ev
    t m l mc post
    a mc' (_ : eval_expr m l ea mc = Some (a, mc'))
    v mc'' (_ : eval_expr m l ev mc' = Some (v, mc''))
    m' (_ : store sz m a v = Some m')
    (_ : post t m' l (cost_store isRegStr UNK UNK mc''))
    : exec (cmd.store sz ea ev) t m l mc post
  | stackalloc x n body
    t mSmall l mc post
    (_ : Z.modulo n (bytes_per_word width) = 0)
    (_ : forall a mStack mCombined,
        anybytes a n mStack ->
        map.split mCombined mSmall mStack ->
        exec body t mCombined (map.put l x a) (cost_stackalloc isRegStr x mc)
          (fun t' mCombined' l' mc' =>
            exists mSmall' mStack',
              anybytes a n mStack' /\
              map.split mCombined' mSmall' mStack' /\
              post t' mSmall' l' mc'))
     : exec (cmd.stackalloc x n body) t mSmall l mc post
  | if_true t m l mc e c1 c2 post
    v mc' (_ : eval_expr m l e mc = Some (v, mc'))
    (_ : word.unsigned v <> 0)
    (_ : exec c1 t m l (cost_if isRegStr UNK (Some UNK) mc') post)
    : exec (cmd.cond e c1 c2) t m l mc post
  | if_false e c1 c2
    t m l mc post
    v mc' (_ : eval_expr m l e mc = Some (v, mc'))
    (_ : word.unsigned v = 0)
    (_ : exec c2 t m l (cost_if isRegStr UNK (Some UNK) mc') post)
    : exec (cmd.cond e c1 c2) t m l mc post
  | seq c1 c2
    t m l mc post
    mid (_ : exec c1 t m l mc mid)
    (_ : forall t' m' l' mc', mid t' m' l' mc' -> exec c2 t' m' l' mc' post)
    : exec (cmd.seq c1 c2) t m l mc post
  | while_false e c
    t m l mc post
    v mc' (_ : eval_expr m l e mc = Some (v, mc'))
    (_ : word.unsigned v = 0)
    (_ : post t m l (cost_loop_false isRegStr UNK (Some UNK) mc'))
    : exec (cmd.while e c) t m l mc post
  | while_true e c
      t m l mc post
      v mc' (_ : eval_expr m l e mc = Some (v, mc'))
      (_ : word.unsigned v <> 0)
      mid (_ : exec c t m l mc' mid)
      (_ : forall t' m' l' mc'', mid t' m' l' mc'' ->
                                 exec (cmd.while e c) t' m' l' (cost_loop_true isRegStr UNK (Some UNK) mc'') post)
    : exec (cmd.while e c) t m l mc post
  | call binds fname arges
      t m l mc post
      params rets fbody (_ : map.get e fname = Some (params, rets, fbody))
      args mc' (_ : eval_call_args m l arges mc = Some (args, mc'))
      lf (_ : map.of_list_zip params args = Some lf)
      mid (_ : exec fbody t m lf mc' mid)
      (_ : forall t' m' st1 mc'', mid t' m' st1 mc'' ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list_zip binds retvs l = Some l' /\
          post t' m' l'  (cost_call PreSpill mc''))
    : exec (cmd.call binds fname arges) t m l mc post
  | interact binds action arges
      t m l mc post
      mKeep mGive (_: map.split m mKeep mGive)
      args mc' (_ :  eval_call_args m l arges mc = Some (args, mc'))
      mid (_ : ext_spec t mGive action args mid)
      (_ : forall mReceive resvals, mid mReceive resvals ->
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (cons ((mGive, action, args), (mReceive, resvals)) t) m' l'
            (cost_interact PreSpill mc'))
    : exec (cmd.interact binds action arges) t m l mc post
  .

  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {ext_spec_ok: ext_spec.ok ext_spec}.

  Lemma weaken: forall t l m mc s post1,
      exec s t m l mc post1 ->
      forall post2: _ -> _ -> _ -> _ -> Prop,
        (forall t' m' l' mc', post1 t' m' l' mc' -> post2 t' m' l' mc') ->
        exec s t m l mc post2.
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

  Lemma intersect: forall t l m mc s post1,
      exec s t m l mc post1 ->
      forall post2,
        exec s t m l mc post2 ->
        exec s t m l mc (fun t' m' l' mc' => post1 t' m' l' mc' /\ post2 t' m' l' mc').
  Proof.
    induction 1;
      intros;
      match goal with
      | H: exec _ _ _ _ _ _ |- _ => inversion H; subst; clear H
      end;
      try match goal with
      | H1: ?e = Some (?x1, ?y1, ?z1), H2: ?e = Some (?x2, ?y2, ?z2) |- _ =>
        replace x2 with x1 in * by congruence;
          replace y2 with y1 in * by congruence;
          replace z2 with z1 in * by congruence;
          clear x2 y2 z2 H2
      end;
      repeat match goal with
             | H1: ?e = Some (?v1, ?mc1), H2: ?e = Some (?v2, ?mc2) |- _ =>
               replace v2 with v1 in * by congruence;
               replace mc2 with mc1 in * by congruence; clear H2
             end;
      repeat match goal with
             | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
               replace v2 with v1 in * by congruence; clear H2
             end;
      try solve [econstructor; eauto | exfalso; congruence].

    - econstructor. 1: eassumption.
      intros.
      rename H0 into Ex1, H12 into Ex2.
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
      + eapply IHexec. exact H16. (* not H2 *)
      + simpl. intros *. intros [? ?].
        edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
        edestruct H17 as (? & ? & ? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
    - pose proof ext_spec.mGive_unique as P.
      specialize P with (1 := H) (2 := H7) (3 := H1) (4 := H14).
      subst mGive0.
      destruct (map.split_diff (map.same_domain_refl mGive) H H7) as (? & _).
      subst mKeep0.
      eapply interact. 1,2: eassumption.
      + eapply ext_spec.intersect; [ exact H1 | exact H14 ].
      + simpl. intros *. intros [? ?].
        edestruct H2 as (? & ? & ?); [eassumption|].
        edestruct H15 as (? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
  Qed.

  End WithEnv.

  Lemma extend_env: forall e1 e2,
      map.extends e2 e1 ->
      forall c t m l mc post,
      exec e1 c t m l mc post ->
      exec e2 c t m l mc post.
  Proof. induction 2; try solve [econstructor; eauto]. Qed.

  End WithParams.
End exec. Notation exec := exec.exec.

Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: ExtSpec}.

  Implicit Types (l: locals) (m: mem).

  Definition call e fname t m args mc post :=
    exists argnames retnames body,
      map.get e fname = Some (argnames, retnames, body) /\
      exists l, map.of_list_zip argnames args = Some l /\
        exec e body t m l mc (fun t' m' l' mc' => exists rets,
          map.getmany_of_list l' retnames = Some rets /\ post t' m' rets mc').

  Lemma weaken_call: forall e fname t m args mc post1,
      call e fname t m args mc post1 ->
      forall (post2: trace -> mem -> list word -> MetricLog -> Prop),
      (forall t' m' rets mc', post1 t' m' rets mc' -> post2 t' m' rets mc') ->
      call e fname t m args mc post2.
  Proof.
    unfold call. intros. fwd.
    do 4 eexists. 1: eassumption.
    do 2 eexists. 1: eassumption.
    eapply exec.weaken. 1: eassumption.
    cbv beta. clear -H0. intros. fwd. eauto.
  Qed.

  Lemma extend_env_call: forall e1 e2,
      map.extends e2 e1 ->
      forall f t m rets mc post,
      call e1 f t m rets mc post ->
      call e2 f t m rets mc post.
  Proof.
    unfold call. intros. fwd. repeat eexists.
    - eapply H. eassumption.
    - eassumption.
    - eapply exec.extend_env; eassumption.
  Qed.

  Lemma of_metrics_free_eval_expr: forall m l e v,
      Semantics.eval_expr m l e = Some v ->
      forall mc, exists mc', MetricSemantics.eval_expr m l e mc = Some (v, mc').
  Proof.
    induction e; cbn; intros;
      repeat match goal with
        | H: Some _ = Some _ |- _ => eapply Option.eq_of_eq_Some in H; subst
        | H: _ = Some _ |- _ => rewrite H
        | IH: forall _, Some _ = Some _ -> _ |- _ => specialize IH with (1 := eq_refl)
        | IH: forall _: MetricLog, exists _: MetricLog, eval_expr ?m ?l ?e _ = Some _
          |- context[eval_expr ?m ?l ?e ?mc] => specialize (IH mc)
        | |- _ => progress fwd
        | |- _ => Tactics.destruct_one_match
        end;
      eauto.
  Qed.

  Lemma to_metrics_free_eval_expr: forall m l e mc v mc',
      MetricSemantics.eval_expr m l e mc = Some (v, mc') ->
      Semantics.eval_expr m l e = Some v.
  Proof.
    induction e; cbn; intros; fwd;
      repeat match goal with
        | IH: forall _ _ _, eval_expr _ _ _ _ = _ -> _, H: eval_expr _ _ _ _ = _ |- _ =>
          specialize IH with (1 := H)
        | H: _ = Some _ |- _ => rewrite H
        | |- _ => Tactics.destruct_one_match
        end;
    try congruence.
  Qed.

  Lemma of_metrics_free_eval_call_args: forall m l arges args,
      Semantics.eval_call_args m l arges = Some args ->
      forall mc, exists mc', MetricSemantics.eval_call_args m l arges mc = Some (args, mc').
  Proof.
    induction arges; cbn; intros.
    - eapply Option.eq_of_eq_Some in H. subst. eauto.
    - fwd.
      eapply of_metrics_free_eval_expr in E. destruct E as (mc' & E). rewrite E.
      specialize IHarges with (1 := eq_refl). specialize (IHarges mc').
      destruct IHarges as (mc'' & IH). rewrite IH. eauto.
  Qed.

  Lemma to_metrics_free_eval_call_args: forall m l arges mc args mc',
      MetricSemantics.eval_call_args m l arges mc = Some (args, mc') ->
      Semantics.eval_call_args m l arges = Some args.
  Proof.
    induction arges; cbn; intros.
    - congruence.
    - fwd.
      eapply to_metrics_free_eval_expr in E. rewrite E.
      specialize IHarges with (1 := E0). rewrite IHarges. reflexivity.
  Qed.

  Context (e: env).

  Lemma of_metrics_free: forall c t m l post,
      Semantics.exec e c t m l post ->
      forall mc, MetricSemantics.exec e c t m l mc (fun t' m' l' _ => post t' m' l').
  Proof.
    induction 1; intros;
      repeat match reverse goal with
        | H: Semantics.eval_expr _ _ _ = Some _ |- _ =>
            eapply of_metrics_free_eval_expr in H; destruct H as (? & H)
        | H: Semantics.eval_call_args _ _ _ = Some _ |- _ =>
            eapply of_metrics_free_eval_call_args in H; destruct H as (? & H)
        end;
      try solve [econstructor; eauto].
  Qed.

  Lemma to_metrics_free: forall c t m l mc post,
      MetricSemantics.exec e c t m l mc post ->
      Semantics.exec e c t m l (fun t' m' l' => exists mc', post t' m' l' mc').
  Proof.
    induction 1; intros;
      repeat match reverse goal with
        | H: eval_expr _ _ _ _ = Some _ |- _ =>
            eapply to_metrics_free_eval_expr in H
        | H: eval_call_args _ _ _ _ = Some _ |- _ =>
            eapply to_metrics_free_eval_call_args in H
        end;
      try solve [econstructor; eauto].
    { econstructor. 1: eauto.
      intros.
      eapply Semantics.exec.weaken. 1: eapply H1. all: eauto.
      cbv beta.
      clear. firstorder idtac. }
    { econstructor.
      1: eapply IHexec.
      cbv beta. intros.
      fwd.
      eapply H1. eassumption. }
    { econstructor; [ eassumption .. | ].
      cbv beta. intros. fwd. eapply H3. eassumption. }
    { econstructor. 1-4: eassumption.
      cbv beta. intros. fwd. specialize H3 with (1 := H4). fwd. eauto 10. }
    { econstructor. 1-3: eassumption.
      intros. specialize H2 with (1 := H3). fwd. eauto. }
  Qed.

  Lemma of_metrics_free_call: forall f t m args post,
      Semantics.call e f t m args post ->
      forall mc, call e f t m args mc (fun t' m' rets _ => post t' m' rets).
  Proof.
    unfold call, Semantics.call. intros. fwd. eauto 10 using of_metrics_free.
  Qed.

  Lemma to_metrics_free_call: forall f t m args mc post,
      call e f t m args mc post ->
      Semantics.call e f t m args (fun t' m' rets => exists mc', post t' m' rets mc').
  Proof.
    unfold call, Semantics.call. intros. fwd.
    do 4 eexists. 1: eassumption. do 2 eexists. 1: eassumption.
    eapply Semantics.exec.weaken. 1: eapply to_metrics_free. 1: eassumption.
    cbv beta. clear. firstorder idtac.
  Qed.
End WithParams.
