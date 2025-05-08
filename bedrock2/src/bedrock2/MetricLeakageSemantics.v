Require Import coqutil.sanity coqutil.Byte.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Properties.
Require coqutil.Map.SortedListString.
Require Import coqutil.Z.Lia.
Require Import bedrock2.Syntax coqutil.Map.Interface coqutil.Map.OfListWord.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Export bedrock2.Memory.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.MetricCosts.
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
      | expr.op1 op e1 =>
          '(v1, k', mc') <- eval_expr e1 k mc;
          Some (interp_op1 op v1, leak_op1 op v1 ++ k', cost_op1 isRegStr UNK UNK mc')
      | expr.op op e1 e2 =>
          '(v1, k', mc') <- eval_expr e1 k mc;
          '(v2, k'', mc'') <- eval_expr e2 k' mc';
          Some (interp_binop op v1 v2, leak_binop op v1 v2 ++ k'', cost_op isRegStr UNK UNK UNK mc'')
      | expr.ite c e1 e2 =>
          '(vc, k', mc') <- eval_expr c k mc;
          let b := word.eqb vc (word.of_Z 0) in
          eval_expr (if b then e2 else e1) (leak_bool (negb b) :: k')
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
  Context {ext_spec: ExtSpec}.
  Section WithEnv.
  Context (e: env).

  Local Notation metrics := MetricLog.

  Implicit Types post : leakage -> trace -> mem -> locals -> metrics -> Prop. (* COQBUG: unification finds Type instead of Prop and fails to downgrade *)
  Inductive exec {pick_sp: PickSp} :
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

  Lemma weaken {pick_sp: PickSp} : forall s k t m l mc post1,
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

  Lemma intersect {pick_sp: PickSp} : forall k t l m mc s post1,
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

  Lemma eval_expr_extends_trace :
    forall e0 m l mc k v mc' k',
    eval_expr m l e0 k mc = Some (v, k', mc') ->
    exists k'', k' = k'' ++ k.
  Proof.
    intros e0. induction e0; intros; simpl in *;
      repeat match goal with
        | H: (let (_, _) := ?x in _) = _ |- _ =>
            destruct x
        | H: match ?x with
             | Some _ => _
             | None => _
             end = Some (_, _, _) |- _ =>
            destruct x eqn:?; try congruence
        | H: Some (?v1, ?mc1, ?t1) = Some (?v2, ?mc2, ?t2) |- _ =>
            injection H; intros; subst
        end.
    - eexists. align_trace.
    - eexists. align_trace.
    - specialize IHe0 with (1 := Heqo). fwd. eexists. align_trace.
    - specialize IHe0 with (1 := Heqo). fwd. eexists. align_trace.
    - specialize IHe0 with (1 := Heqo). fwd. eexists. align_trace.
    - specialize IHe0_1 with (1 := Heqo). specialize IHe0_2 with (1 := Heqo0). fwd.
      eexists. align_trace.
    - specialize IHe0_1 with (1 := Heqo). destruct (word.eqb _ _).
      + specialize IHe0_3 with (1 := H). fwd. eexists. align_trace.
      + specialize IHe0_2 with (1 := H). fwd. eexists. align_trace.
  Qed.

  Lemma eval_call_args_extends_trace :
    forall arges m l mc k args mc' k',
    eval_call_args m l arges k mc = Some (args, k', mc') ->
    exists k'', k' = k'' ++ k.
  Proof.
    intros arges. induction arges.
    - simpl. intros. injection H. intros. subst. eexists. align_trace.
    - simpl. intros. destruct (eval_expr _ _ _ _ _) eqn:E1; try congruence.
      destruct p. destruct p. destruct (eval_call_args _ _ _ _ _) eqn:E2; try congruence.
      destruct p. destruct p. injection H. intros. subst.
      apply eval_expr_extends_trace in E1. specialize IHarges with (1 := E2).
      fwd. eexists. align_trace.
  Qed.

  Lemma expr_to_other_trace m l a mc mc' k1 k1' v :
    eval_expr m l a k1 mc = Some (v, k1', mc') ->
    exists k'',
      k1' = k'' ++ k1 /\
        forall k2,
          eval_expr m l a k2 mc = Some (v, k'' ++ k2, mc').
  Proof.
    revert v. revert mc. revert k1. revert k1'. revert mc'. clear.
    induction a; intros ? ? ? ? ? H; simpl in H; try (inversion H; subst; clear H).
    - exists nil. auto.
    - destruct (map.get l x) as [v0|] eqn:E; [|congruence]. inversion H1; subst; clear H1.
      exists nil. simpl. rewrite E. auto.
    - destruct (eval_expr _ _ _) as [v0|] eqn:E1; [|congruence].
      destruct v0. destruct p. destruct (load _ _ _) as [v0|] eqn:E2; [|congruence].
      inversion H1; subst; clear H1. eapply IHa in E1. destruct E1 as [k'' [E1 E3] ]. subst.
      eexists (_ :: _). intuition. simpl. rewrite E3. rewrite E2. reflexivity.
    - destruct (eval_expr _ _ _) as [v0|] eqn:E1; [|congruence].
      destruct v0. destruct p. destruct (load _ _ _) as [v0|] eqn:E2; [|congruence].
      inversion H1; subst; clear H1. eapply IHa in E1. destruct E1 as [k'' [E1 E3] ]. subst.
      eexists (_ :: _). intuition. simpl. rewrite E3. rewrite E2. reflexivity.
    - destruct (eval_expr _ _ a _ _) as [ [ [v0 mc0] p0]|] eqn:E1; [|congruence].
      inversion H1; subst; clear H1.
      eapply IHa in E1. destruct E1 as [k''1 [H1 H2] ].
      subst.
      eexists (_ ++ _). repeat rewrite <- (app_assoc _ _ k1). intuition.
      simpl. rewrite H2. f_equal. f_equal. repeat rewrite <- (app_assoc _ _ k2).
      reflexivity.
    - destruct (eval_expr _ _ a1 _ _) as [ [ [v0 mc0] p0]|] eqn:E1; [|congruence].
      destruct (eval_expr _ _ a2 _ _) as [ [ [v1 mc1] p1]|] eqn:E2; [|congruence].
      inversion H1; subst; clear H1.
      eapply IHa1 in E1. destruct E1 as [k''1 [H1 H2] ]. eapply IHa2 in E2.
      destruct E2 as [k''2 [H3 H4] ]. subst.
      eexists (_ ++ _ ++ _). repeat rewrite <- (app_assoc _ _ k1). intuition.
      simpl. rewrite H2. rewrite H4. f_equal. f_equal. repeat rewrite <- (app_assoc _ _ k2).
      reflexivity.
    - destruct (eval_expr _ _ a1 _ _) as [ [ [v0 mc0] p0]|] eqn:E1; [|congruence].
      eapply IHa1 in E1. destruct E1 as [k''1 [H2 H3] ]. subst. simpl.
      destruct (word.eqb _ _) eqn:E.
      + eapply IHa3 in H1. destruct H1 as [k''3 [H1 H2] ]. subst.
        eexists (_ ++ _ :: _). repeat rewrite <- (app_assoc _ _ k1).
        intuition. rewrite H3. rewrite E. rewrite H2.
        repeat rewrite <- (app_assoc _ _ k2). reflexivity.
      + eapply IHa2 in H1. destruct H1 as [k''2 [H1 H2] ]. subst.
        eexists (_ ++ _ :: _). repeat rewrite <- (app_assoc _ _ k1).
        intuition. rewrite H3. rewrite E. rewrite H2.
        repeat rewrite <- (app_assoc _ _ k2). reflexivity.
  Qed.

    Lemma call_args_to_other_trace (m : mem) l arges mc k1 vs mc' k1' :
      eval_call_args m l arges k1 mc = Some (vs, k1', mc') ->
      exists k'',
        k1' = k'' ++ k1 /\
          forall k2,
            eval_call_args m l arges k2 mc = Some (vs, k'' ++ k2, mc').
    Proof.
      revert mc. revert k1. revert vs. revert mc'. revert k1'. induction arges; intros.
      - cbn [eval_call_args] in H. inversion H. subst.
        exists nil. intuition.
      - cbn [eval_call_args] in *.
        destruct (eval_expr _ _ _) as [ [ [v0 mc0] p0]|] eqn:E1; [|congruence].
        destruct (eval_call_args _ _ _) as [ [ [v1 mc1] p1]|] eqn:E2; [|congruence].
        apply expr_to_other_trace in E1. apply IHarges in E2. fwd.
        eexists (_ ++ _).
        repeat rewrite <- (app_assoc _ _ k1). intuition. repeat rewrite <- (app_assoc _ _ k2).
        rewrite E1p1. rewrite E2p1. reflexivity.
    Qed.

  Local Ltac subst_exprs :=
    repeat match goal with
      | H : eval_expr _ _ _ _ _ = Some _ |- _ =>
          apply eval_expr_extends_trace in H; destruct H; subst
      | H : eval_call_args _ _ _ _ _ = Some _ |- _ =>
          apply eval_call_args_extends_trace in H; destruct H; subst
        end.

  Lemma exec_extends_trace {pick_sp: PickSp} s k t m l mc post :
    exec s k t m l mc post ->
    exec s k t m l mc (fun k' t' m' l' mc' => post k' t' m' l' mc' /\ exists k'', k' = k'' ++ k).
  Proof.
    intros H. induction H; try (econstructor; intuition eauto; subst_exprs; eexists; align_trace; fail).
    - econstructor; intuition eauto. intros. eapply weaken. 1: eapply H1; eauto.
      simpl. intros. fwd. eexists. eexists. intuition eauto. eexists. align_trace.
    - eapply if_true; intuition eauto. eapply weaken. 1: eapply IHexec.
      simpl. intros. fwd. intuition eauto. subst_exprs. eexists. align_trace.
    - eapply if_false; intuition eauto. eapply weaken. 1: eapply IHexec.
      simpl. intros. fwd. intuition eauto. subst_exprs. eexists. align_trace.
    - econstructor; intuition eauto. fwd. eapply weaken. 1: eapply H1; eauto.
      simpl. intros. fwd. intuition eauto. eexists. align_trace.
    - eapply while_true; eauto. simpl. intros. fwd. eapply weaken. 1: eapply H3; eauto.
      simpl. intros. fwd. intuition eauto. subst_exprs. eexists. align_trace.
    - econstructor; intuition eauto. fwd. specialize H3 with (1 := H4p0). fwd.
      eexists. intuition eauto. eexists. intuition eauto. subst_exprs.
      eexists. align_trace.
    - econstructor; intuition eauto. specialize H2 with (1 := H3). fwd.
      eexists. intuition eauto. subst_exprs. eexists. align_trace.
  Qed.

  Lemma exec_ext (pick_sp1: PickSp) s k t m l mc post :
    exec (pick_sp := pick_sp1) s k t m l mc post ->
    forall pick_sp2,
    (forall k', pick_sp1 (k' ++ k) = pick_sp2 (k' ++ k)) ->
    exec (pick_sp := pick_sp2) s k t m l mc post.
  Proof.
    intros H1 pick_sp2. induction H1; intros; try solve [econstructor; eauto].
    - econstructor; eauto. intros. replace (pick_sp1 k) with (pick_sp2 k) in *.
      { subst a. eapply weaken.
        { eapply H1; eauto.
          intros. eassert (H2' := H2 (_ ++ _ :: nil)). rewrite <- app_assoc in H2'. eapply H2'. }
        eauto. }
      symmetry. apply H2 with (k' := nil).
    - eapply if_true; eauto. eapply IHexec. subst_exprs.
      intros. eassert (H2' := H2 (_ ++ _ :: _)). rewrite <- app_assoc in H2'. eapply H2'.
    - eapply if_false; eauto. eapply IHexec. subst_exprs.
      intros. eassert (H2' := H2 (_ ++ _ :: _)). rewrite <- app_assoc in H2'. eapply H2'.
    - econstructor. 1: eapply exec_extends_trace; eauto. simpl. intros. fwd.
      eapply H0; eauto. intros. repeat rewrite app_assoc. apply H2.
    - eapply while_true; intuition eauto.
      { eapply exec_extends_trace. eapply IHexec. subst_exprs.
        intros. simpl. rewrite associate_one_left. rewrite app_assoc. apply H4. }
      simpl in *. fwd. eapply H3; eauto. intros. subst_exprs.
      rewrite associate_one_left. repeat rewrite app_assoc. auto.
    - econstructor. 4: eapply exec_extends_trace. all: intuition eauto.
      { eapply IHexec. subst_exprs. intros.
        rewrite associate_one_left. repeat rewrite app_assoc. auto. }
      fwd. specialize H3 with (1 := H5p0). fwd. intuition eauto.
  Qed.

  Local Ltac solve_picksps_equal :=
    intros; cbv beta; f_equal;
    repeat (rewrite rev_app_distr || cbn [rev app]); rewrite List.skipn_app_r;
    [|repeat (rewrite app_length || rewrite rev_length || simpl); blia];
    repeat rewrite <- app_assoc; rewrite List.skipn_app_r;
    [|rewrite rev_length; reflexivity];
    repeat (rewrite rev_app_distr || cbn [rev app] || rewrite rev_involutive);
    repeat rewrite <- app_assoc; reflexivity.

  Lemma exec_to_other_trace (pick_sp: PickSp) s k1 k2 t m l mc post :
    exec s k1 t m l mc post ->
    exec (pick_sp := fun k => pick_sp (rev (skipn (length k2) (rev k)) ++ k1))
      s k2 t m l mc (fun k2' t' m' l' mc' =>
                       exists k'',
                         k2' = k'' ++ k2 /\
                           post (k'' ++ k1) t' m' l' mc').
  Proof.
    intros H. generalize dependent k2. induction H; intros.
    - econstructor. exists nil. eauto.
    - apply expr_to_other_trace in H. destruct H as [k'' [H1 H2] ]. subst.
      econstructor; intuition eauto.
    - econstructor; intuition. exists nil. intuition.
    - apply expr_to_other_trace in H. apply expr_to_other_trace in H0.
      destruct H as [k''a [H3 H4] ]. subst. destruct H0 as [k''v [H5 H6] ]. subst.
      econstructor; intuition eauto. eexists (_ :: _ ++ _). simpl.
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - econstructor; intuition. intros.
      replace (rev k2) with (rev k2 ++ nil) in * by apply app_nil_r. Search (length (rev _)).
      rewrite List.skipn_app_r in * by (rewrite rev_length; reflexivity).
      simpl in *. eapply weaken.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply H1; eauto. solve_picksps_equal. }
      simpl. intros. fwd. eexists _, _. intuition eauto. eexists (_ ++ _ :: nil).
      rewrite <- app_assoc. simpl. rewrite <- (app_assoc _ _ k). simpl. eauto.
    - apply expr_to_other_trace in H. fwd. eapply if_true; intuition eauto.
      eapply weaken.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec. solve_picksps_equal. }
      simpl. intros. fwd. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply expr_to_other_trace in H. fwd. eapply if_false; intuition.
      eapply weaken.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec. solve_picksps_equal. }
      simpl. intros. fwd. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - econstructor; intuition. fwd. eapply weaken.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply H1; eauto. solve_picksps_equal. }
      simpl. intros. fwd. eexists (_ ++ _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply expr_to_other_trace in H. fwd. eapply while_false; intuition.
      eexists (_ :: _). intuition.
    - apply expr_to_other_trace in H. fwd. eapply while_true; intuition.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec. solve_picksps_equal. }
      cbv beta in *. fwd. eapply weaken.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply H3; eauto. solve_picksps_equal. }
      simpl. intros. fwd. eexists (_ ++ _ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply call_args_to_other_trace in H0.
      fwd. econstructor; intuition eauto.
      { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec; eauto. solve_picksps_equal. }
      cbv beta in *. fwd. apply H3 in H0p2.
      fwd. exists retvs. intuition. exists l'. intuition. eexists (_ ++ _ :: _).
      repeat rewrite <- (app_assoc _ _ k2). repeat rewrite <- (app_assoc _ _ k).
      intuition.
    - apply call_args_to_other_trace in H0. fwd. econstructor; intuition eauto.
      apply H2 in H0. fwd. exists l'. intuition. eexists (_ :: _).
      intuition.
  Qed.

  End WithEnv.

  Lemma extend_env {pick_sp: PickSp} : forall e1 e2,
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
End WithParams.
