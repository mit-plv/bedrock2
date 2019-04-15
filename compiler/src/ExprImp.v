Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Program.Tactics.
Require Import riscv.Utility.Utility.
Require Export bedrock2.Syntax.
Require Export bedrock2.Semantics.
Require Import coqutil.Macros.unique.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PropSet.
Require Import riscv.Utility.ListLib.
Require Import compiler.Simp.

Local Set Ltac Profiling.

Open Scope Z_scope.

Local Notation "' x <- a ; f" :=
  (match (a: option _) with
   | x => f
   | _ => None
   end)
  (right associativity, at level 70, x pattern).

Section ExprImp1.

  Context {p : unique! Semantics.parameters}.

  Notation var := (@Syntax.varname (@Semantics.syntax p)) (only parsing).
  Notation func := (@Syntax.funname (@Semantics.syntax p)) (only parsing).
  Notation vars := (var -> Prop).

  (*Hypothesis actname_empty: Syntax.actname = Empty_set.*)
  Local Notation actname := Syntax.actname.

  Ltac set_solver := set_solver_generic (@Syntax.varname (@Semantics.syntax p)).
  Context {word_ok: word.ok word}. (* TODO which param record? *)

  Section WithEnv.
    Context (e: env).

    Fixpoint eval_cmd(f: nat)(st: locals)(m: mem)(s: cmd): option (locals * mem) :=
      match f with
      | O => None (* out of fuel *)
      | S f => match s with
        | cmd.store aSize a v =>
            'Some a <- eval_expr m st a;
            'Some v <- eval_expr m st v;
            'Some m <- store aSize m a v;
            Some (st, m)
        | cmd.set x e =>
            'Some v <- eval_expr m st e;
            Some (map.put st x v, m)
        | cmd.unset x =>
            Some (map.remove st x, m)
        | cmd.cond cond bThen bElse =>
            'Some v <- eval_expr m st cond;
            eval_cmd f st m (if word.eqb v (word.of_Z 0) then bElse else bThen)
        | cmd.while cond body =>
            'Some v <- eval_expr m st cond;
            if word.eqb v (word.of_Z 0) then Some (st, m) else
              'Some (st, m) <- eval_cmd f st m body;
              eval_cmd f st m (cmd.while cond body)
        | cmd.seq s1 s2 =>
            'Some (st, m) <- eval_cmd f st m s1;
            eval_cmd f st m s2
        | cmd.skip => Some (st, m)
        | cmd.call binds fname args =>
          'Some (params, rets, fbody) <- map.get e fname;
          'Some argvs <- List.option_all (List.map (eval_expr m st) args);
          'Some st0 <- map.putmany_of_list params argvs map.empty;
          'Some (st1, m') <- eval_cmd f st0 m fbody;
          'Some retvs <- map.getmany_of_list st1 rets;
          'Some st' <- map.putmany_of_list binds retvs st;
          Some (st', m')
        | cmd.interact _ _ _ => None (* unsupported *)
        end
      end.

    Fixpoint expr_size(e: expr): Z :=
      match e with
      | expr.literal _ => 15
      | expr.load _ e => expr_size e + 1
      | expr.var _ => 1
      | expr.op op e1 e2 => expr_size e1 + expr_size e2 + 2
      end.

    Lemma expr_size_pos: forall exp, expr_size exp > 0.
    Proof.
      induction exp; simpl; try blia.
    Qed.

    Definition exprs_size(es: list expr): Z := fold_right (fun e res => res + expr_size e) 0 es.

    Fixpoint cmd_size(s: cmd): Z :=
      match s with
      | cmd.store _ a v => expr_size a + expr_size v + 1
      | cmd.set x e => expr_size e
      | cmd.cond cond bThen bElse => expr_size cond + cmd_size bThen + cmd_size bElse + 2
      | cmd.while cond body => expr_size cond + cmd_size body + 2
      | cmd.seq s1 s2 => cmd_size s1 + cmd_size s2
      | cmd.skip | cmd.unset _ => 0
      | cmd.call binds f args => exprs_size args + 1000 (* TODO *)
      | cmd.interact _ _ exprs => exprs_size exprs
                                  + 7 (* randomly chosen max allowed number of instructions
                                         one interaction can be compiled to, TODO parametrize
                                         over this *)
      end.

    Lemma exprs_size_nonneg: forall es, 0 <= exprs_size es.
    Proof.
      induction es; simpl in *; try blia. pose proof (expr_size_pos a). blia.
    Qed.

    Lemma cmd_size_nonneg: forall s, 0 <= cmd_size s.
    Proof.
      induction s; simpl;
      repeat match goal with
      | e: expr |- _ => unique pose proof (expr_size_pos e)
      | es: list expr |- _ => unique pose proof (exprs_size_nonneg es)
      | l: list _ |- _ => unique pose proof (Zlength_nonneg l)
      end;
      try blia.
    Qed.

    Local Ltac inversion_lemma :=
      intros;
      simpl in *;
      repeat (destruct_one_match_hyp; try discriminate);
      repeat match goal with
             | E: _ _ _ = true  |- _ => apply word.eqb_true  in E
             | E: _ _ _ = false |- _ => apply word.eqb_false in E
             end;
      simp;
      subst;
      eauto 10.

    Lemma invert_eval_store: forall fuel initialSt initialM a v final aSize,
      eval_cmd (S fuel) initialSt initialM (cmd.store aSize a v) = Some final ->
      exists av vv finalM, eval_expr initialM initialSt a = Some av /\
                           eval_expr initialM initialSt v = Some vv /\
                           store aSize initialM av vv = Some finalM /\
                           final = (initialSt, finalM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_set: forall f st1 m1 p2 x e,
      eval_cmd (S f) st1 m1 (cmd.set x e) = Some p2 ->
      exists v, eval_expr m1 st1 e = Some v /\ p2 = (map.put st1 x v, m1).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_unset: forall f st1 m1 p2 x,
      eval_cmd (S f) st1 m1 (cmd.unset x) = Some p2 ->
      p2 = (map.remove st1 x, m1).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_cond: forall f st1 m1 p2 cond bThen bElse,
      eval_cmd (S f) st1 m1 (cmd.cond cond bThen bElse) = Some p2 ->
      exists cv,
        eval_expr m1 st1 cond = Some cv /\
        (cv <> word.of_Z 0 /\ eval_cmd f st1 m1 bThen = Some p2 \/
         cv = word.of_Z 0  /\ eval_cmd f st1 m1 bElse = Some p2).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_while: forall st1 m1 p3 f cond body,
      eval_cmd (S f) st1 m1 (cmd.while cond body) = Some p3 ->
      exists cv,
        eval_expr m1 st1 cond = Some cv /\
        (cv <> word.of_Z 0 /\ (exists st2 m2, eval_cmd f st1 m1 body = Some (st2, m2) /\
                                     eval_cmd f st2 m2 (cmd.while cond body) = Some p3) \/
         cv = word.of_Z 0 /\ p3 = (st1, m1)).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_seq: forall st1 m1 p3 f s1 s2,
      eval_cmd (S f) st1 m1 (cmd.seq s1 s2) = Some p3 ->
      exists st2 m2, eval_cmd f st1 m1 s1 = Some (st2, m2) /\ eval_cmd f st2 m2 s2 = Some p3.
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_skip: forall st1 m1 p2 f,
      eval_cmd (S f) st1 m1 cmd.skip = Some p2 ->
      p2 = (st1, m1).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_call : forall st m1 p2 f binds fname args,
      eval_cmd (S f) st m1 (cmd.call binds fname args) = Some p2 ->
      exists params rets fbody argvs st0 st1 m' retvs st',
        map.get e fname = Some (params, rets, fbody) /\
        List.option_all (List.map (eval_expr m1 st) args) = Some argvs /\
        map.putmany_of_list params argvs map.empty = Some st0 /\
        eval_cmd f st0 m1 fbody = Some (st1, m') /\
        map.getmany_of_list st1 rets = Some retvs /\
        map.putmany_of_list binds retvs st = Some st' /\
        p2 = (st', m').
    Proof. inversion_lemma. eauto 16. Qed.

    Lemma invert_eval_interact : forall st m1 p2 f binds fname args,
      eval_cmd (S f) st m1 (cmd.interact binds fname args) = Some p2 ->
      False.
    Proof. inversion_lemma. discriminate. Qed.

  End WithEnv.

  (* Returns a list to make it obvious that it's a finite set. *)
  Fixpoint allVars_expr_as_list(e: expr): list var :=
    match e with
    | expr.literal v => []
    | expr.var x => [x]
    | expr.load nbytes e => allVars_expr_as_list e
    | expr.op op e1 e2 => (allVars_expr_as_list e1) ++ (allVars_expr_as_list e2)
    end.

  Definition allVars_exprs_as_list(es: list expr): list var :=
    List.flat_map allVars_expr_as_list es.

  Fixpoint allVars_cmd_as_list(s: cmd): list var :=
    match s with
    | cmd.store _ a e => (allVars_expr_as_list a) ++ (allVars_expr_as_list e)
    | cmd.set v e => v :: allVars_expr_as_list e
    | cmd.unset v => v :: nil
    | cmd.cond c s1 s2 => (allVars_expr_as_list c) ++ (allVars_cmd_as_list s1) ++ (allVars_cmd_as_list s2)
    | cmd.while c body => (allVars_expr_as_list c) ++ (allVars_cmd_as_list body)
    | cmd.seq s1 s2 => (allVars_cmd_as_list s1) ++ (allVars_cmd_as_list s2)
    | cmd.skip => []
    | cmd.call binds _ args => binds ++ allVars_exprs_as_list args
    | cmd.interact binds _ args => binds ++ allVars_exprs_as_list args
    end.

  Fixpoint allVars_expr(e: expr): set var :=
    match e with
    | expr.literal v => empty_set
    | expr.var x => singleton_set x
    | expr.load nbytes e => allVars_expr e
    | expr.op op e1 e2 => union (allVars_expr e1) (allVars_expr e2)
    end.

  Definition allVars_exprs(es: list expr): set var :=
    List.fold_right union empty_set (List.map allVars_expr es).

  Fixpoint allVars_cmd(s: cmd): set var :=
    match s with
    | cmd.store _ a e => union (allVars_expr a) (allVars_expr e)
    | cmd.set v e => add (allVars_expr e) v
    | cmd.unset v => singleton_set v
    | cmd.cond c s1 s2 => union (allVars_expr c) (union (allVars_cmd s1) (allVars_cmd s2))
    | cmd.while c body => union (allVars_expr c) (allVars_cmd body)
    | cmd.seq s1 s2 => union (allVars_cmd s1) (allVars_cmd s2)
    | cmd.skip => empty_set
    | cmd.call binds _ args => union (of_list binds) (allVars_exprs args)
    | cmd.interact binds _ args => union (of_list binds) (allVars_exprs args)
    end.

  Lemma allVars_expr_allVars_expr_as_list: forall e x,
      x \in allVars_expr e <-> In x (allVars_expr_as_list e).
  Proof.
    induction e; intros; simpl in *; set_solver; try apply in_or_app; set_solver.
    apply in_app_or in H3.
    destruct H3; eauto.
  Qed.

  Lemma allVars_exprs_allVars_exprs_as_list: forall es x,
      x \in allVars_exprs es <-> In x (allVars_exprs_as_list es).
  Proof.
    induction es; intros; simpl in *; set_solver.
    - apply in_or_app. unfold allVars_exprs in H1. simpl in H1.
      pose proof (allVars_expr_allVars_expr_as_list a).
      set_solver.
    - apply in_app_or in H1. unfold allVars_exprs.
      pose proof (allVars_expr_allVars_expr_as_list a).
      simpl. destruct H1; set_solver.
  Qed.

  Lemma allVars_cmd_allVars_cmd_as_list: forall s x,
      x \in allVars_cmd s <-> In x (allVars_cmd_as_list s).
  Proof.
    induction s; intros; simpl in *;
      repeat match goal with
             | e: expr |- _ => unique pose proof (allVars_expr_allVars_expr_as_list e x)
             | es: list expr |- _ => unique pose proof (allVars_exprs_allVars_exprs_as_list es x)
             | _: context [?l1 ++ ?l2] |- _ =>
               unique pose proof (in_app_or l1 l2 x)
             | |- context [?l1 ++ ?l2] =>
               unique pose proof (in_or_app l1 l2 x)
             end;
      try solve [set_solver].
  Qed.

  (* Returns a static approximation of the set of modified vars.
     The returned set might be too big, but is guaranteed to include all modified vars. *)
  Fixpoint modVars(s: cmd): vars :=
    match s with
    | cmd.store _ _ _ => empty_set
    | cmd.set v _ | cmd.unset v => singleton_set v
    | cmd.cond _ s1 s2 => union (modVars s1) (modVars s2)
    | cmd.while _ body => modVars body
    | cmd.seq s1 s2 => union (modVars s1) (modVars s2)
    | cmd.skip => empty_set
    | cmd.call binds _ _ => of_list binds
    | cmd.interact binds _ _ => of_list binds
    end.

  Lemma modVars_subset_allVars: forall s, subset (modVars s) (allVars_cmd s).
  Proof.
    intros. induction s; simpl in *; set_solver.
  Qed.

End ExprImp1.


Ltac invert_eval_cmd :=
  lazymatch goal with
  | E: eval_cmd _ (S ?fuel) _ _ ?s = Some _ |- _ =>
    destruct s;
    [ apply invert_eval_skip in E
    | apply invert_eval_set in E
    | apply invert_eval_unset in E
    | apply invert_eval_store in E
    | apply invert_eval_cond in E
    | apply invert_eval_seq in E
    | apply invert_eval_while in E
    | apply invert_eval_call in E
    | apply invert_eval_interact in E ];
    deep_destruct E;
    [ let x := fresh "Case_skip" in pose proof tt as x; move x at top
    | let x := fresh "Case_set" in pose proof tt as x; move x at top
    | let x := fresh "Case_unset" in pose proof tt as x; move x at top
    | let x := fresh "Case_store" in pose proof tt as x; move x at top
    | let x := fresh "Case_cond_Then" in pose proof tt as x; move x at top
    | let x := fresh "Case_cond_Else" in pose proof tt as x; move x at top
    | let x := fresh "Case_seq" in pose proof tt as x; move x at top
    | let x := fresh "Case_while_Done" in pose proof tt as x; move x at top
    | let x := fresh "Case_while_NotDone" in pose proof tt as x; move x at top
    | let x := fresh "Case_call" in pose proof tt as x; move x at top
    | let x := fresh "Case_interact" in pose proof tt as x; move x at top
    ]
  end.


Section ExprImp2.

  Context {p : unique! Semantics.parameters}.

  Notation var := (@Syntax.varname (@Semantics.syntax p)) (only parsing).
  Notation func := (@Syntax.funname (@Semantics.syntax p)) (only parsing).
  Notation vars := (var -> Prop).

  (*Hypothesis actname_empty: Syntax.actname = Empty_set.*)
  Local Notation actname := Syntax.actname.

  Context {word_ok: word.ok word}. (* TODO which param record? *)
  Context {locals_ok: map.ok locals}.
  Context {varname_dec: DecidableEq Syntax.varname}.

  Ltac state_calc := map_solver locals_ok.
  Ltac set_solver := set_solver_generic (@Syntax.varname (@Semantics.syntax p)).

  Lemma modVarsSound_fixpointsemantics: forall (e: env) fuel s initialS initialM finalS finalM,
    eval_cmd e fuel initialS initialM s = Some (finalS, finalM) ->
    map.only_differ initialS (modVars s) finalS.
  Proof.
    induction fuel; intros *; intro Ev.
    - discriminate.
    - invert_eval_cmd; simpl in *; simp; subst;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          simpl in IH';
          ensure_new IH'
      end;
      try solve [state_calc | refine (map.only_differ_putmany _ _ _ _ _); eassumption].
  Qed.

  (* TODO is this the canconical form to impose as a requirement?
     Or should we impose post1 <-> post2, or something else? *)
  Axiom ext_spec_intersect: forall t mGive1 mGive2 a args post1 post2,
    ext_spec t mGive1 a args post1 ->
    ext_spec t mGive2 a args post2 ->
    mGive1 = mGive2 /\ (* TODO will this be provable? *)
    ext_spec t mGive1 a args (fun mReceive resvals => post1 mReceive resvals /\
                                                     post2 mReceive resvals).

  Lemma map_split_diff: forall {m m1 m2 m3: mem},
      map.split m m2 m1 ->
      map.split m m3 m1 ->
      m2 = m3.
  Proof.
    unfold map.split.
    intros *. intros [? ?] [? ?].
  Admitted.

  Lemma map_split_det: forall {m m' m1 m2: mem},
      map.split m  m1 m2 ->
      map.split m' m1 m2 ->
      m = m'.
  Proof.
    unfold map.split.
    intros *. intros [? ?] [? ?].
    subst.
    reflexivity.
  Qed.

  Lemma intersect_exec: forall env t l m s post1,
      exec env s t m l post1 ->
      forall post2,
        exec env s t m l post2 ->
        exec env s t m l (fun t' m' l' => post1 t' m' l' /\ post2 t' m' l').
  Proof.
    induction 1; intros;
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
             | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
               replace v2 with v1 in * by congruence; clear H2
             end;
      try solve [econstructor; eauto | exfalso; congruence].

    - econstructor.
      + eapply IHexec. exact H5. (* not H *)
      + simpl. intros *. intros [? ?]. eauto.
    - eapply exec.while_true. 1, 2: eassumption.
      + eapply IHexec. exact H9. (* not H1 *)
      + simpl. intros *. intros [? ?]. eauto.
    - eapply exec.call. 1, 2, 3: eassumption.
      + eapply IHexec. exact H15. (* not H2 *)
      + simpl. intros *. intros [? ?].
        edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
        edestruct H16 as (? & ? & ? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        eauto 10.
    - pose proof ext_spec_intersect as P.
      specialize P with (1 := H1) (2 := H13). destruct P as [? P]. subst mGive0.
      pose proof (map_split_diff H H7). subst mKeep0. clear H7.
      eapply exec.interact. 1,2: eassumption.
      + eapply ext_spec_intersect; [ exact H1 | exact H13 ].
      + simpl. intros *. intros [? ?].
        edestruct H2 as (? & ? & ?); [eassumption|].
        edestruct H14 as (? & ? & ?); [eassumption|].
        repeat match goal with
               | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
                 replace v2 with v1 in * by congruence; clear H2
               end.
        destruct H6 as (m'1 & S1 & P1).
        destruct H8 as (m'2 & S2 & P2).
        pose proof (map_split_det S1 S2) as Q. subst m'2. rename m'1 into m'.
        eauto 10.
  Qed.

  Lemma weaken_exec: forall env t l m s post1,
      exec env s t m l post1 ->
      forall post2: _ -> _ -> _ -> Prop,
        (forall t' m' l', post1 t' m' l' -> post2 t' m' l') ->
        exec env s t m l post2.
  Proof.
    induction 1; intros; try solve [econstructor; eauto].
    - eapply @exec.call.
      4: eapply IHexec.
      all: eauto.
      intros.
      edestruct H3 as (? & ? & ? & ? & ?); [eassumption|].
      eauto 10.
    - eapply @exec.interact; try eassumption.
      intros.
      edestruct H2 as (? & ? & ?); [eassumption|].
      destruct H6 as (? & ? & ?).
      eauto 10.
  Qed.

  (* As we see, one can prove this lemma as is, but the proof is a bit cumbersome because
     the seq and while case have to instantiate mid with the intersection, and use
     intersect_exec to prove it.
     And it turns out that users of this lemma will encounter the same problem:
     What they really want is one exec where the post is the conjunction, because they
     can only feed one exec to other lemmas or IHs, so all clients will use the lemma below
     in combination with intersect_exec.
     So it makes more sense to directly prove the conjunction version which follows after
     this proof. *)
  Lemma modVarsSound_less_useful: forall e s t m l post,
      exec e s t m l post ->
      exec e s t m l (fun t' m' l' => map.only_differ l (modVars s) l').
  Proof.
    induction 1;
      try solve [ econstructor; [eassumption..|simpl; map_solver locals_ok] ].
    - eapply exec.if_true; try eassumption.
      eapply weaken_exec; [eassumption|].
      simpl; intros. map_solver locals_ok.
    - eapply exec.if_false; try eassumption.
      eapply weaken_exec; [eassumption|].
      simpl; intros. map_solver locals_ok.
    - eapply exec.seq with
          (mid0 := fun t' m' l' => mid t' m' l' /\ map.only_differ l (modVars c1) l').
      + eapply intersect_exec; eassumption.
      + simpl. intros *. intros [? ?].
        eapply weaken_exec; [eapply H1; eauto|].
        simpl; intros.
        map_solver locals_ok.
    - eapply exec.while_true with
          (mid0 := fun t' m' l' => mid t' m' l' /\ map.only_differ l (modVars c) l');
        try eassumption.
      + eapply intersect_exec; eassumption.
      + intros *. intros [? ?]. simpl in *.
        eapply weaken_exec.
        * eapply H3; eassumption.
        * simpl. intros. map_solver locals_ok.
    - eapply exec.call. 4: exact H2. (* don't pick IHexec! *) all: try eassumption.
      simpl. intros.
      edestruct H3 as (? & ? & ? & ? & ?); try eassumption.
      eexists; split; [eassumption|].
      eexists; split; [eassumption|].
      eapply map.only_differ_putmany. eassumption.
    - eapply exec.interact; try eassumption.
      intros.
      edestruct H2 as (? & ? & ?); try eassumption.
      destruct H5 as (? & ? & ?).
      eexists; split; [eassumption|].
      eexists; split; [eassumption|].
      eapply map.only_differ_putmany. eassumption.
  Qed.

  Lemma modVarsSound: forall e s t m l post,
      exec e s t m l post ->
      exec e s t m l (fun t' m' l' => map.only_differ l (modVars s) l' /\ post t' m' l').
  Proof.
    induction 1;
      try solve [econstructor; repeat split; try eassumption; simpl; map_solver locals_ok].
    - eapply exec.if_true; try eassumption.
      eapply weaken_exec; [eassumption|].
      simpl; intros. intuition idtac. map_solver locals_ok.
    - eapply exec.if_false; try eassumption.
      eapply weaken_exec; [eassumption|].
      simpl; intros. intuition idtac. map_solver locals_ok.
    - eapply exec.seq.
      + eapply IHexec.
      + simpl; intros *. intros [? ?].
        eapply weaken_exec; [eapply H1; eauto|].
        simpl; intros. intuition idtac. map_solver locals_ok.
    - eapply exec.while_true. 3: exact IHexec. all: try eassumption.
      intros *. intros [? ?]. simpl in *.
      eapply weaken_exec.
      + eapply H3; eassumption.
      + simpl. intros. intuition idtac. map_solver locals_ok.
    - eapply exec.call. 4: exact H2. (* don't pick IHexec! *) all: try eassumption.
      simpl. intros.
      edestruct H3 as (? & ? & ? & ? & ?); try eassumption.
      repeat (eexists || split || eassumption).
      eapply map.only_differ_putmany. eassumption.
    - eapply exec.interact; try eassumption.
      intros.
      edestruct H2 as (? & ? & ?); try eassumption.
      destruct H5 as (? & ? & ?).
      eexists; split; [eassumption|].
      eexists; split; [eassumption|].
      repeat (eexists || split || eassumption).
      eapply map.only_differ_putmany. eassumption.
  Qed.

End ExprImp2.

Goal True. idtac "End of ExprImp.v". Abort.
