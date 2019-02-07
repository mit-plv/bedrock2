Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.Program.Tactics.
Require Import lib.LibTacticsMin.
Require Import riscv.Utility.
Require Export bedrock2.Syntax.
Require Export bedrock2.Semantics.
Require Import coqutil.Macros.unique.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PropSet.
Require Import riscv.util.ListLib.


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
          'Some argvs <- option_all (List.map (eval_expr m st) args);
          'Some st0 <- map.putmany_of_list params argvs map.empty;
          'Some (st1, m') <- eval_cmd f st0 m fbody;
          'Some retvs <- option_all (List.map (map.get st1) rets);
          'Some st' <- map.putmany_of_list binds retvs st;
          Some (st', m')
        | cmd.interact _ _ _ => None (* unsupported *)
        end
      end.

    Fixpoint expr_size(e: expr): Z :=
      match e with
      | expr.literal _ => 8
      | expr.load _ e => expr_size e + 1
      | expr.var _ => 1
      | expr.op op e1 e2 => expr_size e1 + expr_size e2 + 2
      end.

    Lemma expr_size_pos: forall exp, expr_size exp > 0.
    Proof.
      induction exp; simpl; try omega.
    Qed.

    Fixpoint cmd_size(s: cmd): Z :=
      match s with
      | cmd.store _ a v => expr_size a + expr_size v + 1
      | cmd.set x e => expr_size e + 1
      | cmd.cond cond bThen bElse => expr_size cond + cmd_size bThen + cmd_size bElse + 1
      | cmd.while cond body => expr_size cond + cmd_size body + 1
      | cmd.seq s1 s2 => cmd_size s1 + cmd_size s2 + 1
      | cmd.skip | cmd.unset _ => 1
      | cmd.call binds f args =>
          Zlength binds + Zlength args + List.fold_right Z.add 0 (List.map expr_size args) + 1
      | cmd.interact _ _ exprs => fold_right (fun e res => res + expr_size e) 0 exprs
                                  + 7 (* randomly chosen max allowed number of instructions
                                         one interaction can be compiled to, TODO parametrize
                                         over this *)
      end.

    Lemma cmd_size_pos: forall s, cmd_size s > 0.
    Proof.
      induction s; simpl;
      repeat match goal with
      | e: expr |- _ => unique pose proof (expr_size_pos e)
      | l: list _ |- _ => unique pose proof (Zlength_nonneg l)
      end;
      try omega;
      induction args;
      simpl;
      rewrite? Zlength_nil in *;
      try omega;
      rewrite? Zlength_cons in *;
      repeat match goal with
      | e: expr |- _ => unique pose proof (expr_size_pos e)
      | l: list _ |- _ => unique pose proof (Zlength_nonneg l)
      | A: _ -> _, B: _ |- _ => specialize (A B)
      end;
      try omega.
    Qed.

    Local Ltac inversion_lemma :=
      intros;
      simpl in *;
      repeat (destruct_one_match_hyp; try discriminate);
      repeat match goal with
             | E: _ _ _ = true  |- _ => apply word.eqb_true  in E
             | E: _ _ _ = false |- _ => apply word.eqb_false in E
             end;
      inversionss;
      eauto 16.

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
        option_all (List.map (eval_expr m1 st) args) = Some argvs /\
        map.putmany_of_list params argvs map.empty = Some st0 /\
        eval_cmd f st0 m1 fbody = Some (st1, m') /\
        option_all (List.map (map.get st1) rets) = Some retvs /\
        map.putmany_of_list binds retvs st = Some st' /\
        p2 = (st', m').
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_interact : forall st m1 p2 f binds fname args,
      eval_cmd (S f) st m1 (cmd.interact binds fname args) = Some p2 ->
      False.
    Proof. inversion_lemma. Qed.

  End WithEnv.

  (* Returns a list to make it obvious that it's a finite set. *)
  Fixpoint allVars_expr(e: expr): list var :=
    match e with
    | expr.literal v => []
    | expr.var x => [x]
    | expr.load nbytes e => allVars_expr e
    | expr.op op e1 e2 => (allVars_expr e1) ++ (allVars_expr e2)
    end.

  Fixpoint allVars_cmd(s: cmd): list var :=
    match s with
    | cmd.store _ a e => (allVars_expr a) ++ (allVars_expr e)
    | cmd.set v e => v :: allVars_expr e
    | cmd.unset v => v :: nil
    | cmd.cond c s1 s2 => (allVars_expr c) ++ (allVars_cmd s1) ++ (allVars_cmd s2)
    | cmd.while c body => (allVars_expr c) ++ (allVars_cmd body)
    | cmd.seq s1 s2 => (allVars_cmd s1) ++ (allVars_cmd s2)
    | cmd.skip => []
    | cmd.call binds _ args => binds ++ List.fold_right (@List.app _) nil (List.map allVars_expr args)
    | cmd.interact binds _ args => binds ++ List.fold_right (@List.app _) nil (List.map allVars_expr args)
    end.

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

  Lemma modVars_subset_allVars: forall x s,
    x \in modVars s ->
    In x (allVars_cmd s).
  Proof.
    intros.
    induction s; simpl in *.
    - set_solver.
    - set_solver.
    - set_solver.
    - set_solver.
    - set_solver.
      + apply in_or_app. right. apply in_or_app. left. assumption.
      + apply in_or_app. right. apply in_or_app. right. assumption.
    - set_solver; apply in_or_app; auto.
    - apply in_or_app. right. auto.
    - generalize dependent binds; induction binds; intros H; cbn in *.
      + contradiction.
      + destruct H; auto.
    - generalize dependent binds; induction binds; intros H; cbn in *.
      + contradiction.
      + destruct H; auto.
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

  Lemma modVarsSound: forall (e: env) fuel s initialS initialM finalS finalM,
    eval_cmd e fuel initialS initialM s = Some (finalS, finalM) ->
    map.only_differ initialS (modVars s) finalS.
  Proof.
    induction fuel; introv Ev.
    - discriminate.
    - invert_eval_cmd; simpl in *; inversionss;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          simpl in IH';
          ensure_new IH'
      end;
      state_calc;
      refine (only_differ_putmany _ _ _ _ _ _); eassumption.
  Qed.

End ExprImp2.
