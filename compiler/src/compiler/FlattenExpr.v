Require Import coqutil.Word.Properties.
Require Import compiler.util.Common.
Require compiler.ExprImp.
Require compiler.FlatImp.
Require Import compiler.NameGen.
Require Import coqutil.Decidable.
Require Import coqutil.Word.Bitwidth.
Require Import bedrock2.Syntax.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.Semantics.
Require Import coqutil.Macros.unique.
Require Import Coq.Bool.Bool.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.Simp.
Require Import Coq.Program.Tactics.
Require Import coqutil.Datatypes.String.
Require Import compiler.FlattenExprDef.
Require Export coqutil.Word.SimplWordExpr.
Require Import coqutil.Map.MapEauto.

Open Scope Z_scope.

Section FlattenExpr1.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {word_ok: word.ok word}
          {locals: map.map String.string word}
          {mem: map.map word Byte.byte}
          {ExprImp_env: map.map string (list string * list string * cmd)}
          {FlatImp_env: map.map string (list string * list string * FlatImp.stmt string)}
          {ext_spec: ExtSpec}
          {NGstate: Type}
          {NG: NameGen String.string NGstate}
          {locals_ok: map.ok locals}
          {mem_ok: map.ok mem}
          {ExprImp_env_ok: map.ok ExprImp_env}
          {FlatImp_env_ok: map.ok FlatImp_env}
          {ext_spec_ok: ext_spec.ok ext_spec}.

  Ltac set_solver := set_solver_generic String.string.

  Local Arguments Z.add : simpl never.
  Local Arguments Z.mul : simpl never.

  Ltac specializes H :=
    match type of H with
    | ?P -> ?Q => let n := fresh in assert P as n; [|specialize (H n); specializes H]
    | forall (x: ?T), _ => let n := fresh x in evar (n: T);
                           specialize (H n); subst n; specializes H
    | _ => idtac
    end.

  (* We don't currently track code size, we just validate at the end that no immediates grew too big *)
  Lemma flattenExpr_size: forall e s oResVar resVar ngs ngs',
    flattenExpr ngs oResVar e = (s, resVar, ngs') ->
    0 <= FlatImp.stmt_size s <= ExprImp.expr_size e.
  Proof.
    induction e; intros; destruct oResVar; simpl in *; simp; simpl;
      repeat match goal with
             | IH: _, H: _ |- _ => specialize IH with (1 := H)
             | |- context [?x / 4] => unique pose proof (Z.div_pos x 4)
             end;
      try blia.
  Qed.

  Lemma flattenExprAsBoolExpr_size: forall e s bcond ngs ngs',
      flattenExprAsBoolExpr ngs e = (s, bcond, ngs') ->
      0 <= FlatImp.stmt_size s <= ExprImp.expr_size e.
  Proof.
    induction e; intros; simpl in *; repeat destruct_one_match_hyp;
      simp; subst; simpl;
      repeat match goal with
      | H : _ |- _ => apply flattenExpr_size in H
      | |- context [?x / 4] => unique pose proof (Z.div_pos x 4)
      end; try blia.
  Qed.

  Lemma flattenExprs_size: forall es s resVars ngs ngs',
    flattenExprs ngs es = (s, resVars, ngs') ->
    0 <= FlatImp.stmt_size s <= ExprImp.exprs_size es.
  Proof.
    induction es; intros; simpl in *; simp; simpl; try blia.
    specialize IHes with (1 := E0).
    apply flattenExpr_size in E.
    blia.
  Qed.

  Lemma flattenExprs_resVarsLength: forall es s resVars ngs ngs',
    flattenExprs ngs es = (s, resVars, ngs') ->
    List.length resVars = List.length es.
  Proof.
    induction es; intros; simpl in *; simp; simpl; try blia.
    specialize IHes with (1 := E0).
    f_equal.
    assumption.
  Qed.

  Lemma flattenCall_size: forall f args binds ngs ngs' s,
      flattenCall ngs binds f args = (s, ngs') ->
      0 < FlatImp.stmt_size s <= ExprImp.cmd_size (Syntax.cmd.call binds f args).
  Proof.
    intros. unfold flattenCall in *.
    destruct_one_match_hyp.
    destruct_one_match_hyp.
    simp. simpl.
    pose proof E as E'.
    apply flattenExprs_size in E.
    apply flattenExprs_resVarsLength in E'.
    blia.
  Qed.

  Lemma flattenInteract_size: forall f args binds ngs ngs' s,
      flattenInteract ngs binds f args = (s, ngs') ->
      0 <= FlatImp.stmt_size s <= ExprImp.cmd_size (Syntax.cmd.interact binds f args).
  Proof.
    intros. unfold flattenInteract in *.
    destruct_one_match_hyp.
    destruct_one_match_hyp.
    simp. simpl.
    apply flattenExprs_size in E.
    blia.
  Qed.

  Lemma flattenStmt_size: forall s s' ngs ngs',
    flattenStmt ngs s = (s', ngs') ->
    0 <= FlatImp.stmt_size s' <= ExprImp.cmd_size s.
  Proof.
    induction s; intros; simpl in *; repeat destruct_one_match_hyp; simp; subst; simpl;
    repeat match goal with
    | IH: _, A: _ |- _ => specialize IH with (1 := A)
    end;
    repeat match goal with
    | H: flattenExpr _ _ _ = _ |- _ => apply flattenExpr_size in H
    | H: flattenExprAsBoolExpr _ _ = _ |- _ => apply flattenExprAsBoolExpr_size in H
    | H: flattenCall _ _ _ _ = _ |- _ => apply flattenCall_size in H
    | H: flattenInteract _ _ _ _ = _ |- _ => apply flattenInteract_size in H
    end;
    simpl in *;
    try blia.
  Qed.

  Lemma flattenExpr_freshVarUsage: forall e ngs ngs' oResVar s v,
    flattenExpr ngs oResVar e = (s, v, ngs') ->
    subset (allFreshVars ngs') (allFreshVars ngs).
  Proof.
    induction e; intros; destruct oResVar;
      repeat (simpl in *; simp; subst; try destruct_one_match_hyp);
    repeat match goal with
    | H: _ |- _ => apply genFresh_spec in H
    end;
    repeat match goal with
    | IH: forall _ _ _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    set_solver.
  Qed.

  Lemma flattenExprs_freshVarUsage: forall es ngs ngs' s vs,
    flattenExprs ngs es = (s, vs, ngs') ->
    subset (allFreshVars ngs') (allFreshVars ngs).
  Proof.
    induction es; intros; simpl in *; simp; [ set_solver |].
    specialize IHes with (1 := E0).
    eapply flattenExpr_freshVarUsage in E.
    set_solver.
  Qed.

  Lemma flattenExprAsBoolExpr_freshVarUsage: forall e ngs ngs' s v,
    flattenExprAsBoolExpr ngs e = (s, v, ngs') ->
    subset (allFreshVars ngs') (allFreshVars ngs).
  Proof.
    induction e; intros; simpl in *; repeat (destruct_one_match_hyp);
      repeat match goal with
             | H: (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
             | H : genFresh _ = _      |- _ => apply genFresh_spec in H
             | H : flattenExpr _ _ _ = _ |- _ => apply flattenExpr_freshVarUsage in H
    end;
    repeat match goal with
    | IH: forall _ _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    set_solver.
  Qed.

  Lemma flattenExpr_uses_Some_resVar: forall e s resVar1 resVar2 ngs ngs',
      flattenExpr ngs (Some resVar1) e = (s, resVar2, ngs') ->
      resVar2 = resVar1.
  Proof.
    induction e; intros; simpl in *; simp; reflexivity.
  Qed.

  Lemma flattenExpr_valid_resVar: forall e s oResVar ngs ngs' resVar,
      flattenExpr ngs oResVar e = (s, resVar, ngs') ->
      disjoint (union (ExprImp.allVars_expr e) (of_option oResVar)) (allFreshVars ngs) ->
      ~ resVar \in (allFreshVars ngs').
  Proof.
    destruct e; intros; destruct oResVar; simp; simpl in *; simp;
      repeat match goal with
          | H: _ |- _ => apply genFresh_spec in H; simp
          | H: flattenExpr _ _ _ = _ |- _ => apply flattenExpr_freshVarUsage in H
          end;
      try assumption;
      try solve [set_solver].
  Qed.

  Lemma flattenExpr_modVars_spec: forall e oResVar s ngs ngs' resVar,
    flattenExpr ngs oResVar e = (s, resVar, ngs') ->
    subset (FlatImp.modVars s) (union (of_option oResVar )
                                      (diff (allFreshVars ngs) (allFreshVars ngs'))).
  Proof.
    induction e; intros; destruct oResVar; simpl in *; repeat destruct_one_match_hyp;
    simpl;
    repeat match goal with
    | IH: forall _ _ _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    repeat match goal with
             | H: (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
             | H: genFresh _ = _      |- _ => apply genFresh_spec in H
             | H: flattenExpr _ _ _ = _ |- _ => apply flattenExpr_freshVarUsage in H
             | |- _ => progress simpl in *
    end;
    try solve [set_solver].
  Qed.

  Lemma flattenExprs_modVars_spec: forall es s ngs ngs' resVars,
    flattenExprs ngs es = (s, resVars, ngs') ->
    subset (FlatImp.modVars s) (diff (allFreshVars ngs) (allFreshVars ngs')).
  Proof.
    induction es; intros; simpl in *; simp; simpl; [set_solver|].
    repeat match goal with
    | IH: forall _ _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    repeat match goal with
    | H: genFresh _ = _ |- _ => apply genFresh_spec in H
    | H: flattenExpr _ _ _ = _ |- _ =>
      unique eapply flattenExpr_freshVarUsage in copy of H;
      unique eapply flattenExpr_modVars_spec in copy of H
    | H: flattenExprs _ _ = _ |- _ =>
      unique eapply flattenExprs_freshVarUsage in copy of H
    | H: (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
    | |- _ => progress simpl in *
    end;
    try solve [set_solver].
  Qed.

  Lemma flattenExprAsBoolExpr_modVars_spec: forall e s ngs ngs' cond,
    flattenExprAsBoolExpr ngs e = (s, cond, ngs') ->
    subset (FlatImp.modVars s) (diff (allFreshVars ngs) (allFreshVars ngs')).
  Proof.
    induction e; intros; simpl in *; repeat destruct_one_match_hyp;
    simpl;
    repeat match goal with
    | IH: forall _ _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    repeat match goal with
    | H: genFresh _ = _ |- _ => apply genFresh_spec in H
    | H: flattenExpr _ _ _ = _ |- _ =>
      unique eapply flattenExpr_freshVarUsage in copy of H;
      unique eapply flattenExpr_modVars_spec in copy of H
    | H: (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
    | |- _ => progress simpl in *
    end;
    try solve [set_solver].
  Qed.

  Lemma flattenStmt_modVars_spec: forall s ngs ngs' s',
      flattenStmt ngs s = (s', ngs') ->
      subset (FlatImp.modVars s') (union (ExprImp.modVars s)
                                         (diff (allFreshVars ngs) (allFreshVars ngs'))).
  Abort. (* hopefully not needed *)

  Lemma flattenCall_freshVarUsage: forall f args binds ngs1 ngs2 s,
      flattenCall ngs1 binds f args = (s, ngs2) ->
      subset (allFreshVars ngs2) (allFreshVars ngs1).
  Proof.
    unfold flattenCall.
    intros. simp. eauto using flattenExprs_freshVarUsage.
  Qed.

  Lemma flattenInteract_freshVarUsage: forall args s' binds a ngs1 ngs2,
      flattenInteract ngs1 binds a args = (s', ngs2) ->
      subset (allFreshVars ngs2) (allFreshVars ngs1).
  Proof.
    unfold flattenInteract.
    intros. simp. eauto using flattenExprs_freshVarUsage.
  Qed.

  Lemma flattenStmt_freshVarUsage: forall s s' ngs1 ngs2,
    flattenStmt ngs1 s = (s', ngs2) ->
    subset (allFreshVars ngs2) (allFreshVars ngs1).
  Proof.
    induction s; intros; simpl in *; repeat (destruct_one_match_hyp);
    repeat match goal with
    | H: _ |- _ => apply genFresh_spec in H
    | H: _ |- _ => apply flattenExpr_freshVarUsage in H
    | H: _ |- _ => apply flattenExprAsBoolExpr_freshVarUsage in H
    | H: _ |- _ => apply flattenInteract_freshVarUsage in H
    | H: _ |- _ => apply flattenCall_freshVarUsage in H
    | H: (_, _) = (_, _) |- _ => inversion H; subst; clear H
    end;
    repeat match goal with
    | IH: forall _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    try solve [set_solver].
  Qed.

  Ltac pose_flatten_var_ineqs :=
    repeat match goal with
    (* fresh var usage: new fresh vars are a subset of old fresh vars: *)
    | H: _ |- _ => unique eapply flattenExpr_freshVarUsage in copy of H
    | H: _ |- _ => unique eapply flattenExprs_freshVarUsage in copy of H
    | H: _ |- _ => unique eapply flattenExprAsBoolExpr_freshVarUsage in copy of H
    | H: _ |- _ => unique eapply flattenStmt_freshVarUsage in copy of H
    (* a flattened statement only modifies vars obtained from the fresh var generator: *)
    | H: _ |- _ => unique eapply flattenExpr_modVars_spec in copy of H
    | H: _ |- _ => unique eapply flattenExprs_modVars_spec in copy of H
    | H: _ |- _ => unique eapply flattenExprAsBoolExpr_modVars_spec in copy of H
    (* resVar returned by flattenExpr is not in the new fresh vars
       This one has an additional disjointness hyp, so if we pose this, we have a hyp of the
       form "(forall x, _) -> _", which is not supported by the map_solver, so we
       pose it manually
    | H: flattenExpr _ _ _ = _ |- _ => unique pose proof (flattenExpr_valid_resVar _ _ _ _ _ _ H)
    *)
    end.

  Arguments map.empty: simpl never.

  (* only instantiates evars when it's sure to make the correct choice *)
  Ltac t_safe :=
    repeat match goal with
    | |- _ /\ _ => split
    | |- _ => solve [auto]
    | |- map.get (map.put _ ?x _) ?y = Some _ =>
      (* might instantiate the value, but this choice is definitely correct *)
      constr_eq x y; apply map.get_put_same
    end.

  Ltac maps :=
    pose_flatten_var_ineqs;
    simpl (disjoint _ _) in *;
    map_solver locals_ok.

  Lemma seq_with_modVars: forall env t m (l: locals) mc s1 s2 mid post,
    FlatImp.exec env s1 t m l mc mid ->
    (forall t' m' l' mc',
        mid t' m' l' mc' ->
        map.only_differ l (FlatImp.modVars s1) l' ->
        FlatImp.exec env s2 t' m' l' mc' post) ->
    FlatImp.exec env (FlatImp.SSeq s1 s2) t m l mc post.
  Proof.
    intros *. intros E1 E2. eapply @FlatImp.exec.seq.
    - eapply FlatImp.exec.intersect.
      + exact E1.
      + eapply FlatImp.modVarsSound; try typeclasses eauto. exact E1.
    - simpl. intros. simp. eauto.
  Qed.

  (* eauto doesn't see through RelationClasses.Transitive *)
  Lemma subset_transitive[E: Type]: forall a b c: set E,
      subset a b -> subset b c -> subset a c.
  Proof. apply subset_trans. Qed.

  Goal True. idtac "FlattenExpr: Entering slow lemmas section". Abort.

  Lemma flattenExpr_correct_aux : forall e fenv oResVar ngs1 ngs2 resVar s initialH initialL initialM initialMcH initialMcL finalMcH res t,
    flattenExpr ngs1 oResVar e = (s, resVar, ngs2) ->
    map.extends initialL initialH ->
    map.undef_on initialH (allFreshVars ngs1) ->
    disjoint (union (ExprImp.allVars_expr e) (of_option oResVar)) (allFreshVars ngs1) ->
    eval_expr initialM initialH e initialMcH = Some (res, finalMcH) ->
    FlatImp.exec fenv s t initialM initialL initialMcL (fun t' finalM finalL finalMcL =>
      t' = t /\ finalM = initialM /\ map.get finalL resVar = Some res /\
      (finalMcL - initialMcL <= finalMcH - initialMcH)%metricsH).
  Proof.
    induction e; intros *; intros F Ex U D Ev; simpl in *; simp.

    - (* expr.literal *)
      eapply @FlatImp.exec.lit; t_safe; solve_MetricLog.

    - (* expr.var *)
      destruct oResVar; simp.
      + eapply @FlatImp.exec.set; t_safe; [maps | solve_MetricLog].
      + eapply @FlatImp.exec.skip; t_safe. solve_MetricLog.

    - (* expr.load *)
      eapply @FlatImp.exec.seq.
      + eapply IHe; try eassumption. maps.
      + intros. simpl in *. simp.
        eapply @FlatImp.exec.load; t_safe; rewrite ?add_0_r; try eassumption; solve_MetricLog.

    - (* expr.inlinetable *)
      repeat match goal with
             | H: genFresh _ = _ |- _ => unique pose proof (genFresh_spec _ _ _ H)
             end.
      simp.
      eapply @FlatImp.exec.seq.
      + eapply IHe; try eassumption. 1: maps.
        set_solver; destr (String.eqb s0 x); subst; tauto. (* TODO improve set_solver? *)
      + intros. simpl in *. simp.
        eapply @FlatImp.exec.inlinetable; t_safe; try eassumption. 2: solve_MetricLog.
        apply_in_hyps flattenExpr_uses_Some_resVar. subst s0.
        intro C. subst s2.
        destruct oResVar.
        * cbn in *. simp. set_solver.
        * cbn in *. apply_in_hyps genFresh_spec. simp. pose_flatten_var_ineqs. set_solver.

    - (* expr.op *)
      eapply seq_with_modVars.
      + eapply IHe1. 1: eassumption. 4: eassumption. 1,2: eassumption.
        clear -D. set_solver.
      + intros. simpl in *. simp.
        eapply seq_with_modVars.
        * eapply IHe2. 1: eassumption. 4: eassumption. 1,2: solve [maps].
          clear IHe1 IHe2. pose_flatten_var_ineqs. set_solver.
        * intros. simpl in *. simp. clear IHe1 IHe2.
          eapply @FlatImp.exec.op; t_safe; t_safe. 2 : solve_MetricLog.
          eapply flattenExpr_valid_resVar in E1; maps.

    - (* expr.ite *)
      eapply seq_with_modVars.
      + eapply IHe1. 1: eassumption. 4: eassumption. 1,2: eassumption.
        clear -D. set_solver.
      + simpl. intros. simp.
        pose proof flattenExpr_valid_resVar as A.
        specialize A with (1 := E0). cbn [of_option] in *.
        destruct_one_match_hyp.
        * eapply FlatImp.exec.if_false.
          -- simpl. rewrite_match. rewrite word.eqb_eq; reflexivity.
          -- eapply FlatImp.exec.weaken.
             ++ eapply IHe3; clear IHe1 IHe2 IHe3. 1: eassumption. 4: eassumption.
                ** solve [maps].
                ** unfold genFresh_if_needed in *.
                   destruct oResVar; simp; pose_flatten_var_ineqs; cbn[of_option] in *.
                   { solve[maps]. }
                   { apply_in_hyps genFresh_spec. solve[maps]. }
                ** unfold genFresh_if_needed in *.
                   destruct oResVar; simp; pose_flatten_var_ineqs; cbn[of_option] in *.
                   { set_solver. }
                   { apply_in_hyps genFresh_spec. simp.
                     eapply disjoint_union_l_iff.
                     split. 2: {
                       assert (~ resVar \in (allFreshVars n1)) as HA by set_solver.
                       unfold disjoint. intro k.
                       (* TODO set_solver should do this case analysis *)
                       destr (String.eqb k resVar); auto.
                     }
                     move D at bottom.
                     assert (subset (allFreshVars n1) (allFreshVars ngs1)) as Sub1. {
                         eauto using subset_transitive.
                     }
                     eapply subset_disjoint_r. 1: exact Sub1.
                     eapply subset_disjoint_l. 2: exact D.
                     eapply subset_union_rl.
                     eapply subset_union_rr.
                     eapply subset_union_rr.
                     eapply subset_refl.
                   }
             ++ cbv beta. intros. simp. t_safe. 2: solve_MetricLog.
                clear IHe1 IHe2 IHe3.
                apply_in_hyps flattenExpr_uses_Some_resVar. subst. assumption.
        * eapply FlatImp.exec.if_true.
          -- simpl. rewrite_match. rewrite word.eqb_ne; cbn; congruence.
          -- eapply FlatImp.exec.weaken.
             ++ eapply IHe2; clear IHe1 IHe2 IHe3. 1: eassumption. 4: eassumption.
                ** solve [maps].
                ** unfold genFresh_if_needed in *.
                   destruct oResVar; simp; pose_flatten_var_ineqs; cbn[of_option] in *.
                   { solve[maps]. }
                   { apply_in_hyps genFresh_spec. solve[maps]. }
                ** unfold genFresh_if_needed in *.
                   destruct oResVar; simp; pose_flatten_var_ineqs; cbn[of_option] in *.
                   { set_solver. }
                   { apply_in_hyps genFresh_spec. simp.
                     eapply disjoint_union_l_iff.
                     split. 2: {
                       assert (~ resVar \in (allFreshVars n1)) as HA by set_solver.
                       unfold disjoint. intro k.
                       (* TODO set_solver should do this case analysis *)
                       destr (String.eqb k resVar); auto.
                     }
                     move D at bottom.
                     assert (subset (allFreshVars n0) (allFreshVars ngs1)) as Sub1. {
                         eauto using subset_transitive.
                     }
                     eapply subset_disjoint_r. 1: exact Sub1.
                     eapply subset_disjoint_l. 2: exact D.
                     eapply subset_union_rl.
                     eapply subset_union_rr.
                     eapply subset_union_rl.
                     eapply subset_refl.
                   }
             ++ cbv beta. intros. simp. t_safe. 2: solve_MetricLog.
                clear IHe1 IHe2 IHe3.
                apply_in_hyps flattenExpr_uses_Some_resVar. subst. assumption.
  Qed.
  Goal True. idtac "FlattenExpr: flattenExpr_correct_aux done". Abort.

  Lemma flattenExpr_correct_with_modVars : forall e fenv oResVar ngs1 ngs2 resVar s t m lH lL initialMcH initialMcL finalMcH res,
    flattenExpr ngs1 oResVar e = (s, resVar, ngs2) ->
    map.extends lL lH ->
    map.undef_on lH (allFreshVars ngs1) ->
    disjoint (union (ExprImp.allVars_expr e) (of_option oResVar)) (allFreshVars ngs1) ->
    eval_expr m lH e initialMcH = Some (res, finalMcH) ->
    FlatImp.exec fenv s t m lL initialMcL (fun t' m' lL' finalMcL =>
      map.only_differ lL (FlatImp.modVars s) lL' /\
      t' = t /\ m' = m /\ map.get lL' resVar = Some res /\
      (finalMcL - initialMcL <= finalMcH - initialMcH)%metricsH).
  Proof.
    intros *. intros F Ex U D Ev.
    epose proof (flattenExpr_correct_aux _ _ _ _ _ _ _ _ _ _ _ _ _ _ _ F Ex U D Ev) as P.
    eapply FlatImp.exec.intersect; cycle 1.
    - exact P.
    - rapply FlatImp.modVarsSound. exact P.
  Qed.

  Lemma flattenExprs_correct: forall es fenv ngs1 ngs2 resVars s t m lH lL initialMcH initialMcL finalMcH resVals,
    flattenExprs ngs1 es = (s, resVars, ngs2) ->
    map.extends lL lH ->
    map.undef_on lH (allFreshVars ngs1) ->
    disjoint (ExprImp.allVars_exprs es) (allFreshVars ngs1) ->
    evaluate_call_args_log m lH es initialMcH = Some (resVals, finalMcH) ->
    (* List.option_all (List.map (eval_expr m lH) es) = Some resVals -> *)
    FlatImp.exec fenv s t m lL initialMcL (fun t' m' lL' finalMcL =>
      t' = t /\ m' = m /\
      map.getmany_of_list lL' resVars = Some resVals /\
      map.only_differ lL (FlatImp.modVars s) lL' /\
      (finalMcL - initialMcL <= finalMcH - initialMcH)%metricsH).
  Proof.
    induction es; intros *; intros F Ex U D Evs; simpl in *; simp;
      [ eapply @FlatImp.exec.skip; simpl; repeat split; try solve_MetricLog; auto; maps | ].
    rename n into ngs2, ngs2 into ngs3.
    eapply seq_with_modVars.
    - eapply flattenExpr_correct_aux; try eassumption.
      clear -D.
      unfold ExprImp.allVars_exprs in D.
      simpl in *.
      set_solver.
    - intros. simpl in *. simp.
      assert (disjoint (ExprImp.allVars_exprs es) (allFreshVars ngs2)). {
        unfold ExprImp.allVars_exprs in D.
        simpl in *.
        pose_flatten_var_ineqs.
        set_solver.
      }
      eapply @FlatImp.exec.weaken.
      + eapply IHes; try eassumption; maps.
      + intros. simpl in *. simp. cbn. unfold map.getmany_of_list in *.
        replace (map.get l'0 s1) with (Some r).
        * rewrite_match. repeat (split || auto); try solve_MetricLog. maps.
        * unfold ExprImp.allVars_exprs in D.
          eapply flattenExpr_valid_resVar in E1; maps.
  Qed.
  Goal True. idtac "FlattenExpr: flattenExprs_correct done". Abort.

  Lemma unsigned_ne: forall (a b: word), word.unsigned a <> word.unsigned b -> a <> b.
  Proof.
    intros.
    intro C.
    subst b.
    apply H.
    reflexivity.
  Qed.

  Lemma one_ne_zero: word.of_Z 1 <> word.of_Z 0 :> word.
  Proof.
    apply unsigned_ne.
    rewrite! word.unsigned_of_Z. unfold word.wrap.
    pose proof word.width_pos as P; pose proof (Z.pow_gt_1 2 width) as Q.
    rewrite! Z.mod_small; blia.
  Qed.

  Local Hint Mode Word.Interface.word - : typeclass_instances.

  Lemma bool_to_word_to_bool_id: forall (b: bool),
      negb (word.eqb (if b then word.of_Z 1 else word.of_Z 0) (word.of_Z 0)) = b.
  Proof.
    intro b. unfold negb.
    destruct_one_match; destruct_one_match_hyp; try reflexivity.
    - exfalso. apply one_ne_zero. assumption.
    - congruence.
  Qed.

  Ltac default_flattenBooleanExpr :=
    eapply FlatImp.exec.weaken;
    [ eapply flattenExpr_correct_with_modVars; try eassumption; try reflexivity;
      try solve [maps]
    | intros; simpl in *; simp; repeat rewrite_match; t_safe ].

  Lemma flattenBooleanExpr_correct_aux :
    forall e fenv ngs1 ngs2 resCond (s: FlatImp.stmt string) (initialH initialL: locals) initialM t initialMcH initialMcL finalMcH res,
    flattenExprAsBoolExpr ngs1 e = (s, resCond, ngs2) ->
    map.extends initialL initialH ->
    map.undef_on initialH (allFreshVars ngs1) ->
    disjoint (ExprImp.allVars_expr e) (allFreshVars ngs1) ->
    eval_expr initialM initialH e initialMcH = Some (res, finalMcH) ->
    FlatImp.exec fenv s t initialM initialL initialMcL (fun t' finalM finalL finalMcL =>
      t' = t /\ finalM = initialM /\
      FlatImp.eval_bcond finalL resCond = Some (negb (word.eqb res (word.of_Z 0))) /\
      (finalMcL - initialMcL <= finalMcH - initialMcH)%metricsH).
  Proof.
    destruct e; intros *; intros F Ex U D Ev; unfold flattenExprAsBoolExpr in F.

    1, 2, 3, 4, 6: solve [simp; default_flattenBooleanExpr].

    simp.
    pose proof E  as N1. eapply flattenExpr_valid_resVar in N1; [|maps].
    pose proof E0 as N2. eapply flattenExpr_valid_resVar in N2; [|maps].

    destruct op; simp; try solve [default_flattenBooleanExpr].

    all: simpl in *; simp;
      eapply seq_with_modVars;
      [ eapply flattenExpr_correct_with_modVars; try eassumption; try reflexivity; try solve [maps]
      | intros; simpl in *; simp;
        default_flattenBooleanExpr ].

    2, 4, 6 : solve_MetricLog.

    all: rewrite bool_to_word_to_bool_id;
      destruct_one_match;
      [ f_equal; f_equal; maps
      | exfalso; maps ].
  Qed.
  Goal True. idtac "FlattenExpr: flattenBooleanExpr_correct_aux done". Abort.

  Lemma flattenBooleanExpr_correct_with_modVars:
    forall e fenv ngs1 ngs2 resCond (s: FlatImp.stmt string) (initialH initialL: locals) initialM t initialMcH initialMcL finalMcH res,
    flattenExprAsBoolExpr ngs1 e = (s, resCond, ngs2) ->
    map.extends initialL initialH ->
    map.undef_on initialH (allFreshVars ngs1) ->
    disjoint (ExprImp.allVars_expr e) (allFreshVars ngs1) ->
    eval_expr initialM initialH e initialMcH = Some (res, finalMcH) ->
    FlatImp.exec fenv s t initialM initialL initialMcL (fun t' finalM finalL finalMcL =>
      (t' = t /\ finalM = initialM /\
       FlatImp.eval_bcond finalL resCond = Some (negb (word.eqb res (word.of_Z 0))) /\
       (finalMcL - initialMcL <= finalMcH - initialMcH)%metricsH) /\
       map.only_differ initialL (FlatImp.modVars s) finalL (* <-- added *)).
  Proof.
    intros. eapply FlatImp.exec.intersect.
    - eapply flattenBooleanExpr_correct_aux; eassumption.
    - rapply FlatImp.modVarsSound.
      eapply flattenBooleanExpr_correct_aux; eassumption.
  Qed.

  Lemma freshNameGenState_disjoint: forall (sH: cmd),
    disjoint (ExprImp.allVars_cmd sH)
             (allFreshVars (@freshNameGenState _ NGstate NG (ExprImp.allVars_cmd_as_list sH))).
  Proof.
    unfold disjoint. intros.
    pose proof (freshNameGenState_spec (ExprImp.allVars_cmd_as_list sH) x) as P.
    match type of P with
    | In ?x ?l -> _ => edestruct (in_dec String.string_dec x l) as [Iyes | Ino]
    end.
    + auto.
    + left. clear -Ino.
      intro. apply Ino.
      epose proof (ExprImp.allVars_cmd_allVars_cmd_as_list _ _) as P. destruct P as [P _].
      apply P.
      apply H.
  Qed.

  Lemma freshNameGenState_disjoint_fbody: forall (fbody: cmd) (params rets: list String.string),
    disjoint (ExprImp.allVars_cmd fbody)
             (allFreshVars (@freshNameGenState _ NGstate NG
                  (ListSet.list_union String.eqb (ListSet.list_union String.eqb params rets)
                                                 (ExprImp.allVars_cmd_as_list fbody)))).
  Proof.
    unfold disjoint. intros.
    epose proof (freshNameGenState_spec _ x) as P.
    match type of P with
    | In ?x ?l -> _ => edestruct (in_dec String.string_dec x l) as [Iyes | Ino]
    end.
    + right. apply P. assumption.
    + left. clear P.
      intro. apply Ino.
      epose proof (ExprImp.allVars_cmd_allVars_cmd_as_list _ _) as P. destruct P as [P _].
      eauto using ListSet.In_list_union_l, ListSet.In_list_union_r, nth_error_In.
  Qed.

  Lemma flattenStmt_correct_aux: forall eH eL,
      flatten_functions eH = Success eL ->
      forall eH0 sH t m mcH lH post,
      Semantics.exec eH0 sH t m lH mcH post ->
      eH0 = eH ->
      forall ngs ngs' sL lL mcL,
      flattenStmt ngs sH = (sL, ngs') ->
      map.extends lL lH ->
      map.undef_on lH (allFreshVars ngs) ->
      disjoint (ExprImp.allVars_cmd sH) (allFreshVars ngs) ->
      FlatImp.exec eL sL t m lL mcL (fun t' m' lL' mcL' => exists lH' mcH',
        post t' m' lH' mcH' /\ (* <-- put first so that eassumption will instantiate lH' correctly *)
        map.extends lL' lH' /\
        (* this one is a property purely about ExprImp (it's the conclusion of
           ExprImp.modVarsSound). In the previous proof, which was by induction
           on the fuel of the ExprImp execution, we did not need to carry it
           around in the IH, but could just apply ExprImp.modVarsSound as needed,
           (eg after the when proving the second part of a (SSeq s1 s2)), but
           now we have to make it part of the conclusion in order to get a stronger
           "mid" in that case, because once we're at s2, it's too late to learn/prove
           more things about the (t', m', l') in mid *)
        map.only_differ lH (ExprImp.modVars sH) lH' /\
        (mcL' - mcL <= mcH' - mcH)%metricsH).
  Proof.
    induction 2; intros; simpl in *; subst; simp.

    - (* exec.skip *)
      eapply @FlatImp.exec.skip.
      eexists; eexists; repeat (split || eassumption || solve_MetricLog). maps.

    - (* exec.set *)
      eapply @FlatImp.exec.weaken.
      + eapply @flattenExpr_correct_with_modVars; try eassumption. maps.
      + simpl. intros. simp.
        repeat eexists; repeat split.
        * eassumption.
        * pose proof flattenExpr_uses_Some_resVar as P.
          specialize P with (1 := E). subst.
          maps.
        * maps.
        * solve_MetricLog.
        * solve_MetricLog.
        * solve_MetricLog.
        * solve_MetricLog.

    - (* exec.unset *)
      eapply @FlatImp.exec.skip.
      repeat eexists; repeat (split || eassumption || solve_MetricLog); maps.

    - (* exec.store *)
      eapply @FlatImp.exec.seq.
      + eapply flattenExpr_correct_with_modVars; try eassumption. maps.
      + intros. simpl in *. simp.
        eapply @FlatImp.exec.seq.
        * eapply flattenExpr_correct_with_modVars; try eassumption; maps.
        * intros. simpl in *. simp.
          eapply @FlatImp.exec.store; rewrite ?add_0_r; try eassumption.
          { eapply flattenExpr_valid_resVar in E; maps. }
          { repeat eexists; repeat (split || eassumption || solve_MetricLog); maps. }

    - (* exec.stackalloc *)
      eapply @FlatImp.exec.stackalloc. 1: eassumption.
      intros. rename H2 into IHexec.
      eapply @FlatImp.exec.weaken.
      { eapply IHexec; try reflexivity; try eassumption; maps. }
      { intros. simpl in *. simp. do 2 eexists. ssplit; try eassumption.
        do 2 eexists. ssplit; try eassumption; try solve_MetricLog. maps. }

    - (* if_true *)
      eapply @FlatImp.exec.seq.
      + eapply flattenBooleanExpr_correct_with_modVars; try eassumption. maps.
      + intros. simpl in *. simp.
        eapply @FlatImp.exec.if_true.
        * etransitivity. 1: eassumption. f_equal.
          rewrite word.eqb_ne; [reflexivity|].
          apply unsigned_ne.
          rewrite word.unsigned_of_Z.
          assumption.
        * (* including "map.only_differ lH (ExprImp.modVars sH) lH'" in the conclusion
             requires us to do one more weakening step here than otherwise needed: *)
          eapply @FlatImp.exec.weaken.
          { eapply IHexec; try reflexivity; try eassumption; maps. }
          { intros. simpl in *. simp.
            repeat eexists; repeat (split || eassumption || solve_MetricLog). maps. }

    - (* if_false *)
      eapply @FlatImp.exec.seq.
      + eapply flattenBooleanExpr_correct_with_modVars; try eassumption. maps.
      + intros. simpl in *. simp.
        eapply @FlatImp.exec.if_false.
        * etransitivity. 1: eassumption. f_equal.
          rewrite word.eqb_eq; [reflexivity|].
          apply word.unsigned_inj.
          rewrite word.unsigned_of_Z.
          assumption.
        * (* including "map.only_differ lH (ExprImp.modVars sH) lH'" in the conclusion
             requires us to do one more weakening step here than otherwise needed: *)
          eapply @FlatImp.exec.weaken.
          { eapply IHexec; try reflexivity; try eassumption; maps. }
          { intros. simpl in *. simp.
            repeat eexists; repeat (split || eassumption || solve_MetricLog). maps. }

    - (* seq *)
      eapply seq_with_modVars.
      + eapply IHexec; try reflexivity; try eassumption. maps.
      + simpl. intros. simp.
        rename l into lH, l' into lL'.
        (* NOTE how the new high-level locals (lH') are not only constrained by mid and
           by "map.extends lL' lH'" but also by the additional
           "map.only_differ lH (ExprImp.modVars c1) lH'".
           This additional constraint is not related to the flattening at all, but we still
           have to carry it in the conclusion of the statement in order to get it here *)
        rename H2 into IHexec2.
        (* including "map.only_differ lH (ExprImp.modVars sH) lH'" in the conclusion
           requires us to do one more weakening step here than otherwise needed: *)
        eapply @FlatImp.exec.weaken.
        * eapply IHexec2; try reflexivity; try eassumption.
          { pose proof (ExprImp.modVars_subset_allVars c1).
            (* note: here we need the high-level map.only_differ we were carrying around *)
            (* Fail (solve [clear H9; maps]). *)
            solve [maps]. }
          { maps. }
        * clear IHexec IHexec2.
          simpl. intros. simp.
          repeat eexists; repeat (split || eassumption || solve_MetricLog); maps.

    - (* while_false *)
      eapply @FlatImp.exec.loop;
        [ eapply flattenBooleanExpr_correct_with_modVars; try eassumption
        | intros; simpl in *; simp .. ].
      + maps.
      + congruence.
      + repeat eexists; repeat (split || eassumption || solve_MetricLog); maps.
      + exfalso.
        match goal with
        | H: context [word.eqb _ _] |- _ => rewrite word.eqb_eq in H
        end.
        1: simpl in *; congruence.
        apply word.unsigned_inj. rewrite word.unsigned_of_Z. assumption.
      + exfalso. exact H3. (* instantiates mid2 to (fun _ _ _ => False) *)

    - (* while_true *)
      (* We instantiate mid2 here to quanitfy the bound over both the loop body
         and the expression to avoid issues later. This is a modified version of the
         postcondition offered by IHexec - the metric differences are now between the
         start and end of the loop rather than after the expression execution and the end
         of the loop *)
      eapply @FlatImp.exec.loop with (mid2 := (fun t' m' lL' mcL' => exists lH' mcH',
        mid t' m' lH' mcH' /\
        map.extends lL' lH' /\
        map.only_differ l (ExprImp.modVars c) lH' /\
        (mcL' - mcL <= mcH' - mc)%metricsH));
        [ eapply flattenBooleanExpr_correct_with_modVars; try eassumption
        | intros; simpl in *; simp .. ].
      + maps.
      + congruence.
      + exfalso.
        match goal with
        | H: context [word.eqb _ _] |- _ => rewrite word.eqb_ne in H
        end.
        1: simpl in *; congruence.
        apply unsigned_ne. rewrite word.unsigned_of_Z. assumption.
      + (* This weakening step is how we link the knowledge about the bound for the loop body
           and for the expression into a bound for both *)
        eapply FlatImp.exec.weaken.
        * eapply IHexec; try eassumption; try reflexivity; maps.
        * intros. simpl in *. simp. repeat eexists; repeat (split || eassumption || solve_MetricLog).
      + simpl in *. simp. rename H4 into IH3.
        match goal with
        | H: _ |- _ => specialize IH3 with (1 := H)
        end.
        eapply FlatImp.exec.weaken.
        * eapply IH3; try reflexivity.
          { clear IH3 IHexec. rewrite E. rewrite E0. reflexivity. }
          1,3: solve [maps].
          pose proof (ExprImp.modVars_subset_allVars c). maps.
        * simpl. intros. simp.
          repeat eexists; repeat (split || eassumption || solve_MetricLog). maps.

    - (* call *)
      unfold flattenCall in *. simp.
      eapply @FlatImp.exec.seq.
      + eapply flattenExprs_correct. 1: eassumption. 4: eassumption. all: try eassumption. maps.
      + simpl in *. intros. simp.
        rename l into lH, l' into lL'. rename l0 into argValNames.
        unfold flatten_functions in H.
        pose proof (map.try_map_values_fw _ _ _ H _ _ H0).
        simp.
        unfold flatten_function, ExprImp2FlatImp in *.
        destruct v2 as [[params' rets'] fbody'].
        simp.
        eapply @FlatImp.exec.call.
        1,2,3: eassumption.
        * unfold ExprImp2FlatImp in *.
          match goal with
          | |- context [fst ?x] => destruct x as [fbody' ngs0] eqn: EF
          end.
          eapply (IHexec eq_refl).
          -- eassumption.
          -- clear -locals_ok. maps.
          -- unfold map.undef_on, map.agree_on.
             intros. rewrite map.get_empty.
             destr (map.get lf k); [exfalso|reflexivity].
             eapply freshNameGenState_spec. 2: eassumption.
             pose proof H2 as G.
             unfold map.of_list_zip in G.
             eapply map.putmany_of_list_zip_find_index in G. 2: eassumption.
             rewrite map.get_empty in G. destruct G as [G | G]; [|discriminate G]. simp.
             eauto using ListSet.In_list_union_l, ListSet.In_list_union_r, nth_error_In.
          -- eapply freshNameGenState_disjoint_fbody.
        * cbv beta. intros. simp.
          edestruct H4 as [resvals ?]. 1: eassumption. simp.
          pose proof (map.putmany_of_list_zip_extends_exists binds resvals) as R.
          assert (map.extends lL' lH) as A by maps.
          edestruct R as [lL'' ?]; [eassumption..|]. simp.
          do 2 eexists. ssplit.
          -- eapply map.getmany_of_list_extends; eassumption.
             (* Automation: Why does "eauto using map.getmany_of_list_extends." not work? *)
          -- eassumption.
          -- do 2 eexists. ssplit; try eassumption.
             ++ simple eapply map.only_differ_putmany; eassumption.
             ++ solve_MetricLog. 

    - (* interact *)
      unfold flattenInteract in *. simp.
      eapply @FlatImp.exec.seq.
      + eapply flattenExprs_correct. 1: eassumption. 4: eassumption. all: try eassumption. maps.
      + simpl in *. intros. simp.
        rename l into lH, l' into lL'. rename l0 into argValNames.
        eapply @FlatImp.exec.interact; [eassumption..|].
        intros. edestruct H3 as (lH' & P & Q). 1: eassumption.
        pose proof (map.putmany_of_list_zip_extends_exists binds resvals) as R.
        assert (map.extends lL' lH) as A by maps. specialize R with (1 := P) (2 := A).
        destruct R as (lL'' & R1 & R2).
        simp.
        simple eapply ex_intro.
        simple apply conj; [exact R1|].
        intros.
        do 2 eexists.
        split; eauto.
        simple apply conj; [eassumption|].
        split; [simple eapply map.only_differ_putmany; eassumption|].
        solve_MetricLog.
  Qed.
  Goal True. idtac "FlattenExpr: flattenStmt_correct_aux done". Abort.

  Lemma flattenStmt_correct: forall eH eL sH sL lL t m mc post,
      flatten_functions eH = Success eL ->
      ExprImp2FlatImp sH = sL ->
      Semantics.exec eH sH t m map.empty mc post ->
      FlatImp.exec eL sL t m lL mc (fun t' m' lL' mcL' => exists lH' mcH',
        post t' m' lH' mcH' /\
        map.extends lL' lH' /\
        (mcL' - mc <= mcH' - mc)%metricsH).
  Proof.
    intros.
    unfold ExprImp2FlatImp in *.
    match goal with
    | H: fst ?x = _ |- _ => destruct x as [sL' ngs'] eqn: E
    end.
    simpl in *. subst sL'.
    eapply @FlatImp.exec.weaken.
    - eapply flattenStmt_correct_aux; try solve [eassumption | reflexivity | maps].
      eapply freshNameGenState_disjoint.
    - simpl. intros. simp. eauto.
  Qed.

End FlattenExpr1.

Goal True. idtac "End of FlattenExpr.v". Abort.
