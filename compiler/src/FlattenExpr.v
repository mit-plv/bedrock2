Require Import coqutil.Word.Properties.
Require Import compiler.util.Common.
Require compiler.ExprImp.
Require compiler.FlatImp.
Require Import compiler.NameGen.
Require Import coqutil.Decidable.
Require Import bedrock2.Syntax.
Require Import riscv.Utility.
Require Import bedrock2.Semantics.
Require Import coqutil.Macros.unique.
Require Import Coq.Bool.Bool.
Require Import coqutil.Datatypes.PropSet.
Require Import compiler.Simp.
Require coqutil.Map.Empty_set_keyed_map.


Open Scope Z_scope.

Module Import FlattenExpr.
  Class parameters := {
    varname: Type;
    actname: Type;
    W :> Words;
    varname_eq_dec :> DecidableEq varname;
    actname_eq_dec :> DecidableEq actname;
    locals :> map.map varname Utility.word;
    mem :> map.map Utility.word Utility.byte;
    locals_ok :> map.ok locals;
    mem_ok :> map.ok mem;
    trace := list (mem * actname * list Utility.word * (mem * list Utility.word));
    ext_spec : trace ->
               mem -> actname -> list Utility.word -> (mem -> list Utility.word -> Prop) -> Prop;
    max_ext_call_code_size : actname -> Z;
    max_ext_call_code_size_nonneg : forall a : actname, 0 <= max_ext_call_code_size a;
    NGstate: Type;
    NG :> NameGen varname NGstate;
  }.

  Instance mk_Syntax_params(p: parameters): Syntax.parameters := {|
    Syntax.varname := varname;
    Syntax.funname := Empty_set;
    Syntax.actname := actname;
  |}.

  Instance mk_Semantics_params(p: parameters) : Semantics.parameters := {|
    Semantics.syntax := _;
    Semantics.word := Utility.word;
    Semantics.byte := Utility.byte;
    Semantics.funname_env := Empty_set_keyed_map.map;
    Semantics.funname_eqb := Empty_set_rect _;
    Semantics.ext_spec:= ext_spec;
  |}.

  Instance mk_FlatImpSize_params(p: parameters): FlatImp.FlatImpSize.parameters := {|
    FlatImp.FlatImpSize.bopname_params := _;
    FlatImp.FlatImpSize.max_ext_call_code_size := max_ext_call_code_size;
    FlatImp.FlatImpSize.max_ext_call_code_size_nonneg := max_ext_call_code_size_nonneg;
  |}.

End FlattenExpr.

Section FlattenExpr1.

  Context {p : unique! parameters}.

  Ltac state_calc0 :=
    map_solver (@locals_ok p).

  Ltac set_solver :=
    set_solver_generic (@varname p).

  Definition genFresh_if_needed(resVar: option varname)(ngs: NGstate): (varname * NGstate) :=
    match resVar with
    | Some r => (r, ngs)
    | None => genFresh ngs
    end.

  (* returns stmt and var into which result is saved, and new fresh name generator state.
     If resVar is not None, the result will be stored there, otherwise a fresh var will
     be generated for the result if needed (not needed if e already is a var) *)
  Fixpoint flattenExpr(ngs: NGstate)(resVar: option varname)(e: Syntax.expr):
    (FlatImp.stmt * varname * NGstate) :=
    match e with
    | Syntax.expr.literal n =>
        let '(x, ngs') := genFresh_if_needed resVar ngs in
        (FlatImp.SLit x n, x, ngs')
    | Syntax.expr.var x =>
        match resVar with
        | Some r => (FlatImp.SSet r x, r, ngs)
        | None => (FlatImp.SSkip, x, ngs)
        end
    | Syntax.expr.load sz e =>
        let '(s1, r1, ngs') := flattenExpr ngs None e in
        let '(x, ngs'') := genFresh_if_needed resVar ngs' in
        (FlatImp.SSeq s1 (@FlatImp.SLoad (mk_Syntax_params p) sz x r1), x, ngs'')
    | Syntax.expr.op op e1 e2 =>
        let '(s1, r1, ngs') := flattenExpr ngs None e1 in
        let '(s2, r2, ngs'') := flattenExpr ngs' None e2 in
        let '(x, ngs''') := genFresh_if_needed resVar ngs'' in
        (FlatImp.SSeq s1
          (FlatImp.SSeq s2
            (@FlatImp.SOp (mk_Syntax_params p) x op r1 r2)), x, ngs''')
    end.

  Definition flattenExprAsBoolExpr(ngs: NGstate)(e: Syntax.expr):
    (FlatImp.stmt * FlatImp.bcond * NGstate) :=
    let default := (* always correct, but in some cases we can do better *)
        (let '(stmt, x, ngs') := flattenExpr ngs None e in (stmt, FlatImp.CondNez x, ngs')) in
    match e with
    | Syntax.expr.op op e1 e2 =>
        let '(s1, r1, ngs') := flattenExpr ngs None e1 in
        let '(s2, r2, ngs'') := flattenExpr ngs' None e2 in
        match op with
        | Syntax.bopname.lts => (FlatImp.SSeq s1 s2, FlatImp.CondBinary FlatImp.BLt  r1 r2, ngs'')
        | Syntax.bopname.ltu => (FlatImp.SSeq s1 s2, FlatImp.CondBinary FlatImp.BLtu r1 r2, ngs'')
        | Syntax.bopname.eq  => (FlatImp.SSeq s1 s2, FlatImp.CondBinary FlatImp.BEq  r1 r2, ngs'')
        | _ => default
        end
    | _ => default
    end.

  (* Returns seq of stmt which calculate the list of expressions, and a list of vars into which
     the results are saved, and new fresh name generator state.
     Note: We don't use fold_left or fold_right because none of them does the recursion in
     the way which is easiest to prove: We need the fold_right direction to expose the head of the
     returned list, but we want to first invoke flattenExpr and then flattenExprs, which is
     the opposite order of what fold_right does. *)
  Fixpoint flattenExprs(ngs1: NGstate)(es: list Syntax.expr):
    (FlatImp.stmt * list varname * NGstate) :=
    match es with
    | nil => (FlatImp.SSkip, nil, ngs1)
    | e :: rest => let '(ci, vi, ngs2) := flattenExpr ngs1 None e in
                   let '(cs, vs, ngs3) := flattenExprs ngs2 rest in
                   (FlatImp.SSeq ci cs, vi :: vs, ngs3)
    end.

  (* TODO this is only useful if we also flatten the bodies of all functions *)
  Definition flattenCall(ngs: NGstate)(binds: list varname)(f: Syntax.funname)
             (args: list Syntax.expr):
    FlatImp.stmt * NGstate :=
    let '(compute_args, argvars, ngs) := flattenExprs ngs args in
    (FlatImp.SSeq compute_args (FlatImp.SCall binds f argvars), ngs).

  Definition flattenInteract(ngs: NGstate)(binds: list varname)(a: actname)
             (args: list Syntax.expr):
    FlatImp.stmt * NGstate :=
    let '(compute_args, argvars, ngs) := flattenExprs ngs args in
    (FlatImp.SSeq compute_args (FlatImp.SInteract binds a argvars), ngs).

  (* returns statement and new fresh name generator state *)
  Fixpoint flattenStmt(ngs: NGstate)(s: Syntax.cmd): (FlatImp.stmt * NGstate) :=
    match s with
    | Syntax.cmd.store sz a v =>
        let '(sa, ra, ngs') := flattenExpr ngs None a in
        let '(sv, rv, ngs'') := flattenExpr ngs' None v in
        (FlatImp.SSeq sa (FlatImp.SSeq sv (FlatImp.SStore sz ra rv)), ngs'')
    | Syntax.cmd.set x e =>
        let '(e', x', ngs') := flattenExpr ngs (Some x) e in (* assert(x' = x) *)
        (e', ngs')
    | Syntax.cmd.cond cond sThen sElse =>
        let '(cond', bcond, ngs') := flattenExprAsBoolExpr ngs cond in
        let '(sThen', ngs'') := flattenStmt ngs' sThen in
        let '(sElse', ngs''') := flattenStmt ngs'' sElse in
        (FlatImp.SSeq cond' (FlatImp.SIf bcond sThen' sElse'), ngs''')
    | Syntax.cmd.while cond body =>
        let '(cond', bcond, ngs') := flattenExprAsBoolExpr ngs cond in
        let '(body', ngs'') := flattenStmt ngs' body in
        (FlatImp.SLoop cond' bcond body', ngs'')
    | Syntax.cmd.seq s1 s2 =>
        let '(s1', ngs') := flattenStmt ngs s1 in
        let '(s2', ngs'') := flattenStmt ngs' s2 in
        (FlatImp.SSeq s1' s2', ngs'')
    | Syntax.cmd.skip | Syntax.cmd.unset _ => (FlatImp.SSkip, ngs)
    | Syntax.cmd.call binds f args => flattenCall ngs binds f args
    | Syntax.cmd.interact binds a args => flattenInteract ngs binds a args
    end.

  Arguments Z.add : simpl never.
  Arguments Z.mul : simpl never.

  Ltac specializes H :=
    match type of H with
    | ?P -> ?Q => let n := fresh in assert P as n; [|specialize (H n); specializes H]
    | forall (x: ?T), _ => let n := fresh x in evar (n: T);
                           specialize (H n); subst n; specializes H
    | _ => idtac
    end.

  Lemma flattenExpr_size: forall e s oResVar resVar ngs ngs',
    flattenExpr ngs oResVar e = (s, resVar, ngs') ->
    0 <= FlatImp.stmt_size s <= 2 * ExprImp.expr_size e.
  Proof. Admitted. (*
    induction e; intros; simpl in *; simp; simpl; try omega.
    - specializes IHe; [eassumption|]. omega.
    - specializes IHe1; [eassumption|].
      specializes IHe2; [eassumption|].
      omega.
  Qed.

  Lemma flattenExprAsBoolExpr_size: forall e s bcond ngs ngs',
      flattenExprAsBoolExpr ngs e = (s, bcond, ngs') ->
      FlatImp.stmt_size s <= 2 * ExprImp.expr_size e.
  Proof.
    induction e; intros; simpl in *; repeat destruct_one_match_hyp;
      inversionss; simpl;
      repeat match goal with
      | H : _ |- _ => apply flattenExpr_size in H
      end; try omega.
  Qed.

  Lemma fold_right_cons: forall (A B: Type) (f: B -> A -> A) (a0: A) (b: B) (bs: list B),
      fold_right f a0 (b :: bs) = f b (fold_right f a0 bs).
  Proof.
    intros. reflexivity.
  Qed.

  Lemma flattenCall_size: forall f args binds ngs ngs' s,
      flattenCall ngs binds f args = (s, ngs') ->
      0 < FlatImp.stmt_size s <= 3 * ExprImp.cmd_size (Syntax.cmd.call binds f args).
  Proof.
    intro f.
    induction args; intros.
    - unfold flattenCall in *. simpl in H. inversions H. simpl.
      rewrite! Zcomplements.Zlength_nil in *.
      pose proof (ListLib.Zlength_nonneg binds).
      omega.
    - unfold flattenCall in *. simpl in H.
      repeat destruct_one_match_hyp.
      inversions H.
      inversions E.
      specialize (IHargs binds n0).
      rewrite E1 in IHargs.
      specialize IHargs with (1 := eq_refl).

      unfold ExprImp.cmd_size.
      unfold ExprImp.cmd_size in IHargs.
      rewrite map_cons. rewrite fold_right_cons.
      apply flattenExpr_size in E0.
      simpl in *.
      rewrite! ListLib.Zlength_cons.

      (* PARAMRECORDS ? *)

      (* doesn't match
      forget (@map expr Z (@ExprImp.expr_size semantics_params) args) as FR. *)

      lazymatch goal with
      | H: context [fold_right Z.add 0 ?a] |- context [fold_right Z.add 0 ?a'] =>
        constr_eq a a';
        forget (fold_right Z.add 0 a) as FR
      end.

      repeat match goal with
      | H: context [Zcomplements.Zlength ?a] |- _ =>
        let n := fresh "l" in
        forget (Zcomplements.Zlength a) as n
      | e: expr |- _ => unique pose proof (ExprImp.expr_size_pos e)
      | e: FlatImp.stmt |- _ => unique pose proof (FlatImp.stmt_size_pos e)
      end.

      forget (FlatImp.stmt_size s2) as sz0.
      forget (FlatImp.stmt_size s1) as sz1.
      forget (ExprImp.expr_size a) as esz.

      match goal with
      | |- 0 < ?a <= ?b => ring_simplify a b
      end.
      lazymatch type of IHargs with
      | 0 < ?a <= ?b => ring_simplify a b in IHargs
      end.

      Lia.lia.
  Qed.

  Lemma flattenStmt_size: forall s s' ngs ngs',
    flattenStmt ngs s = (s', ngs') ->
    0 < FlatImp.stmt_size s' <= 3 * ExprImp.cmd_size s.
  Proof.
    induction s; intros; simpl in *; repeat destruct_one_match_hyp; inversionss; simpl;
    repeat match goal with
    | IH: _, A: _ |- _ => specialize IH with (1 := A)
    end;
    repeat match goal with
    | H: flattenExpr _ _ = _ |- _ => apply flattenExpr_size in H
    | H: flattenExprAsBoolExpr _ _ = _ |- _ => apply flattenExprAsBoolExpr_size in H
    end;
    try omega;
    try eapply flattenCall_size; try eassumption.
  Admitted.

  Lemma flattenExpr_freshVarUsage: forall e ngs ngs' s v,
    flattenExpr ngs e = (s, v, ngs') ->
    subset (allFreshVars ngs') (allFreshVars ngs).
  Proof.
    induction e; intros; repeat (inversionss; try destruct_one_match_hyp);
    repeat match goal with
    | H: _ |- _ => apply genFresh_spec in H
    end;
    repeat match goal with
    | IH: forall _ _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
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
             | H : flattenExpr _ _ = _ |- _ => apply flattenExpr_freshVarUsage in H
    end;
    repeat match goal with
    | IH: forall _ _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    set_solver.
  Qed.

  Lemma flattenExpr_valid_resVar: forall e s ngs ngs' resVar,
      flattenExpr ngs e = (s, resVar, ngs') ->
      disjoint (of_list (ExprImp.allVars_expr e)) (allFreshVars ngs) ->
      ~ resVar \in (allFreshVars ngs').
  Proof.
    intros.
    destruct e; simp; simpl in *; simp;
      try match goal with
          | H: _ |- _ => apply genFresh_spec in H; simp; assumption
          end.
    unfold of_list in *. simpl in *. set_solver.
  Qed.

  Lemma flattenExpr_modVars_spec: forall e s ngs ngs' resVar,
    flattenExpr ngs e = (s, resVar, ngs') ->
    subset (FlatImp.modVars s) (diff (allFreshVars ngs) (allFreshVars ngs')).
  Proof.
    induction e; intros; simpl in *; repeat destruct_one_match_hyp;
    simpl;
    repeat match goal with
    | IH: forall _ _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    repeat match goal with
             | H: (_, _, _) = (_, _, _) |- _ => inversion H; subst; clear H
             | H: genFresh _ = _      |- _ => apply genFresh_spec in H
             | H: flattenExpr _ _ = _ |- _ => apply flattenExpr_freshVarUsage in H
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
    | H: flattenExpr _ _ = _ |- _ =>
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
    | H: flattenExpr _ _ = _ |- _ =>
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
    induction args; cbn; intros.
    { inversionss; subst; set_solver. }
    { unfold flattenCall in *. simpl in H.
      repeat destruct_one_match_hyp.
      inversions H.
      inversions E.
      specialize (IHargs binds n0).
      rewrite E1 in IHargs.
      specialize IHargs with (1 := eq_refl).
      apply flattenExpr_freshVarUsage in E0.
      clear -IHargs E0.
      set_solver. }
  Qed.

  Lemma flattenInteract_freshVarUsage: forall args s' binds a ngs1 ngs2,
      flattenInteract ngs1 binds a args = (s', ngs2) ->
      subset (allFreshVars ngs2) (allFreshVars ngs1).
  Proof.
    induction args; intros; unfold flattenInteract in *; simp; try solve [map_solver locals_ok].
    - simpl in E. simp.
      specialize IHargs with (ngs1 := n).
      rewrite E1 in IHargs.
      specialize IHargs with (1 := eq_refl).
      apply flattenExpr_freshVarUsage in E0.
      map_solver locals_ok.
      Unshelve. all: assumption.
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
    end.

  (* only needed if we want to export the goal into a map_solver-only environment *)
  Ltac prepare_for_map_solver :=
    repeat match goal with
             | H: context [allFreshVars ?ngs] |- _ =>
               let n := fresh "fv" ngs in
               forget (allFreshVars ngs) as n
             | H: context [FlatImp.modVars ?var ?func ?s] |- _ =>
               let n := fresh "mv" s in
               forget (FlatImp.modVars var func s) as n
             | H: context [ExprImp.modVars ?s] |- _ =>
               let n := fresh "emv" in
               forget (ExprImp.modVars s) as n
             | H: @eq ?T _ _ |- _ =>
               match T with
            (* | option Semantics.word => don't clear because we have maps of Semantics.word *)
               | nat => clear H
               end
           end;
    repeat match goal with
           | H: context[?x] |- _ =>
             let t := type of x in
             unify t NGstate;
             clear H
           end;
    repeat match goal with
           | x: NGstate |- _ => clear x
           end;
    (repeat (so fun hyporgoal => match hyporgoal with
    | context [ZToReg ?x] => let x' := fresh x in forget (ZToReg x) as x'
    end));
    repeat match goal with
           | H: ?P |- _ =>
             progress
               tryif (let T := type of P in unify T Prop)
               then revert H
               else (match P with
                     | DecidableEq _ => idtac
                     | _ => clear H
                     end)
           end;
    repeat match goal with
           | x: ?T |- _ =>
             lazymatch T with
             | MachineWidth _  => fail
             | DecidableEq _ => fail
             | _ => revert x
             end
           end.

  Ltac state_calc_with_logging :=
    prepare_for_map_solver;
    idtac "map_solver goal:";
    match goal with
    | |- ?G => idtac G
    end;
    time state_calc0.

  Ltac state_calc_with_timing :=
    prepare_for_map_solver;
    time state_calc0.

  Ltac state_calc_without_logging :=
    prepare_for_map_solver;
    state_calc0.

  Ltac state_calc := state_calc0.

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
    simpl in *; (* PARAMRECORDS simplifies implicit arguments to a (hopefully) canoncical form *)
    try solve [set_solver | map_solver (@locals_ok p)].

  Lemma seq_with_modVars: forall env t m l s1 s2 mid post,
    FlatImp.exec env s1 t m l mid ->
    (forall t' m' l',
        mid t' m' l' ->
        map.only_differ l (FlatImp.modVars s1) l' ->
        FlatImp.exec env s2 t' m' l' post) ->
    FlatImp.exec env (FlatImp.SSeq s1 s2) t m l post.
  Proof.
    intros *. intros E1 E2. eapply @FlatImp.exec.seq.
    - eapply @FlatImp.exec.intersect.
      + exact E1.
      + eapply FlatImp.modVarsSound. exact E1.
    - simpl. intros. simp. eauto.
  Qed.

  Lemma flattenExpr_correct_aux : forall e ngs1 ngs2 resVar s initialH initialL initialM res t,
    flattenExpr ngs1 e = (s, resVar, ngs2) ->
    map.extends initialL initialH ->
    map.undef_on initialH (allFreshVars ngs1) ->
    disjoint (of_list (ExprImp.allVars_expr e)) (allFreshVars ngs1) ->
    @eval_expr (mk_Semantics_params p) initialM initialH e = Some res ->
    FlatImp.exec map.empty s t initialM initialL (fun t' finalM finalL =>
      t' = t /\ finalM = initialM /\ map.get finalL resVar = Some res).
  Proof.
    induction e; intros *; intros F Ex U D Ev; simpl in *; simp.

    - (* expr.literal *)
      eapply @FlatImp.exec.lit; t_safe; maps.

    - (* expr.var *)
      eapply @FlatImp.exec.skip; t_safe.

    - (* expr.load *)
      eapply @FlatImp.exec.seq.
      + eapply IHe; eassumption.
      + intros. simpl in *. simp.
        eapply @FlatImp.exec.load; t_safe; try eassumption; maps.

    - (* expr.op *)
      eapply seq_with_modVars.
      + eapply IHe1. 1: eassumption. 4: eassumption. 1,2: eassumption.
        clear -D. set_solver.
      + intros. simpl in *. simp.
        eapply seq_with_modVars.
        * eapply IHe2. 1: eassumption. 4: eassumption. 1,2: solve [maps].
          clear IHe1 IHe2. pose_flatten_var_ineqs. set_solver.
        * intros. simpl in *. simp. clear IHe1 IHe2.
          eapply @FlatImp.exec.op; t_safe; t_safe.
          eapply flattenExpr_valid_resVar in E1.
          { maps. }
          { clear -D. maps. (* TODO can it also work in reasonable time without clearing? *) }
  Qed.

  Lemma flattenExpr_correct_with_modVars : forall e ngs1 ngs2 resVar s t m lH lL res,
    flattenExpr ngs1 e = (s, resVar, ngs2) ->
    map.extends lL lH ->
    map.undef_on lH (allFreshVars ngs1) ->
    disjoint (of_list (ExprImp.allVars_expr e)) (allFreshVars ngs1) ->
    @eval_expr (mk_Semantics_params p) m lH e = Some res ->
    FlatImp.exec map.empty s t m lL (fun t' m' lL' =>
      map.only_differ lL (FlatImp.modVars s) lL' /\
      t' = t /\ m' = m /\ map.get lL' resVar = Some res).
  Proof.
    intros *. intros F Ex U D Ev.
    epose proof (flattenExpr_correct_aux _ _ _ _ _ _ _ _ _ _ F Ex U D Ev) as P.
    eapply FlatImp.exec.intersect; cycle 1.
    - exact P.
    - (* PARAMRECORDS why can't this just be "eapply FlatImp.modVarsSound" ? *)
      eapply @FlatImp.modVarsSound; try typeclasses eauto.
      exact P.
  Qed.

  Lemma flattenExprs_correct: forall es ngs1 ngs2 resVars s t m lH lL resVals,
    flattenExprs ngs1 es = (s, resVars, ngs2) ->
    map.extends lL lH ->
    map.undef_on lH (allFreshVars ngs1) ->
    disjoint (of_list (List.flat_map ExprImp.allVars_expr es)) (allFreshVars ngs1) ->
    List.option_all (List.map (@eval_expr (mk_Semantics_params p) m lH) es) = Some resVals ->
    FlatImp.exec map.empty s t m lL (fun t' m' lL' =>
      t' = t /\ m' = m /\
      List.option_all (List.map (map.get lL') resVars) = Some resVals /\
      map.only_differ lL (FlatImp.modVars s) lL').
  Proof.
    induction es; intros *; intros F Ex U D Evs; simpl in *; simp;
      [ eapply @FlatImp.exec.skip; simpl; repeat split; auto; maps | ].
    rename n into ngs2, ngs2 into ngs3.
    eapply seq_with_modVars.
    - eapply flattenExpr_correct_aux; try eassumption.
      clear -D.
      simpl in *. (* PARAMRECORDS *)
      set_solver.
    - intros. simpl in *. simp.
      assert (disjoint (of_list (flat_map ExprImp.allVars_expr es)) (allFreshVars ngs2)). {
        pose_flatten_var_ineqs.
        simpl in *. (* PARAMRECORDS *)
        set_solver.
      }
      eapply @FlatImp.exec.weaken.
      + eapply IHes; try eassumption; maps.
      + intros. simpl in *. simp.
        replace (map.get l'0 v) with (Some r).
        * rewrite_match. repeat (split || auto). maps.
        * eapply flattenExpr_valid_resVar in E1; [maps|].
          clear -D.
          progress simpl in *. (* PARAMRECORDS without this set_solver cannot solve the goal *)
          set_solver.
  Qed.

  Ltac simpl_reg_eqb :=
    rewrite? word.eqb_eq by congruence;
    rewrite? word.eqb_ne by congruence;
    repeat match goal with
           | E: _ _ _ = true  |- _ => apply word.eqb_true  in E
           | E: _ _ _ = false |- _ => apply word.eqb_false in E
           end.

  Ltac cleanup_options :=
    repeat match goal with
    | H : Some _ = Some _ |- _ =>
        invert_Some_eq_Some
    | |- Some _ = Some _ =>
        f_equal
    end; try discriminate.

  Lemma unsigned_ne: forall (a b: word), word.unsigned a <> word.unsigned b -> a <> b.
  Proof.
    intros.
    intro C.
    subst b.
    apply H.
    reflexivity.
  Qed.

  Lemma one_ne_zero: word.of_Z 1 <> word.of_Z 0.
  Proof.
    apply unsigned_ne.
    rewrite! word.unsigned_of_Z.
    rewrite! Z.mod_small;
      [omega|
       pose proof word.width_pos as P; pose proof (Z.pow_gt_1 2 Utility.width) as Q ..].
    {
      (* PARAMRECORDS *)
      Fail omega.
      simpl.
      omega.
    }
    {
      (* PARAMRECORDS *)
      Fail omega.
      simpl.
      omega.
    }
  Qed.

  Ltac default_flattenBooleanExpr :=
    eapply FlatImp.exec.weaken;
    [ eapply flattenExpr_correct_aux; try eassumption; try reflexivity
    | intros; simpl in *; simp; rewrite_match; auto ].

  (* TODO if we had a decently fast map solver, we needn't prove and apply such lemmas
     manually: *)
  Lemma disjoint_of_list_app: forall (T: Type) (l1 l2: list T) (s: set T),
      disjoint (of_list (l1 ++ l2)) s ->
      disjoint (of_list l1) s /\ disjoint (of_list l2) s.
  Proof.
    intros. split; simpl in *; set_solver_generic T.
  Qed.

  Lemma flattenBooleanExpr_correct_aux :
    forall e ngs1 ngs2 resCond (s: FlatImp.stmt) (initialH initialL: locals) initialM t res,
    flattenExprAsBoolExpr ngs1 e = (s, resCond, ngs2) ->
    map.extends initialL initialH ->
    map.undef_on initialH (allFreshVars ngs1) ->
    disjoint (of_list (ExprImp.allVars_expr e)) (allFreshVars ngs1) ->
    @eval_expr (mk_Semantics_params p) initialM initialH e = Some res ->
    FlatImp.exec map.empty s t initialM initialL (fun t' finalM finalL =>
      t' = t /\ finalM = initialM /\
      FlatImp.eval_bcond finalL resCond = Some (negb (word.eqb res (word.of_Z 0)))).
  Proof.
    destruct e; intros *; intros F Ex U D Ev; unfold flattenExprAsBoolExpr in F; simp.

    1, 2, 3: default_flattenBooleanExpr.

    destruct op; simp; try solve [default_flattenBooleanExpr].

    all: simpl in D; apply disjoint_of_list_app in D; destruct D as [D1 D2].

    all: simpl in *; simp;
      eapply seq_with_modVars;
      [ eapply flattenExpr_correct_with_modVars; try eassumption; try reflexivity
      | intros; simpl in *; simp;
        eapply FlatImp.exec.weaken;
        [ eapply flattenExpr_correct_with_modVars; try eassumption; try reflexivity(*; maps*)
        | intros; simpl in *; simp; repeat rewrite_match; t_safe ] ].

    all: try match goal with
             | |- disjoint _ _ => shelve
             end.
    all: try match goal with
             | |- _ = Some _ => shelve
             end.

    {
      (* TODO consolidate E0 and E5 *)
      pose_flatten_var_ineqs.
(*
      eapply flattenExpr_valid_resVar in E5.

          { maps. }
          { clear -D. maps. (* TODO can it also work in reasonable time without clearing? *) }


    all: replace (map.get l'0 v) with (Some r) by maps;
      f_equal;
      repeat (match goal with
      | |- context[if ?e then _ else _] =>
          destruct e
      | |- true = negb ?b =>
          let H' := fresh in
          pose proof (negb_true_iff b) as H'; destruct H' as [_ H'];
          symmetry; apply H'; simpl_reg_eqb
      | |- false = negb ?b =>
          let H' := fresh in
          pose proof (negb_false_iff b) as H'; destruct H' as [_ H'];
          symmetry; apply H'; simpl_reg_eqb
        end); auto using word.eqb_ne, one_ne_zero.
*)Admitted.

  Lemma flattenBooleanExpr_correct_with_modVars:
    forall e ngs1 ngs2 resCond (s: FlatImp.stmt) (initialH initialL: locals) initialM t res,
    flattenExprAsBoolExpr ngs1 e = (s, resCond, ngs2) ->
    map.extends initialL initialH ->
    map.undef_on initialH (allFreshVars ngs1) ->
    @eval_expr (mk_Semantics_params p) initialM initialH e = Some res ->
    FlatImp.exec map.empty s t initialM initialL (fun t' finalM finalL =>
      (t' = t /\ finalM = initialM /\
       FlatImp.eval_bcond finalL resCond = Some (negb (word.eqb res (word.of_Z 0)))) /\
      map.only_differ initialL (FlatImp.modVars s) finalL (* <-- added *)).
  Proof.
    intros. eapply FlatImp.exec.intersect.
    - eapply flattenBooleanExpr_correct_aux; try eassumption.
      admit.
    - (* PARAMRECORDS why not just "eapply @FlatImp.modVarsSound" ? *)
      eapply @FlatImp.modVarsSound; [typeclasses eauto..|].
      eapply flattenBooleanExpr_correct_aux; try eassumption.
      admit.
  Admitted.

  Lemma flattenStmt_correct_aux: forall e sH t m lH post,
      Semantics.exec e sH t m lH post ->
      e = map.empty ->
      forall ngs ngs' sL lL,
      flattenStmt ngs sH = (sL, ngs') ->
      map.extends lL lH ->
      map.undef_on lH (allFreshVars ngs) ->
      disjoint (ExprImp.modVars sH) (allFreshVars ngs) ->
      FlatImp.exec map.empty sL t m lL (fun t' m' lL' => exists lH',
        post t' m' lH' /\ (* <-- put first so that eassumption will instantiate lH' correctly *)
        map.extends lL' lH' /\
        (* this one is a property purely about ExprImp (it's the conclusion of
           ExprImp.modVarsSound). In the previous proof, which was by induction
           on the fuel of the ExprImp execution, we did not need to carry it
           around in the IH, but could just apply ExprImp.modVarsSound as needed,
           (eg after the when proving the second part of a (SSeq s1 s2)), but
           now we have to make it part of the conclusion in order to get a stronger
           "mid" in that case, because once we're at s2, it's too late to learn/prove
           more things about the (t', m', l') in mid *)
        map.only_differ lH (ExprImp.modVars sH) lH').
  Proof.
    induction 1; intros; simpl in *; subst; simp.

    - (* exec.skip *)
      eapply @FlatImp.exec.skip.
      eexists; repeat (split || eassumption).
      maps.

    - (* exec.set *)
      eapply @FlatImp.exec.seq.
      + eapply flattenExpr_correct_with_modVars; try eassumption. admit.
      + simpl. intros. simp.
        eapply @FlatImp.exec.set; [eassumption|].
        eexists; repeat (split || eassumption); maps.

    - (* exec.unset *)
      eapply @FlatImp.exec.skip.
      eexists; repeat (split || eassumption); maps.

    - (* exec.store *)
      eapply @FlatImp.exec.seq.
      + eapply flattenExpr_correct_with_modVars; try eassumption. admit.
      + intros. simpl in *. simp.
        eapply @FlatImp.exec.seq.
        * eapply flattenExpr_correct_with_modVars; try eassumption; maps. admit.
        * intros. simpl in *. simp.
          eapply @FlatImp.exec.store; try eassumption. 1: maps. 1: admit.
          eexists; repeat (split || eassumption).

  Ltac maps ::=
    pose_flatten_var_ineqs;
    simpl in *; (* PARAMRECORDS simplifies implicit arguments to a (hopefully) canoncical form *)
    try solve [map_solver (@locals_ok p)].

          2: maps.
          pose_flatten_var_ineqs. simpl in *.
          assert (map.only_differ l'0 (union (FlatImp.modVars s0) (FlatImp.modVars s)) lL)
            by (simpl in *; map_solver locals_ok).
          simpl in *.
(* TODO...
map_solver locals_ok.
 idtac. maps.

    - (* if_true *)
      eapply @FlatImp.exec.seq.
      + eapply flattenBooleanExpr_correct_with_modVars; try eassumption.
      + intros. simpl in *. simp.
        eapply @FlatImp.exec.if_true.
        * rewrite H3. f_equal. simpl_reg_eqb. reflexivity.
        * (* including "map.only_differ lH (ExprImp.modVars sH) lH'" in the conclusion
             requires us to do one more weakening step here than otherwise needed: *)
          eapply @FlatImp.exec.weaken.
          { eapply IHexec; try reflexivity; try eassumption; maps. }
          { intros. simpl in *. simp.
            eexists; repeat (split || eassumption); maps. }

    - (* if_false *)
      eapply @FlatImp.exec.seq.
      + eapply flattenBooleanExpr_correct_with_modVars; try eassumption.
      + intros. simpl in *. simp.
        eapply @FlatImp.exec.if_false.
        * rewrite H2. f_equal. simpl_reg_eqb. reflexivity.
        * (* including "map.only_differ lH (ExprImp.modVars sH) lH'" in the conclusion
             requires us to do one more weakening step here than otherwise needed: *)
          eapply @FlatImp.exec.weaken.
          { eapply IHexec; try reflexivity; try eassumption.
            - maps.
            - maps.
            - pose_flatten_var_ineqs. progress simpl in *.
              (* TODO make map_solver work without the intermediate steps *)
              assert (disjoint (ExprImp.modVars c2) (allFreshVars ngs)) as A
                  by map_solver locals_ok.
              assert (subset (allFreshVars n0) (allFreshVars ngs)) as B
                  by map_solver locals_ok.
              clear -A B.
              map_solver locals_ok. }
          { intros. simpl in *. simp.
            eexists; repeat (split || eassumption); maps. }

    - (* seq *)
      eapply seq_with_modVars.
      + eapply IHexec; try reflexivity; try eassumption. maps.
      + simpl. intros. simp.
        rename l into lH, l' into lL', x into lH'.
        (* NOTE how the new high-level locals (lH') are not only constrained by mid and
           by "map.extends lL' lH'" but also by the additional
           "map.only_differ lH (ExprImp.modVars c1) lH'".
           This additional constraint is not related to the flattening at all, but we still
           have to carry it in the conclusion of the statement in order to get it here *)

        (* including "map.only_differ lH (ExprImp.modVars sH) lH'" in the conclusion
           requires us to do one more weakening step here than otherwise needed: *)
        eapply @FlatImp.exec.weaken.
        * eapply H1 (* <-- that's an IH too *); try reflexivity; try eassumption.
          { (* note: here we need the high-level map.only_differ we were carrying around *)
            Fail (solve [clear H9; maps]).
            solve [maps]. }
          { maps. }
        * clear IHexec H1.
          simpl. intros. simp.
          eexists; repeat (split || eassumption); maps.

    - (* while_false *)
      eapply @FlatImp.exec.loop;
        [ eapply flattenBooleanExpr_correct_with_modVars; try eassumption
        | intros; simpl in *; simp .. ].
      + congruence.
      + eexists; repeat (split || eassumption); maps.
      + exfalso. rewrite word.eqb_eq in H6 by reflexivity. simpl in *. congruence.
      + exfalso. exact H1. (* instantiates mid2 to (fun _ _ _ => False) *)

    - (* while_true *)
      eapply @FlatImp.exec.loop;
        [ eapply flattenBooleanExpr_correct_with_modVars; try eassumption
        | intros; simpl in *; simp .. ].
      + congruence.
      + exfalso. rewrite word.eqb_ne in H9 by congruence. simpl in *. congruence.
      + eapply IHexec; try eassumption; try reflexivity; maps.
      + simpl in *. simp.
        specialize H3 with (1 := H4).
        eapply FlatImp.exec.weaken.
        * eapply H3; try reflexivity. (* <-- also an IH *)
          { clear H3 IHexec. rewrite E. rewrite E0. reflexivity. }
          all: maps.
        * simpl. intros. simp.
          eexists; repeat (split || eassumption); maps.

    - (* call *)
      destruct fname.

    - (* interact *)
      unfold flattenInteract in *. simp.
      eapply @FlatImp.exec.seq.
      + eapply flattenExprs_correct. 1: eassumption. 3: eassumption. all: eassumption.
      + simpl in *. intros. simp.
        rename l into lH, l' into lL'. rename l0 into argValNames.
        eapply @FlatImp.exec.interact; [eassumption..|].
        intros. edestruct H1 as (lH' & P & Q). 1: eassumption.
        pose proof (map.putmany_of_list_extends_exists binds resvals) as R.
        assert (map.extends lL' lH) as A by maps. specialize R with (1 := P) (2 := A).
        destruct R as (lL'' & R1 & R2).
        eauto 10 using only_differ_putmany.
  Qed.
*)
  Admitted.
  *)

  Definition ExprImp2FlatImp(s: Syntax.cmd): FlatImp.stmt :=
    fst (flattenStmt (freshNameGenState (ExprImp.allVars_cmd s)) s).

  Lemma flattenStmt_correct: forall sH sL t m post,
      ExprImp2FlatImp sH = sL ->
      Semantics.exec map.empty sH t m map.empty post ->
      FlatImp.exec map.empty sL t m map.empty (fun t' m' lL' => exists lH',
        post t' m' lH' /\
        map.extends lL' lH').
  Proof.
  Admitted. (*
    intros.
    unfold ExprImp2FlatImp in *.
    match goal with
    | H: fst ?x = _ |- _ => destruct x as [sL' ngs'] eqn: E
    end.
    simpl in *. subst sL'.
    eapply @FlatImp.exec.weaken.
    - eapply flattenStmt_correct_aux; try solve [eassumption | reflexivity | maps].
      unfold disjoint.
      intro x.
      pose proof (freshNameGenState_spec (ExprImp.allVars_cmd sH) x) as P.
      match type of P with
      | In ?x ?l -> _ => destruct (in_dec varname_eq_dec x l) as [Iyes | Ino]
      end.
      + auto.
      + left. clear -Ino.
        intro. apply Ino.
        pose proof @ExprImp.modVars_subset_allVars as Q.
        specialize Q with (1 := H). exact Q.
    - simpl. intros. simp. eauto.
  Qed.
  *)

End FlattenExpr1.
