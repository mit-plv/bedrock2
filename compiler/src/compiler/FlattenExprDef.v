Require Import coqutil.Word.Properties.
Require Import compiler.util.Common.
Require compiler.ExprImp.
Require compiler.FlatImp.
Require Import compiler.NameGen.
Require Import coqutil.Decidable.
Require Import bedrock2.Syntax.
Require Import riscv.Utility.Utility.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.Semantics.
Require Import coqutil.Macros.unique.
Require Import Coq.Bool.Bool.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.Simp.
Require Import coqutil.Datatypes.String.

Open Scope Z_scope.

Module Import FlattenExpr.
  Class parameters := {
    W :> Words;
    locals :> map.map String.string Utility.word;
    mem :> map.map Utility.word byte;
    ExprImp_env :> map.map string (list string * list string * cmd);
    FlatImp_env :> map.map string (list string * list string * FlatImp.stmt string);
    trace := list (mem * string * list Utility.word * (mem * list Utility.word));
    ext_spec : trace ->
               mem -> string -> list Utility.word -> (mem -> list Utility.word -> Prop) -> Prop;
    NGstate: Type;
    NG :> NameGen String.string NGstate;
  }.

  Instance mk_Semantics_params(p: parameters) : Semantics.parameters := {|
    Semantics.word := Utility.word;
    Semantics.env := ExprImp_env;
    Semantics.ext_spec:= ext_spec;
  |}.

  Instance mk_FlatImp_params(p: parameters): FlatImp.parameters string := {
    FlatImp.varname_eqb := String.eqb;
    FlatImp.ext_spec := ext_spec;
  }.

  Class assumptions{p: parameters}: Prop := {
    locals_ok :> map.ok locals;
    mem_ok :> map.ok mem;
    ExprImp_env_ok :> map.ok ExprImp_env;
    FlatImp_env_ok :> map.ok FlatImp_env;
    ext_spec_ok: FlatImp.ext_spec.ok _ _;
  }.
  Arguments assumptions: clear implicits.

  Instance mk_ExprImp_ext_spec_ok(p: parameters)(hyps: assumptions p): ext_spec.ok (mk_Semantics_params p).
  Proof.
    destruct hyps. destruct ext_spec_ok0.
    constructor.
    all: intros; eauto.
    eapply intersect; eassumption.
  Qed.

  Instance mk_Semantics_params_ok(p: parameters)(hyps: assumptions p):
    Semantics.parameters_ok (mk_Semantics_params p) := {
    Semantics.locals_ok := locals_ok;
    Semantics.word_ok := Utility.word_ok;
    Semantics.mem_ok := mem_ok;
    Semantics.env_ok := ExprImp_env_ok;
    Semantics.width_cases := Utility.width_cases;
    Semantics.ext_spec_ok := _
  }.

  Instance mk_FlatImp_params_ok{p: parameters}(hyps: @assumptions p):
    FlatImp.parameters_ok string (mk_FlatImp_params p) := {
    FlatImp.varname_eq_spec := String.eqb_spec;
    FlatImp.width_cases := width_cases;
    FlatImp.word_ok := word_ok;
    FlatImp.mem_ok := mem_ok;
    FlatImp.locals_ok := locals_ok;
    FlatImp.env_ok := FlatImp_env_ok;
    FlatImp.ext_spec_ok := ext_spec_ok;
  }.

End FlattenExpr.

Section FlattenExpr1.

  Context {p : unique! parameters}.

  Ltac set_solver :=
    set_solver_generic (@String.string p).

  Definition genFresh_if_needed(resVar: option String.string)(ngs: NGstate): (String.string * NGstate) :=
    match resVar with
    | Some r => (r, ngs)
    | None => genFresh ngs
    end.

  (* returns stmt and var into which result is saved, and new fresh name generator state.
     If resVar is not None, the result will be stored there, otherwise a fresh var will
     be generated for the result if needed (not needed if e already is a var) *)
  Fixpoint flattenExpr(ngs: NGstate)(resVar: option String.string)(e: Syntax.expr):
    (FlatImp.stmt String.string * String.string * NGstate) :=
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
        (FlatImp.SSeq s1 (FlatImp.SLoad sz x r1 0), x, ngs'')
    | Syntax.expr.inlinetable sz t index =>
        let '(r1, ngs') := genFresh ngs in (* by picking r1 fresh, we guarantee r1 <> x *)
        let '(s1, r1, ngs'') := flattenExpr ngs' (Some r1) index in
        let '(x, ngs''') := genFresh_if_needed resVar ngs'' in
        (FlatImp.SSeq s1 (FlatImp.SInlinetable sz x t r1), x, ngs''')
    | Syntax.expr.op op e1 e2 =>
        let '(s1, r1, ngs') := flattenExpr ngs None e1 in
        let '(s2, r2, ngs'') := flattenExpr ngs' None e2 in
        let '(x, ngs''') := genFresh_if_needed resVar ngs'' in
        (FlatImp.SSeq s1
          (FlatImp.SSeq s2
            (FlatImp.SOp x op r1 r2)), x, ngs''')
    end.

  Definition flattenExprAsBoolExpr(ngs: NGstate)(e: Syntax.expr):
    (FlatImp.stmt string * FlatImp.bcond string * NGstate) :=
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
    (FlatImp.stmt string * list String.string * NGstate) :=
    match es with
    | nil => (FlatImp.SSkip, nil, ngs1)
    | e :: rest => let '(ci, vi, ngs2) := flattenExpr ngs1 None e in
                   let '(cs, vs, ngs3) := flattenExprs ngs2 rest in
                   (FlatImp.SSeq ci cs, vi :: vs, ngs3)
    end.

  (* TODO this is only useful if we also flatten the bodies of all functions *)
  Definition flattenCall(ngs: NGstate)(binds: list String.string)(f: String.string)
             (args: list Syntax.expr):
    FlatImp.stmt string * NGstate :=
    let '(compute_args, argvars, ngs) := flattenExprs ngs args in
    (FlatImp.SSeq compute_args (FlatImp.SCall binds f argvars), ngs).

  Definition flattenInteract(ngs: NGstate)(binds: list String.string)(a: String.string)
             (args: list Syntax.expr):
    FlatImp.stmt string * NGstate :=
    let '(compute_args, argvars, ngs) := flattenExprs ngs args in
    (FlatImp.SSeq compute_args (FlatImp.SInteract binds a argvars), ngs).

  (* returns statement and new fresh name generator state *)
  Fixpoint flattenStmt(ngs: NGstate)(s: Syntax.cmd): (FlatImp.stmt string * NGstate) :=
    match s with
    | Syntax.cmd.store sz a v =>
        let '(sa, ra, ngs') := flattenExpr ngs None a in
        let '(sv, rv, ngs'') := flattenExpr ngs' None v in
        (FlatImp.SSeq sa (FlatImp.SSeq sv (FlatImp.SStore sz ra rv 0)), ngs'')
    | Syntax.cmd.set x e =>
        let '(e', x', ngs') := flattenExpr ngs (Some x) e in (* assert(x' = x) *)
        (e', ngs')
    | Syntax.cmd.stackalloc x n body =>
        let '(body', ngs') := flattenStmt ngs body in
        (FlatImp.SStackalloc x n body', ngs')
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

  Definition ExprImp2FlatImp0(s: Syntax.cmd): FlatImp.stmt string :=
    fst (flattenStmt (freshNameGenState (ExprImp.allVars_cmd_as_list s)) s).

  Section WithMaxSize.
    Context (max_size: Z).

    Definition ExprImp2FlatImp(s: Syntax.cmd): option (FlatImp.stmt string) :=
      let res := ExprImp2FlatImp0 s in
      if FlatImp.stmt_size res <? max_size then Some res else None.

    Definition flatten_function:
      list String.string * list String.string * Syntax.cmd -> option (list String.string * list String.string * FlatImp.stmt string) :=
      fun '(argnames, retnames, body) =>
        let avoid := ListSet.list_union String.eqb (ExprImp.allVars_cmd_as_list body)
                                                    (ListSet.list_union String.eqb argnames retnames) in
        let body' := fst (flattenStmt (freshNameGenState avoid) body) in
        if FlatImp.stmt_size body' <? max_size then Some (argnames, retnames, body') else None.

    Definition flatten_functions: ExprImp_env -> option FlatImp_env :=
      map.map_all_values flatten_function.

  End WithMaxSize.

End FlattenExpr1.
