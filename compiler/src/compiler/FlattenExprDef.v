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

Section FlattenExpr1.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}
          {word_ok: word.ok word}
          {locals: map.map String.string word}
          {mem: map.map word byte}
          {ExprImp_env: map.map string (list string * list string * cmd)}
          {FlatImp_env: map.map string (list string * list string * FlatImp.stmt string)}
          {ext_spec: ExtSpec}
          {NGstate: Type}
          {NG: NameGen String.string NGstate}.

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
    | Syntax.expr.ite c e1 e2 =>
        let '(sc, rc, ngs') := flattenExpr ngs None c in
        let '(r, ngs'') := genFresh_if_needed resVar ngs' in
        let '(s1, r1, ngs''') := flattenExpr ngs'' (Some r) e1 in
        let '(s2, r2, ngs'''') := flattenExpr ngs''' (Some r) e2 in
        (FlatImp.SSeq sc (FlatImp.SIf (FlatImp.CondNez rc) s1 s2), r, ngs'''')
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

  Definition ExprImp2FlatImp(s: Syntax.cmd): FlatImp.stmt string :=
    fst (flattenStmt (freshNameGenState (ExprImp.allVars_cmd_as_list s)) s).

  Definition flatten_function: list string * list string * Syntax.cmd ->
                               result (list string * list string * FlatImp.stmt string) :=
    fun '(argnames, retnames, body) =>
      let avoid := ListSet.list_union String.eqb
                                      (ListSet.list_union String.eqb argnames retnames)
                                      (ExprImp.allVars_cmd_as_list body) in
      let body' := fst (flattenStmt (freshNameGenState avoid) body) in
      Success (argnames, retnames, body').

  Definition flatten_functions: ExprImp_env -> result FlatImp_env :=
    map.try_map_values flatten_function.

End FlattenExpr1.
