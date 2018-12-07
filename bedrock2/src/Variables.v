Require Import coqutil.subst coqutil.unique bedrock2.Syntax.

Require Import Coq.Lists.List.

Module expr. Section expr. Import Syntax.expr.
  Context {p : unique! Syntax.parameters}.
  Fixpoint vars (e : expr) : list varname :=
    match e with
    | literal v => nil
    | var x => cons x nil
    | load _ ea => vars ea
    | op _ e1 e2 => List.app (vars e1) (vars e2)
    end.
End expr. End expr.

Module cmd. Section cmd. Import Syntax.cmd.
  Context {p : unique! Syntax.parameters}.
  Fixpoint vars (c: cmd) : list varname := 
    match c with
    | skip => nil
    | set x e => x::expr.vars e
    | unset x => x::nil
    | store _ ea ev => expr.vars ea ++ expr.vars ev
    | cond eb ct cf => expr.vars eb ++ (vars ct ++ vars cf)
    | seq c1 c2 => vars c1 ++ vars c2
    | while e c => expr.vars e ++ vars c
    | call binds _ args | interact binds _ args => binds ++ (List.flat_map expr.vars args)
    end.
End cmd. End cmd.