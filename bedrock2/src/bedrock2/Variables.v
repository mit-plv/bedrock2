Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.

Require Import Coq.Lists.List.

Module expr. Import Syntax.expr.
  Fixpoint vars (e : expr) : list String.string :=
    match e with
    | literal v => nil
    | var x => cons x nil
    | load _ ea => vars ea
    | inlinetable _ _ index => vars index
    | op _ e1 e2 => List.app (vars e1) (vars e2)
    end.
End expr.

Module cmd. Import Syntax.cmd.
  Fixpoint vars (c: cmd) : list String.string :=
    match c with
    | skip => nil
    | set x e => x::expr.vars e
    | unset x => x::nil
    | store _ ea ev => expr.vars ea ++ expr.vars ev
    | stackalloc x n body => x :: vars body
    | cond eb ct cf => expr.vars eb ++ (vars ct ++ vars cf)
    | seq c1 c2 => vars c1 ++ vars c2
    | while e c => expr.vars e ++ vars c
    | call binds _ args | interact binds _ args => binds ++ (List.flat_map expr.vars args)
    end.
End cmd.
