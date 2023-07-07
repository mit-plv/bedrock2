Require Import Coq.Strings.String.
Require Import bedrock2.Syntax.

Inductive assignment_rhs :=
| RCall(fname: string)(args: list Syntax.expr)
| RExpr(e: Syntax.expr).

Inductive snippet :=
| SAssign(is_decl: bool)(x: string)(r: assignment_rhs)
| SVoidCall(fname: string)(args: list Syntax.expr)
| SStore(sz: access_size)(addr val: Syntax.expr)
| SIf(cond: Syntax.expr)(split: bool)
| SElse(startsWithClosingBrace: bool)
| SWhile(cond: Syntax.expr){Measure: Type}(measure0: Measure)
| SStart
| SEnd
| SRet(retexpr: Syntax.expr)
| SEmpty.
