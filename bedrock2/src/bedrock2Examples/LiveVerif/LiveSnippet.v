Require Import Coq.Strings.String.
Require Import bedrock2.Syntax.

Inductive snippet :=
| SAssign(is_decl: bool)(x: string)(e: Syntax.expr)
| SCall(lhs: option (bool (* is_decl *) * string (* varname *)))
       (fname: string)(args: list Syntax.expr)
| SStore(sz: access_size)(addr val: Syntax.expr)
| SIf(cond: Syntax.expr)
| SElse
| SWhile(cond: Syntax.expr){Measure: Type}(measure0: Measure)
| SStart
| SEnd
| SRet(xs: list string)
| SEmpty.
