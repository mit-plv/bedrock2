Require Import Coq.Strings.String.
Require Import bedrock2.Syntax.

Inductive assignment_rhs :=
| RCall(fname: string)(args: list expr)
| RExpr(e: expr).

Inductive snippet :=
| SAssign(is_decl: bool)(x: string)(r: assignment_rhs) (* uintptr_t x = r;  |  x = r; *)
| SVoidCall(fname: string)(args: list expr)            (* fname(args);                *)
| SStore(sz: access_size)(addr val: expr)              (* store[|8|16|32](addr, val); *)
| SIf(cond: expr)(split: bool)                         (* if (cond) /* split */ {     *)
| SElse(startsWithClosingBrace: bool)                  (* } else {     |    else {    *)
| SWhile(c: expr){Measure: Type}(m: Measure)           (* while(c)/* decreases m */ { *)
| SStart                                               (* {                           *)
| SEnd                                                 (* }                           *)
| SRet(retexpr: expr)                                  (* return e;                   *)
| SEmpty.                                              (* /* for C comments */        *)
