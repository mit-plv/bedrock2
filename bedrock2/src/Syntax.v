Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique.

Require Import Coq.Numbers.BinNums.

Module Import bopname.
  Inductive bopname := add | sub | mul | and | or | xor | sru | slu | srs | lts | ltu | eq.
End bopname.
Notation bopname := bopname.bopname.
  
Local Set Primitive Projections.
Class parameters := {
  varname : Type;
  funname : Type;
  actname : Type;
}.

Module access_size.
  Variant access_size := one | two | four | word.
  Scheme Equality for access_size.
End access_size. Notation access_size := access_size.access_size.

Module expr. Section expr.
  Context {p : unique! parameters}.
  Inductive expr  : Type :=
  | literal (v: Z)
  | var (x: varname)
  | load (_ : access_size) (addr:expr)
  | op (op: bopname) (e1 e2: expr).
End expr. End expr. Notation expr := expr.expr.

Module cmd. Section cmd.
  Context {p : unique! parameters}.
  Inductive cmd :=
  | skip
  | set (lhs : varname) (rhs : expr)
  | unset (lhs : varname)
  | store (_ : access_size) (address : expr) (value : expr)
  | cond (condition : expr) (nonzero_branch zero_branch : cmd)
  | seq (s1 s2: cmd)
  | while (test : expr) (body : cmd)
  | call (binds : list varname) (function : funname) (args: list expr)
  | interact (binds : list varname) (action : actname) (args: list expr).
End cmd. End cmd. Notation cmd := cmd.cmd.
