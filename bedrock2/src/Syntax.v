Require Import bedrock2.Macros.

Require Import Coq.Numbers.BinNums.
  
Class parameters := {
  varname : Type;
  funname : Type;
  actname : Type;
  bopname : Type;
}.


Module expr. Section expr.
  Context {p : unique! parameters}.
  Inductive expr  : Type :=
  | literal (v: Z)
  | var (x: varname)
  | load (access_size_in_bytes:Z) (addr:expr)
  | op (op: bopname) (e1 e2: expr).
End expr. End expr. Notation expr := expr.expr.

Module cmd. Section cmd.
  Context {p : unique! parameters}.
  Inductive cmd :=
  | skip
  | set (lhs : varname) (rhs : expr)
  | store (size_in_bytes : Z) (address : expr) (value : expr)
  | cond (condition : expr) (nonzero_branch zero_branch : cmd)
  | seq (s1 s2: cmd)
  | while (test : expr) (body : cmd)
  | call (binds : list varname) (function : funname) (args: list expr)
  | interact (binds : list varname) (action : actname) (args: list expr).
End cmd. End cmd. Notation cmd := cmd.cmd.