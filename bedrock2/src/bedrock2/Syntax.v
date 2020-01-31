Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique.
Require Coq.Strings.String.
Require Import Coq.Numbers.BinNums.

Module Import bopname.
  Inductive bopname := add | sub | and | or | xor | sru | slu | srs | lts | ltu | eq.
End bopname.
Notation bopname := bopname.bopname.

Module access_size.
  Variant access_size := one | two | four | word.
  Scheme Equality for access_size.
End access_size. Notation access_size := access_size.access_size.

Module expr.
  Inductive expr  : Type :=
  | literal (v: Z)
  | var (x: String.string)
  | load (_ : access_size) (addr:expr)
  | op (op: bopname) (e1 e2: expr).
End expr. Notation expr := expr.expr.

Module cmd.
  Inductive cmd :=
  | skip
  | set (lhs : String.string) (rhs : expr)
  | unset (lhs : String.string)
  | store (_ : access_size) (address : expr) (value : expr)
  | cond (condition : expr) (nonzero_branch zero_branch : cmd)
  | seq (s1 s2: cmd)
  | while (test : expr) (body : cmd)
  | call (binds : list String.string) (function : String.string) (args: list expr)
  | interact (binds : list String.string) (action : String.string) (args: list expr).
End cmd. Notation cmd := cmd.cmd.
