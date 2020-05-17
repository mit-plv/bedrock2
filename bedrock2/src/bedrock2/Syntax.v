(*tag:importboilerplate*)
Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique.
Require Coq.Strings.String.
Require Import Coq.Numbers.BinNums.

(*tag:workaround*)
Module Import bopname.
  (*tag:compiletimecode*)
  Inductive bopname := add | sub | mul | mulhuu | divu | remu | and | or | xor | sru | slu | srs | lts | ltu | eq.
(*tag:workaround*)
End bopname.
Notation bopname := bopname.bopname.

Module access_size.
  (*tag:compiletimecode*)
  Variant access_size := one | two | four | word.
  Scheme Equality for access_size.
End access_size. Notation access_size := access_size.access_size.
(*tag:workaround*)

Module expr.
  (*tag:compiletimecode*)
  Inductive expr  : Type :=
  | literal (v: Z)
  | var (x: String.string)
  | load (_ : access_size) (addr:expr)
  | op (op: bopname) (e1 e2: expr).
(*tag:workaround*)
End expr. Notation expr := expr.expr.

  (*tag:compiletimecode*)
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
(*tag:workaround*)
End cmd. Notation cmd := cmd.cmd.
