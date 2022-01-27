Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique.
Require Coq.Strings.String.
Require Import Coq.Numbers.BinNums.

Module Import bopname.
  Inductive bopname := add | sub | mul | mulhuu | divu | remu | and | or | xor | sru | slu | srs | lts | ltu | eq.
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
  | inlinetable (_ : access_size) (table: list Byte.byte) (index: expr)
  | op (op: bopname) (e1 e2: expr)
  | ite (c e1 e2: expr). (* if-then-else expression ("ternary if") *)

  Notation lazy_and e1 e2 := (ite e1 e2 (expr.literal Z0)).

  (* If e1 is nonzero, both returning 1 and returning e1 could make sense,
     but we follow C, which returns 1:
     https://stackoverflow.com/questions/30621389/short-circuiting-of-non-booleans *)
  Notation lazy_or e1 e2 := (ite e1 (expr.literal (Zpos xH)) e2).
End expr. Notation expr := expr.expr.

Module cmd.
  Inductive cmd :=
  | skip
  | set (lhs : String.string) (rhs : expr)
  | unset (lhs : String.string)
  | store (_ : access_size) (address : expr) (value : expr)
  | stackalloc (lhs : String.string) (nbytes : Z) (body : cmd)
  (* { lhs = alloca(nbytes); body; /*allocated memory freed right here*/ } *)
  | cond (condition : expr) (nonzero_branch zero_branch : cmd)
  | seq (s1 s2: cmd)
  | while (test : expr) (body : cmd)
  | call (binds : list String.string) (function : String.string) (args: list expr)
  | interact (binds : list String.string) (action : String.string) (args: list expr).
End cmd. Notation cmd := cmd.cmd.

Definition func : Type := String.string * (list String.string * list String.string * cmd).
#[deprecated(note="Use bedrock2.Syntax.func instead.")]
Notation function := func.
#[deprecated(note="Use bedrock2.Syntax.func instead.")]
Notation bedrock_func := func.

Module Coercions.
  Import String.
  Coercion expr.var : string >-> expr.
  Coercion expr.literal : Z >-> expr.
  Coercion name_of_func (f : func) := fst f.
End Coercions.
