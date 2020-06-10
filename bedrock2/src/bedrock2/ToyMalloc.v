Require Import Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.sanity.
Require Import coqutil.Decidable.
Require Import coqutil.Map.Interface coqutil.Map.Properties.

(*
pexpr/pcmd : pair expressions/commands: A while language with immutable pairs are values
  |
  |  compilation *introduces* internal nondeterminism through address returned by malloc
  V
mexpr/mcmd : malloc expressions/commands: A while language where expressions include a malloc command
  |          and evaluation order within expression is nondeterministic
  |
  |  compilation is the identify function, but semantics change *reduces* nondeterminism
  V
mexpr/mcmd : The same language, but with deterministic left-to-right expression evaluation order

The composition of the two phases results in a compilation that both *introduces* and *reduces*
nondeterminism.
*)

Inductive bopname := add | sub | mul.

(* Source language *)

Inductive pexpr :=
| PLiteral(v: Z)
| PVar(x: String.string)
| POp(e1: pexpr)(op: bopname)(e2: pexpr)
| PPair(e1 e2: pexpr)
| PFst(e: pexpr)
| PSnd(e: pexpr)
| PLetIn(x: String.string)(e: pexpr)(body: pexpr)
| PIf(cond thn els: pexpr).

(* Target language *)

Inductive mexpr :=
| MLiteral(v: Z)
| MVar(x: String.string)
| MLoad(addr: mexpr)
| MStore(address value: mexpr)
| MSet(lhs: String.string)(rhs: mexpr)
| MOp(e1: mexpr)(op: bopname)(e2: mexpr)
| MMalloc(amount: mexpr)
| MComma(e1 e2: mexpr) (* evaluate e1 just for its side effects, return e2 *)
| MIf(cond thn els: mexpr).

(* TODO can we make this work without a fresh name generator and map reasoning? *)

Inductive value :=
| VWord(w: Z)
| VPair(fst snd: value).

Section ToyMalloc.
  Context {mem : map.map Z Z}
          {locals : map.map String.string Z}
          {mem_ok : map.ok mem}
          {locals_ok : map.ok locals}.
End ToyMalloc.
