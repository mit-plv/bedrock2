From Coq Require Import List.
From Coq Require Import Lia.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Datatypes.Inhabited.

Declare Scope list_index_scope.

(* Note: Using .. instead of : (like Dafny) doesn't seem to work for a[i .. j],
   and `Check (1 .. 2 .. 3)` says `Special token .. is for use in the Notation command`,
   so we use : (like Python).
   Note: Since Coq prints spaces around operators, we also put spaces around :,
   because `a[:i + j]` would suggest `a[(:i) + j]` instead of `a[:(i + j)]`.
   But if the index is just one number or variable, the space looks weird,
   i.e. we want Coq to print `a[:i]` instead of `a[: i]`, and we achieve this by
   adding an extra only printing rule where i is a `name`.
   We would prefer making i a `global`, which in addition to bound names also includes
   globals and number literals, but `i global` is also printed back even if i is an
   arbitrary expression (COQBUG https://github.com/coq/coq/issues/15360), so we use
   `i name` for now.
   TODO is `a[:i + j]` really that bad?
   Try out new scheme:
   a[:i + j], a[:i], a[j:], a[i:][:n]
   a[i : j], a[i + 1 : j + 3], a[i : j + l]
*)
Notation "a [: i ]" := (List.firstn i a)
  (at level 8, i at level 99, left associativity, format "a [:  i ]")
: list_index_scope.
Notation "a [ : i ]" := (List.firstn i a)
  (at level 8, i name, left associativity, format "a [ : i ]", only printing)
: list_index_scope.

Notation "a [ i :]" := (List.skipn i a)
  (at level 8, i at level 99, left associativity, format "a [ i  :]")
: list_index_scope.
Notation "a [ i : ]" := (List.skipn i a)
  (at level 8, i name, left associativity, format "a [ i : ]", only printing)
: list_index_scope.

(* Note: i needs to be at level <= 99 to avoid conflict with type annotation, and all
   other notations starting with `_ [ _` must therefore also put i at that same level. *)
Notation "a [ i : j ]" := (List.skipn i (List.firstn j a))
  (at level 8, i at level 99, left associativity, format "a [ i  :  j ]")
: list_index_scope.

Section Tests.
  Import ListNotations. Local Open Scope list_scope.
  Local Open Scope list_index_scope.
  Local Open Scope Z_scope. (* to test that number literals are still parsed in nat_scope *)

  Context (A: Type) {inh: inhabited A} (xs ys zs: list A) (a b c: A) (i j k: nat)
          (f: A -> A) (g: list A -> list A).

  Goal xs[:2] = xs[:Nat.two]. Abort.
  Goal xs[:j] = xs[i:]. Abort.
  Goal xs[:3] = ys[4:]. (* has a space, not as desired *) Abort.
  Goal xs[: i + j] = ys[i + j : j + k].  Abort.
  Goal xs[i : j] <> nil.
    (* printing no spaces around `:` here would be nice, but is not possible
       because we can't fake a seemingly different parsing rule that prints the same,
       like we can for `_ [ _ :]` vs `_ [ _ : ]` *)
  Abort.
  Goal xs[i : i + j] = xs[i:][:j]. Abort.
  Goal List.upds xs i ys = zs[i:k]. unfold List.upds. Abort.
End Tests.
