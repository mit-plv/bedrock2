Require Import compiler.util.Tactics.
Require Import coqutil.Decidable.
Require Import compiler.util.ListLib.
Require Import compiler.util.Set.
Require Import Coq.Program.Tactics.
Require Import Coq.Lists.List.
Import ListNotations.

Definition TODO{T: Type}: T. Admitted.

Instance List_Set(E: Type){eeq: DecidableEq E}: SetFunctions E := {|
  set := list E;

  contains A e := List.In e A;
  contains_dec := List.in_dec eeq;

  empty_set := nil;
  singleton_set e := (cons e nil);

  union := list_union;
  intersect := list_intersect;
  diff := list_diff;
  pick_or_else A default := match A with
                             | a :: rest => (a, rest)
                             | nil => (default, nil)
                            end;
|}.
all: apply TODO.
Defined.
