Require Import compiler.util.Tactics.
Require Import compiler.Decidable.
Require Import compiler.util.ListLib.
Require Import compiler.util.Set.
Require Import Coq.Program.Tactics.
Require Import Coq.Lists.List.
Import ListNotations.

Definition TODO{T: Type}: T. Admitted.

Instance PropFunc_Set(E: Type){eeq: DecidableEq E}: SetFunctions E := {|
  set := E -> Prop;

  contains A e := A e;

  empty_set := fun e => False;
  singleton_set e := fun e' => e = e';

  union s1 s2 := fun e => s1 e \/ s2 e;
  intersect s1 s2 := fun e => s1 e /\ s2 e;
  diff s1 s2 := fun e => s1 e /\ ~ s2 e;
  pick_or_else A default := TODO; (* will never work *)
|}.
all: apply TODO.
Defined.
