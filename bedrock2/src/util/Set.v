Require Import compiler.util.Tactics.
Require Import compiler.Decidable.
Require Import compiler.util.ListLib.
Require Import Coq.Program.Tactics.
Require Import Coq.Lists.List.
Import ListNotations.

Class SetFunctions(E: Type) := mkSet {
  set: Type;

  contains: set -> E -> Prop;
  containsb: set -> E -> bool;

  empty_set: set;
  singleton_set: E -> set;

  union: set -> set -> set;
  intersect: set -> set -> set;
  diff: set -> set -> set;
  pick_or_else: set -> E -> (E * set);

  set_elem_eq_dec: DecidableEq E;
  empty_set_spec: forall (x: E), contains empty_set x <-> False;
  containsb_spec: forall (x: E) (A: set), containsb A x = true <-> contains A x;
  singleton_set_spec: forall (x y: E), contains (singleton_set y) x <-> x = y;
  union_spec: forall (x: E) (A B: set), contains (union A B) x <-> contains A x \/ contains B x;
  intersect_spec: forall (x: E) (A B: set), contains (intersect A B) x <-> contains A x /\ contains B x;
  diff_spec: forall (x: E) (A B: set), contains (diff A B) x <-> contains A x /\ ~ contains B x;
  pick_or_else_spec: forall (A: set) (default: E),
      A = empty_set /\ pick_or_else A default = (default, empty_set) \/
      exists (a: E), contains A a /\ pick_or_else A default = (a, diff A (singleton_set a))
}.

Arguments set E {_}.

Hint Rewrite
  @empty_set_spec
  @singleton_set_spec
  @union_spec
  @intersect_spec
  @diff_spec
: rew_set_op_specs.

Notation "x '\in' s" := (contains s x) (at level 39, no associativity).

Section SetDefinitions.
  Context {E: Type}.
  Context {setInst: SetFunctions E}.

  Definition add(s: set E)(e: E) := union (singleton_set e) s.
  Definition remove(s: set E)(e: E) := diff s (singleton_set e).
  Definition subset(s1 s2: set E) := forall x, x \in s1 -> x \in s2.
  Definition disjoint(s1 s2: set E) := forall x, (~ x \in s1) \/ (~ x \in s2).
  Definition of_list l := List.fold_right union empty_set (List.map singleton_set l).
End SetDefinitions.

Hint Unfold add subset disjoint : unf_set_defs.

Definition TODO{T: Type}: T. Admitted.

Instance List_Set(E: Type){eeq: DecidableEq E}: SetFunctions E := {|
  set := list E;

  contains A e := List.In e A;
  containsb A e := if List.in_dec eeq e A then true else false;

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

Ltac set_solver_generic E :=
  repeat autounfold with unf_set_defs in *;
  destruct_products;
  intros;
  specialize_with E;
  autorewrite with rew_set_op_specs in *;
  intuition (subst *; auto).
