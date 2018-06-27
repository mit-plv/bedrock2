Require Import compiler.Tactics.
Require Import Coq.Program.Tactics.

Class set(T E: Type) := mkSet {
  contains: T -> E -> Prop;

  empty_set: T;
  singleton_set: E -> T;

  union: T -> T -> T;
  intersect: T -> T -> T;
  diff: T -> T -> T;

  empty_set_spec: forall (x: E), contains empty_set x <-> False;
  singleton_set_spec: forall (x y: E), contains (singleton_set y) x <-> x = y;
  union_spec: forall (x: E) (A B: T), contains (union A B) x <-> contains A x \/ contains B x;
  intersect_spec: forall (x: E) (A B: T), contains (intersect A B) x <-> contains A x /\ contains B x;
  diff_spec: forall (x: E) (A B: T), contains (diff A B) x <-> contains A x /\ ~ contains B x
}.

Hint Rewrite
  @empty_set_spec
  @singleton_set_spec
  @union_spec
  @intersect_spec
  @diff_spec
: rew_set_op_specs.

Notation "x '\in' s" := (contains s x) (at level 39, no associativity).

Section SetDefinitions.
  Context {T E: Type}.
  Context {setInst: set T E}.

  Definition subset(s1 s2: T) := forall x, x \in s1 -> x \in s2.
  Definition disjoint(s1 s2: T) := forall x, (~ x \in s1) \/ (~ x \in s2).
  Definition of_list l := List.fold_right union empty_set (List.map singleton_set l).
End SetDefinitions.

Hint Unfold subset disjoint : unf_set_defs.

Instance Function_Set(E: Type): set (E -> Prop) E := {|
  contains := fun s => s;
  empty_set := fun _ => False;
  singleton_set y := fun x => x = y;
  union := fun s1 s2 => fun x => s1 x \/ s2 x;
  intersect := fun s1 s2 => fun x => s1 x /\ s2 x;
  diff := fun s1 s2 => fun x => s1 x /\ ~ s2 x
|}.
  all: tauto.
Defined.

Ltac set_solver_generic E :=
  repeat autounfold with unf_set_defs in *;
  destruct_products;
  intros;
  specialize_with E;
  autorewrite with rew_set_op_specs in *;
  intuition (subst *; auto).
