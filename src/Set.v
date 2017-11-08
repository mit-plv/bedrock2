
Class set(T E: Type) := mkSet {
  empty_set: T;
  singleton_set: E -> T;
  union: T -> T -> T;
  intersect: T -> T -> T;
  diff: T -> T -> T;
  contains: T -> E -> Prop;
}.

Notation "x '\in' s" := (contains s x) (at level 39, no associativity).

Instance Function_Set(E: Type): set (E -> Prop) E := {|
  empty_set := fun _ => False;
  singleton_set y := fun x => x = y;
  union := fun s1 s2 => fun x => s1 x \/ s2 x;
  intersect := fun s1 s2 => fun x => s1 x /\ s2 x;
  diff := fun s1 s2 => fun x => s1 x /\ ~ s2 x;
  contains := fun s => s
|}.
