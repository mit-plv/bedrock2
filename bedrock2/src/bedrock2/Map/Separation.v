Require Import coqutil.Map.Interface bedrock2.Lift1Prop. Import map.

Section Sep.
  Context {key value} {map : map key value}.
  Definition emp (P : Prop) := fun m : map => m = empty /\ P.
  Definition sep (p q : map -> Prop) m :=
    exists mp mq, split m mp mq /\ p mp /\ q mq.
  Definition ptsto k v := fun m : map => m = put empty k v.
  Definition read k (P : value -> rep -> Prop) := (ex1 (fun v => sep (ptsto k v) (P v))).

  Fixpoint seps (xs : list (rep -> Prop)) : rep -> Prop :=
    match xs with
    | cons x nil => x
    | cons x xs => sep x (seps xs)
    | nil => emp True
    end.
End Sep.

Declare Scope sep_scope.
Delimit Scope sep_scope with sep.
Infix "*" := sep (at level 40, left associativity) : sep_scope.
Infix "⋆" := sep (at level 40, left associativity) : sep_scope.
