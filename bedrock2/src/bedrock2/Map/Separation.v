(*tag:importboilerplate*)
Require Import coqutil.Map.Interface bedrock2.Lift1Prop. Import map.

Section Sep.
  Context {key value} {map : map key value}.
  (*tag:spec*)
  Definition emp (P : Prop) := fun m => m = empty /\ P.
  Definition sep (p q : rep -> Prop) m :=
    exists mp mq, split m mp mq /\ p mp /\ q mq.
  Definition ptsto k v := fun m => m = put empty k v.
  Definition read k (P : value -> rep -> Prop) := (ex1 (fun v => sep (ptsto k v) (P v))).

  (*tag:lemma*)
  Fixpoint seps (xs : list (rep -> Prop)) : rep -> Prop :=
    match xs with
    | cons x nil => x
    | cons x xs => sep x (seps xs)
    | nil => emp True
    end.
  (*tag:importboilerplate*)
End Sep.
