Require Import bedrock2.Map bedrock2.Lift1Prop. Import map.

Section Sep.
  Context {key value} {map : map key value}.
  Definition emp (P : Prop) := fun m => m = empty /\ P.
  Definition sep (p q : rep -> Prop) m :=
    exists mp mq, split m mp mq /\ p mp /\ q mq.
  Definition ptsto k v := fun m => m = put empty k v.
  Definition read k (P : value -> rep -> Prop) := (ex1 (fun v => sep (ptsto k v) (P v))).
End Sep.