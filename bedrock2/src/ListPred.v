Require Import Coq.Lists.List. Import ListNotations.

Section ListPred.
  Context {T: Type}.

  Definition constraint (P : Prop): list T -> Prop := fun _ => P.

  Definition one(t: T): list T -> Prop := eq [t].

  Definition concat(P1 P2: list T -> Prop): list T -> Prop :=
    fun l => exists l1 l2, l = l1 ++ l2 /\ P1 l1 /\ P2 l2.

  Definition choice(P1 P2: list T -> Prop): list T -> Prop :=
    fun l => P1 l \/ P2 l.

  Inductive kleene(P: list T -> Prop): list T -> Prop :=
  | kleene_empty:
      kleene P nil
  | kleene_step: forall l1 l2,
      P l1 ->
      kleene P l2 ->
      kleene P (l1 ++ l2).

  (* more powerful than regex: *)

  Definition both(P1 P2: list T -> Prop): list T -> Prop :=
    fun l => P1 l /\ P2 l.

  Definition existsl{A: Type}(P: A -> list T -> Prop): list T -> Prop :=
    fun l => exists a, P a l.

End ListPred.

Module ListPredNotations.
  Notation "P ^*" := (kleene P) (at level 50).
  Notation "P ^+" := (concat P (kleene P)) (at level 50).
  Infix "+++" := concat (at level 60).
  Infix "|||" := choice (at level 70).
End ListPredNotations.
