Module Type LEARNING.
  Parameter Learnt: Prop -> Prop.
  Parameter markLearnt: forall {P: Prop} (p: P), Learnt P.
End LEARNING.

Module Import Learning: LEARNING.
  Definition Learnt(P: Prop) := P.
  Definition markLearnt{P: Prop}(p: P): Learnt P := p.
End Learning.

Ltac learn_tac p H :=
  let P := type of p in
  lazymatch goal with
  | H: Learnt P |- _ => fail
  | |- _ =>
    let L := fresh "L" in
    pose proof (markLearnt p) as L; (* will stay around *)
    pose proof p as H (* will likely be destructed *)
  end.

Tactic Notation "learn" constr(p) := let H := fresh in learn_tac p H.
Tactic Notation "learn" constr(p) "as" ident(H) := learn_tac p H.

Ltac cheap_saturate :=
  unshelve (repeat match goal with
    | H: _ /\ _ |- _ => let Hl := fresh H "l" in let Hr := fresh H "r" in destruct H as [Hl Hr]
    | E: exists y, _ |- _ => let yf := fresh y in destruct E as [yf E]
    | H: forall (x: ?T), _ |- _ =>
      match type of T with
      | Prop => fail 1
      | _ => let x' := fresh x in (evar (x': T)); specialize (H x'); subst x'
      end
    | H1: _, H2: _ -> _ |- _ => let H3 := fresh H1 "_" H2 in learn (H2 H1) as H3
  end);
  [(eauto || exact unit)..|].
