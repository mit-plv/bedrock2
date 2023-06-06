Require Import coqutil.Map.Interface.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Lift1Prop.

Section WithMap.
  Context {key value: Type}{mem: map.map key value}.

  Definition is_emp(p: mem -> Prop)(q: Prop): Prop := impl1 p (emp q).

  Lemma weaken_is_emp(p: mem -> Prop)(q1 q2: Prop):
    (q1 -> q2) -> is_emp p q1 -> is_emp p q2.
  Proof. unfold is_emp, impl1, emp. intros. firstorder idtac. Qed.

  Lemma ex1_is_emp{T: Type}(p: T -> mem -> Prop)(q: T -> Prop):
    (forall x: T, is_emp (p x) (q x)) -> is_emp (ex1 p) (exists x: T, q x).
  Proof. unfold is_emp, impl1, emp, ex1. intros. firstorder idtac. Qed.

  Lemma use_is_emp: forall (p: mem -> Prop) (q: Prop) (m: mem),
      is_emp p q -> p m -> emp q m.
  Proof. unfold is_emp, impl1. eauto. Qed.
End WithMap.

Create HintDb is_emp.

#[export] Hint Resolve ex1_is_emp : is_emp.
