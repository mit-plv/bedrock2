Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.fwd.
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

  (* note: not added to the is_emp db, because usually we first destruct all seps *)
  Lemma sep_is_emp{ok: map.ok mem}: forall (P: mem -> Prop) P' (Q: mem -> Prop) Q',
      is_emp P P' ->
      is_emp Q Q' ->
      is_emp (sep P Q) (P' /\ Q').
  Proof.
    unfold is_emp, impl1, sep, emp. intros. fwd.
    specialize (H _ H1p1).
    specialize (H0 _ H1p2).
    fwd. subst.
    unfold map.split in *. apply proj1 in H1p0.
    unfold map.putmany in *.
    rewrite map.fold_empty in *.
    auto.
  Qed.

  Lemma use_is_emp: forall (p: mem -> Prop) (q: Prop) (m: mem),
      is_emp p q -> p m -> emp q m.
  Proof. unfold is_emp, impl1. eauto. Qed.
End WithMap.

Create HintDb is_emp.

#[export] Hint Resolve ex1_is_emp : is_emp.
