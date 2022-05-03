Require Import Coq.Classes.Morphisms.

Section Binary.
  Context {T: Type} (P Q: T -> Prop).
  Definition impl1 := forall x, P x -> Q x.
  Definition iff1 := forall x, P x <-> Q x.
  Definition and1 := fun x => P x /\ Q x.
  Definition or1 := fun x => P x \/ Q x.
End Binary.

Definition ex1 {A B} (P : A -> B -> Prop) := fun (b:B) => exists a:A, P a b.

Global Instance Transitive_impl1 T : Transitive (@impl1 T). firstorder idtac. Qed.
Global Instance Reflexive_impl1 T : Reflexive (@impl1 T). firstorder idtac. Qed.
Global Instance Proper_impl1_impl1 T : Proper (Basics.flip impl1 ==> impl1 ==> Basics.impl) (@impl1 T). firstorder idtac. Qed.
Global Instance subrelation_iff1_impl1 T : subrelation (@iff1 T) (@impl1 T). firstorder idtac. Qed.
Global Instance Equivalence_iff1 T : Equivalence (@iff1 T). firstorder idtac. Qed.
Global Instance Proper_iff1_iff1 T : Proper (iff1 ==> iff1 ==> iff) (@iff1 T). firstorder idtac. Qed.
Global Instance Proper_iff1_impl1 T : Proper (Basics.flip impl1 ==> impl1 ==> Basics.impl) (@impl1 T). firstorder idtac. Qed.
Global Instance Proper_impl1_iff1 T : Proper (iff1 ==> iff1 ==> iff) (@impl1 T). firstorder idtac. Qed.
Global Instance Proper_ex1_iff1 A B : Proper (pointwise_relation _ iff1 ==> iff1) (@ex1 A B). firstorder idtac. Qed.
Global Instance Proper_ex1_impl1 A B : Proper (pointwise_relation _ impl1 ==> impl1) (@ex1 A B). firstorder idtac. Qed.
Global Instance iff1_rewrite_relation T : RewriteRelation (@iff1 T) := {}.

Lemma impl1_ex1_l {A B} p q : impl1 (@ex1 A B p) q <-> (forall x, impl1  (p x) q).
Proof. firstorder idtac. Qed.
Lemma impl1_ex1_r {A B} p q x : impl1 p (q x) -> impl1 p (@ex1 A B q).
Proof. firstorder idtac. Qed.
