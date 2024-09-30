Section FixPoint.

Variable A : Type.
Variable R : A -> A -> Prop.
Hypothesis Rwf : well_founded R.
Variable P : A -> Type.
Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.

Hypothesis F_ext :
  (forall (x : A) (f g : forall y : A, R y x -> P y),
      (forall (y : A) (p1 p2 : R y x), f y p1 = g y p2) -> F x f = F x g).

Lemma Fix_F_inv' : 
  forall (x : A) (r s : Acc R x), Fix_F P F r = Fix_F P F s.
Proof.
  intros x. induction (Rwf x). intros r s.
  rewrite <- Fix_F_eq. rewrite <- Fix_F_eq. apply F_ext. auto.
Qed.

Lemma Fix_eq' :
  forall x : A, Fix Rwf P F x = F x (fun (y : A) (_ : R y x) => Fix Rwf P F y).
Proof.
  intros. unfold Fix. rewrite <- Fix_F_eq.
  apply F_ext. intros. apply Fix_F_inv'.
Qed.

End FixPoint.

Check Fix_eq.
Definition type_of_Fix_eq :=
  forall (A : Type) (R : A -> A -> Prop) (Rwf : well_founded R) 
    (P : A -> Type) (F : forall x : A, (forall y : A, R y x -> P y) -> P x),
    (forall (x : A) (f g : forall y : A, R y x -> P y),
        (forall (y : A) (p : R y x), f y p = g y p) -> F x f = F x g) ->
    forall x : A, Fix Rwf P F x = F x (fun (y : A) (_ : R y x) => Fix Rwf P F y).

Check Fix_eq'.
Definition type_of_Fix_eq' :=
  forall (A : Type) (R : A -> A -> Prop) (Rwf : well_founded R) 
    (P : A -> Type) (F : forall x : A, (forall y : A, R y x -> P y) -> P x),
    (forall (x : A) (f g : forall y : A, R y x -> P y),
        (forall (y : A) (p1 p2 : R y x), f y p1 = g y p2) -> F x f = F x g) ->
    forall x : A, Fix Rwf P F x = F x (fun (y : A) (_ : R y x) => Fix Rwf P F y).
                               
Goal type_of_Fix_eq' -> type_of_Fix_eq.
  cbv [type_of_Fix_eq type_of_Fix_eq']. auto. Qed.




(*did jason do this already?  should explore
  https://github.com/mit-plv/fiat/blob/master/src/Common/Wf1.v*)
(*almost copied verbatim from the standard library*)
(*allows for general recursion where one argument to recursive function is a function, without using funext axiom *)
Section FixPoint.

Variable A : Type.
Variable R : A -> A -> Prop.
Hypothesis Rwf : well_founded R.
Variable P : Type. (* really I want to say that P gives one type for each equivalence class
                      of A wrt the equivalence relation E.  Not clear how to say this though.*)
Variable F : forall x:A, (forall y:A, R y x -> P) -> P.
Variable E1 : A -> A -> Prop.
Variable E2 : P -> P -> Prop.

(* No need to make this my own thing; should just use Fix_F and assume it's non-dependent.*)
Fixpoint my_Fix_F (x:A) (a:Acc R x) : P :=
  F x (fun (y:A) (h:R y x) => my_Fix_F y (Acc_inv a h)).

Scheme Acc_inv_dep := Induction for Acc Sort Prop.

Lemma my_Fix_F_eq (x:A) (r:Acc R x) :
  F x (fun (y:A) (p:R y x) => my_Fix_F y (Acc_inv r p)) = my_Fix_F x r.
Proof.
  destruct r using Acc_inv_dep; auto.
Qed.

Definition my_Fix (x:A) := my_Fix_F x (Rwf x).

(** Proof that [well_founded_induction] satisfies the fixpoint equation.
    It requires an extra property of the functional *)

Hypothesis
  F_ext :
  forall (x1 x2:A) (f1:forall y:A, R y x1 -> P) (f2:forall y:A, R y x2 -> P),
    E1 x1 x2 ->
    (forall (y1 y2:A) (p1:R y1 x1) (p2:R y2 x2),
        E1 y1 y2 -> E2 (f1 y1 p1) (f2 y2 p2)) -> E2 (F x1 f1) (F x2 f2).

Lemma my_Fix_F_inv : forall (x1 x2:A) (r1:Acc R x1) (r2:Acc R x2),
    E1 x1 x2 -> E2 (my_Fix_F x1 r1) (my_Fix_F x2 r2).
Proof.
  intro x1; induction (Rwf x1); intros x2 r1 r2.
  rewrite <- (my_Fix_F_eq x r1); rewrite <- (my_Fix_F_eq x2 r2); intros.
  apply F_ext; auto.
Qed.

Lemma my_Fix_eq : forall (x1 x2:A),
    E1 x1 x2 -> E2 (my_Fix x1) (F x2 (fun (y:A) (p:R y x2) => my_Fix y)).
Proof.
  intro x; unfold my_Fix.
  rewrite <- my_Fix_F_eq.
  intros. apply F_ext; intros.
  - assumption.
  - apply my_Fix_F_inv. assumption.
Qed.

End FixPoint.

Require Import bedrock2.Semantics.
Require Import compiler.FlatImp.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Init.Wf Relation_Operators Wellfounded.
Require Import riscv.Utility.Utility.

Section WithWord.
  Context {var : Type} {width} {BW: Bitwidth width} {word: word.word width}.
  
  Definition lt_tuple' : nat * stmt var -> nat * stmt var -> Prop := slexprod _ _ lt stmt_lt.
  
  Lemma lt_tuple'_wf : well_founded lt_tuple'.
  Proof.
    apply wf_slexprod.
    - apply lt_wf.
    - apply wf_stmt_lt.
  Defined.
  
  Definition Let_In_pf_nd {A B} (x : A) (f : forall a : A, a = x -> B) : B := let y := x in f y eq_refl.
  
  Lemma Let_In_pf_nd_ext {A B} (E : B -> B -> Prop) (x : A) (f1 f2 : forall a : A, a = x -> B) :
    (forall x1 x2, E (f1 x1 x2) (f2 x1 x2)) ->
    E (Let_In_pf_nd x f1) (Let_In_pf_nd x f2).
  Proof. intros. cbv [Let_In_pf_nd]. apply H. Qed.
End WithWord.
