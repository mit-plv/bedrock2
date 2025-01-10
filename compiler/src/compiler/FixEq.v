(* In this file, we prove various strengthenings of Fix_eq.
   Most of the file is nearly-verbatim copied from the stdlib file where Fix_eq is proven.
   The main goal is to get general recursion even when some arguments to the recursive function is a function (without using funext). *)

(*Here we have, supposedly, maximum generality: dependent types and arbitrary relations*)
Section GeneralFixPoint.
  Variable A : Type.
  Variable R : A -> A -> Prop.
  Hypothesis Rwf : well_founded R.
  Variable P : A -> Type.
  Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.
  Variable E1 : A -> A -> Prop.
  Variable E2 : forall {a1 a2}, P a1 -> P a2 -> Prop.

  Let Fix_F := @Fix_F A R P F.

  Lemma Fix_F_eq' (x:A) (r:Acc R x) :
    F x (fun (y:A) (p:R y x) => Fix_F y (Acc_inv r p)) = Fix_F x r.
  Proof.
    destruct r using Acc_inv_dep; auto.
  Qed.

  Let Fix := @Fix A R Rwf P F.

  Hypothesis
    F_ext :
    forall (x1 x2:A) (f1:forall y:A, R y x1 -> P y) (f2:forall y:A, R y x2 -> P y),
      E1 x1 x2 ->
      (forall (y1 y2:A) (p1:R y1 x1) (p2:R y2 x2),
          E1 y1 y2 -> E2 (f1 y1 p1) (f2 y2 p2)) -> E2 (F x1 f1) (F x2 f2).

  Lemma Fix_F_inv' : forall (x1 x2:A) (r1:Acc R x1) (r2:Acc R x2),
      E1 x1 x2 -> E2 (Fix_F x1 r1) (Fix_F x2 r2).
  Proof.
    intro x1; induction (Rwf x1); intros x2 r1 r2.
    rewrite <- (Fix_F_eq' x r1); rewrite <- (Fix_F_eq' x2 r2); intros.
    apply F_ext; auto.
  Qed.

  Lemma Fix_eq' : forall (x1 x2:A),
      E1 x1 x2 -> E2 (Fix x1) (F x2 (fun (y:A) (p:R y x2) => Fix y)).
  Proof.
    intro x; unfold Fix, Wf.Fix.
    rewrite <- Fix_F_eq'.
    intros. apply F_ext; intros.
    - assumption.
    - apply Fix_F_inv'. assumption.
  Qed.
End GeneralFixPoint.

(*Here we have arbitrary relations but no dependent types.*)
Section NonDepFixPoint.
  Variable A : Type.
  Variable R : A -> A -> Prop.
  Hypothesis Rwf : well_founded R.
  Variable P : Type.
  Variable F : forall x:A, (forall y:A, R y x -> P) -> P.
  Variable E1 : A -> A -> Prop.
  Variable E2 : P -> P -> Prop.

  Hypothesis
    F_ext :
    forall (x1 x2:A) (f1:forall y:A, R y x1 -> P) (f2:forall y:A, R y x2 -> P),
      E1 x1 x2 ->
      (forall (y1 y2:A) (p1:R y1 x1) (p2:R y2 x2),
          E1 y1 y2 -> E2 (f1 y1 p1) (f2 y2 p2)) -> E2 (F x1 f1) (F x2 f2).

  Definition Fix_eq'_nondep := Fix_eq' A R Rwf (fun _ => P) F E1 (fun _ _ => E2) F_ext.
End NonDepFixPoint.

(*Here we have dependent types but the relations are eq.
  Sadly we can't simply deduce these lemmas from the supposedly-general case,
  since there's no good way of instantiating E2 to get eq.*)
Section EqualityFixPoint.
  Variable A : Type.
  Variable R : A -> A -> Prop.
  Hypothesis Rwf : well_founded R.
  Variable P : A -> Type.
  Variable F : forall x:A, (forall y:A, R y x -> P y) -> P x.

  Hypothesis F_ext :
    (forall (x : A) (f g : forall y : A, R y x -> P y),
        (forall (y : A) (p1 p2 : R y x), f y p1 = g y p2) -> F x f = F x g).

  Lemma Fix_F_inv'_eq : 
    forall (x : A) (r s : Acc R x), Fix_F P F r = Fix_F P F s.
  Proof.
    intros x. induction (Rwf x). intros r s.
    rewrite <- Fix_F_eq. rewrite <- Fix_F_eq. apply F_ext. auto.
  Qed.

  (*Fix_eq'_eq has the same generality as Fix_eq, but it's a bit stronger
    (and often more convenient).
    For instance, auto can prove that Fix_eq'_eq implies Fix_eq, but it can't prove
    the converse.*)
  Lemma Fix_eq'_eq :
    forall x : A, Fix Rwf P F x = F x (fun (y : A) (_ : R y x) => Fix Rwf P F y).
  Proof.
    intros. unfold Fix. rewrite <- Fix_F_eq.
    apply F_ext. intros. apply Fix_F_inv'_eq.
  Qed.
End EqualityFixPoint.

Section EqualityNonDepFixPoint.
  Variable A : Type.
  Variable R : A -> A -> Prop.
  Hypothesis Rwf : well_founded R.
  Variable P : Type.
  Variable F : forall x:A, (forall y:A, R y x -> P) -> P.

  Hypothesis F_ext :
    (forall (x : A) (f g : forall y : A, R y x -> P),
        (forall (y : A) (p1 p2 : R y x), f y p1 = g y p2) -> F x f = F x g).

  Definition Fix_eq'_eq_nondep := Fix_eq'_eq A R Rwf (fun _ => P) F F_ext.
End EqualityNonDepFixPoint.

(*the rest of this file is random things that are useful sometimes
  for writing recursive functions*)

Definition Let_In_pf_nd {A B} (x : A) (f : forall a : A, a = x -> B) : B := let y := x in f y eq_refl.
  
Lemma Let_In_pf_nd_ext {A B} (E : B -> B -> Prop) (x : A) (f1 f2 : forall a : A, a = x -> B) :
  (forall x1 x2, E (f1 x1 x2) (f2 x1 x2)) ->
  E (Let_In_pf_nd x f1) (Let_In_pf_nd x f2).
Proof. intros H. cbv [Let_In_pf_nd]. apply H. Qed.

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
End WithWord.
