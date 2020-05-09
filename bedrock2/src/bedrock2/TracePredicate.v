Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.ReversedListNotations.

Section ListPred.
  Context {T: Type}.

  Definition constraint (P : Prop): list T -> Prop := fun _ => P.

  Definition one(t: T): list T -> Prop := eq [t].

  Definition any : list T -> Prop := fun _ => True.

  Definition concat(P1 P2: list T -> Prop): list T -> Prop :=
    fun l => exists l1 l2, l = l1 ;++ l2 /\ P1 l1 /\ P2 l2.

  Definition choice(P1 P2: list T -> Prop): list T -> Prop :=
    fun l => P1 l \/ P2 l.

  Section WithP.
    Context (P : list T -> Prop).

    Inductive kleene: list T -> Prop :=
      | kleene_empty:
          kleene nil
      | kleene_step: forall l1 l2,
          P l1 ->
          kleene l2 ->
          kleene (l1 ;++ l2).

    Fixpoint multiple (n:nat) : list T -> Prop :=
      match n with
      | O => eq nil
      | S n => concat P (multiple n)
      end.

    Lemma kleene_multiple n xs
      (H : multiple n xs) : kleene xs.
    Proof.
      revert dependent xs; induction n; intros.
      { cbn in H; subst; constructor. }
      destruct H as (?&?&?&?&?); subst.
      constructor; eauto.
    Qed.
  End WithP.

  (* more powerful than regex: *)

  Definition both(P1 P2: list T -> Prop): list T -> Prop :=
    fun l => P1 l /\ P2 l.

  Definition existsl{A: Type}(P: A -> list T -> Prop): list T -> Prop :=
    fun l => exists a, P a l.

  Lemma concat_app (P Q : list T->Prop) x y (HP : P x) (HQ : Q y) : concat P Q (y ++ x).
  Proof. cbv [concat]; eauto. Qed.

  Lemma kleene_app P xs (Hxs : kleene P xs) ys (Hys : kleene P ys)
    : kleene P (xs ++ ys).
  Proof.
    revert dependent xs; induction Hys; eauto; intros;
      rewrite ?List.app_nil_r, ?List.app_assoc;
      try constructor; eauto.
  Qed.

  Lemma concat_kleene_r_app (P Q:_->Prop) a b :
    Q b ->
    (concat P (kleene Q)) a ->
    (concat P (kleene Q)) (b ++ a).
  Proof.
    intros ? (?&?&?&?&?); subst.
    rewrite app_assoc.
    eapply concat_app, kleene_app; eauto.
    rewrite <-app_nil_l; eauto using kleene_step, kleene_empty.
  Qed.

  Import Morphisms.
  Local Infix "+++" := concat (at level 60).

  Global Instance Proper_concat : Proper (pointwise_relation _ iff ==> pointwise_relation _ iff ==> pointwise_relation _ iff) concat.
  Proof. cbv [Proper respectful pointwise_relation] in *; firstorder idtac. Qed.
  Global Instance Proper_multiple : Proper (pointwise_relation _ iff ==> pointwise_relation _ (pointwise_relation _ iff)) multiple.
  Proof.
    intros ? ? ? n. induction n; cbn [multiple]; [reflexivity|].
    eapply Proper_concat; trivial.
  Qed.

  Lemma concat_nil_r P : pointwise_relation _ iff (P +++ eq []) P.
  Proof.
    cbv [pointwise_relation]; firstorder idtac; subst; eauto.
    exists a, nil; intuition idtac; eauto.
  Qed.
  Lemma concat_nil_l P : pointwise_relation _ iff (eq [] +++ P) P.
  Proof.
    cbv [pointwise_relation]; firstorder idtac; subst; rewrite ?app_nil_r; eauto.
    exists nil, a; intuition idtac; rewrite ?app_nil_r; eauto.
  Qed.
  Lemma concat_assoc P Q R : pointwise_relation _ iff ((P +++ Q) +++ R) (P +++ (Q+++R)).
  Proof.
    cbv [pointwise_relation concat]. firstorder idtac; subst; eexists _, _;
      split; [ |split; eauto]; eauto using app_assoc.
  Qed.

  Lemma any_app_more : forall P (x y : list T), (any +++ P) x -> (any +++ P) (x ++ y).
  Proof.
    intros.
    cbv [any] in *.
    destruct H as (?&?&?&?&?); subst.
    rewrite <-app_assoc.
    eapply concat_app; eauto.
  Qed.

  Lemma multiple_assoc P n :
    pointwise_relation _ iff (P +++ multiple P n) (multiple P n +++ P).
  Proof.
    induction n; cbn [multiple];
      rewrite ?concat_assoc, ?concat_nil_l, ?concat_nil_r, ?IHn;
      reflexivity.
  Qed.

  Lemma  multiple_expand_right : forall P n xs,
    @multiple P (S n) xs <-> concat (multiple P n) P xs.
  Proof. cbn; intros; eapply multiple_assoc. Qed.

End ListPred.

Module TracePredicateNotations.
  Notation "P ^*" := (kleene P) (at level 50).
  Notation "P ^+" := (concat P (kleene P)) (at level 50).
  Infix "+++" := concat (at level 60).
  Infix "|||" := choice (at level 70).
  Notation "'EX' x .. y , p" := (existsl (fun x => .. (existsl (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'EX'  '/  ' x  ..  y ,  '/  ' p ']'").
End TracePredicateNotations.
