From Coq Require Import PropExtensionality FunctionalExtensionality.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation.

Section PurifyLemmas.
  Context{key value: Type} {mem: map.map key value}.

  Definition purify(R: mem -> Prop)(P: Prop): Prop := forall m, R m -> P.

  Lemma purify_sep: forall {RHead RTail: mem -> Prop} {PHead PTail: Prop},
      purify RHead PHead ->
      purify RTail PTail ->
      purify (sep RHead RTail) (PHead /\ PTail).
  Proof. unfold purify, sep. intros. fwd. eauto. Qed.

  Lemma purify_sep_skip_l: forall {RHead RTail: mem -> Prop} {PTail: Prop},
      purify RTail PTail ->
      purify (sep RHead RTail) PTail.
  Proof. unfold purify, sep. intros. fwd. eauto. Qed.

  Lemma purify_sep_skip_r: forall {RHead RTail: mem -> Prop} {PHead: Prop},
      purify RHead PHead ->
      purify (sep RHead RTail) PHead.
  Proof. unfold purify, sep. intros. fwd. eauto. Qed.

  Lemma assume_pure_of_sides_of_iff1: forall (P Q: mem -> Prop) (pureP pureQ: Prop),
      purify P pureP ->
      purify Q pureQ ->
      (pureP \/ pureQ -> Lift1Prop.iff1 P Q) ->
      iff1 P Q.
  Proof.
    unfold purify. intros. split; intros; apply H1; eauto.
  Qed.

  Lemma assume_pure_of_sides_of_sep_eq: forall (P Q: mem -> Prop) (pureP pureQ: Prop),
      purify P pureP ->
      purify Q pureQ ->
      (pureP \/ pureQ -> P = Q) ->
      P = Q.
  Proof.
    unfold purify. intros. extensionality x. eapply propositional_extensionality.
    split; intros.
    - rewrite <- H1; eauto.
    - rewrite -> H1; eauto.
  Qed.

  Lemma purify_emp: forall (P: Prop), purify (emp P) P.
  Proof. unfold purify, emp. intros * (_ & ?). assumption. Qed.

  Lemma purify_eq: forall m: mem, purify (eq m) True.
  Proof. unfold purify. intros. constructor. Qed.
End PurifyLemmas.

Create HintDb purify. (* To register lemmas concluding `purify P pureP` *)

#[export] Hint Resolve purify_emp purify_eq : purify.

Ltac purify_rec :=
  lazymatch goal with
  | |- purify ?clause ?E =>
      is_evar E;
      lazymatch clause with
      | sep ?R1 ?R2 =>
          is_evar E;
          let HLeft := fresh in
          let HRight := fresh in
          tryif (eassert (purify R1 _) as HLeft by purify_rec) then
            tryif (eassert (purify R2 _) as HRight by purify_rec) then
              exact (purify_sep HLeft HRight)
            else
              refine (purify_sep_skip_r HLeft)
          else
            tryif (eassert (purify R2 _) as HRight by purify_rec) then
              exact (purify_sep_skip_l HRight)
            else
              fail "cannot purify" clause
      | _ => solve [eauto with purify]
      end
  | |- _ => fail "goal should be of form 'purify _ _'"
  end.

Ltac purify_hyp H :=
  lazymatch type of H with
  | ?R ?m => let HP := fresh H "P" in eassert (purify R _) as HP;
             [ purify_rec | specialize (HP m H) ]
  end.

Ltac purify :=
  lazymatch goal with
  | H: sep _ _ _ |- _ => purify_hyp H
  end.

Require Import bedrock2.SuppressibleWarnings.

Inductive cannot_purify{mem: Type}(pred: mem -> Prop): Set :=
  mk_cannot_purify.

Notation "'(purify'  pred  '_)'  'cannot'  'be'  'solved'  'by'  'eauto' 'with' 'purify'" :=
  (cannot_purify pred)
  (at level 1, pred at level 9, only printing)
  : message_scope.
