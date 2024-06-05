Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import bedrock2.SepLib.
Require Import bedrock2.sepapp.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.HeapletwiseHyps.

Section WithMem.
  Context {width} {BW: Bitwidth width} {word: word width} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma cancel_sepapp_head{P Q: word -> mem -> Prop} a {sz: PredicateSize P} {Ps om Rest}:
      canceling (cons (P a) (cons (Q (word.add a (word.of_Z sz))) Ps)) om Rest ->
      canceling (cons (sepapp P Q a) Ps) om Rest.
  Proof.
    unfold sepapp, canceling. intros. destruct H as [H HR]. split; [intros | exact HR].
    simpl in *. subst om. destruct Ps as [ | R Rs]. 1: eauto.
    eapply sep_assoc. eauto.
  Qed.

  Lemma cancel_sepapps_cons_head: forall {P: word -> mem -> Prop} {sz l a Ps om Rest},
      canceling (cons (P a) (cons (sepapps l (word.add a (word.of_Z sz))) Ps)) om Rest ->
      canceling (cons (sepapps (cons (mk_sized_predicate P sz) l) a) Ps) om Rest.
  Proof.
    intros. rewrite sepapps_cons. eapply cancel_sep_head. assumption.
  Qed.

  Lemma cancel_sepapps_singleton_head: forall {P: word -> mem -> Prop} {sz a Ps om Rest},
      canceling (cons (P a) Ps) om Rest ->
      canceling (cons (sepapps (cons (mk_sized_predicate P sz) nil) a) Ps) om Rest.
  Proof.
    intros. rewrite sepapps_cons. rewrite sepapps_nil.
    eapply cancel_sep_head.
    simpl.
    unfold canceling in *.
    destruct H as [H HRest]. split; [ | apply HRest].
    intros. specialize (H _ H0). eapply seps'_iff1_seps. cbn.
    eapply seps'_iff1_seps in H. cbn in H.
    replace (sep (emp True) (seps' Ps)) with (seps' Ps). 1: assumption.
    eapply iff1ToEq.
    symmetry.
    eapply sep_emp_True_l.
  Qed.
End WithMem.

Ltac cancel_sepapps_step :=
  lazymatch goal with
  | |- canceling (cons (sepapps (cons _ nil) _) _) _ _ =>
      eapply cancel_sepapps_singleton_head
  | |- canceling (cons (sepapps (cons _ _) _) _) _ _ =>
      eapply cancel_sepapps_cons_head
  | |- canceling (cons (sepapp _ _ _) _) _ _ =>
      eapply cancel_sepapp_head
  end.
