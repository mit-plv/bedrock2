(* These lemmas can be useful when proving a refinement and induction over the
   statement rather than over its exec derivation is preferred *)

From Coq Require Import ZArith.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import bedrock2.Syntax bedrock2.Semantics.

Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.

  Definition refines(c2 c1: cmd) := forall functions t m l post,
      Semantics.exec.exec functions c1 t m l post ->
      Semantics.exec.exec functions c2 t m l post.

  Lemma refinement_while: forall test body1 body2,
      refines body2 body1 ->
      refines (cmd.while test body2) (cmd.while test body1).
  Proof.
    unfold refines. intros * R *.
    remember (cmd.while test body1) as c1. intros. revert Heqc1.
    induction H; intros; subst; inversion Heqc1; subst.
    - eapply Semantics.exec.while_false; eassumption.
    - eapply Semantics.exec.while_true; try eassumption.
      { unfold refines in R.
        eapply R. eassumption. }
      intros.
      eapply H3; eauto.
  Qed.

  Lemma refinement_seq: forall c1 c2 c1' c2',
      refines c1' c1 ->
      refines c2' c2 ->
      refines (cmd.seq c1' c2') (cmd.seq c1 c2).
  Proof.
    intros * R1 R2 functions t m l post H.
    unfold refines in *.
    inversion H. subst. clear H.
    eapply Semantics.exec.seq.
    - eapply R1. eassumption.
    - intros * Hmid. eapply R2. eauto.
  Qed.
End WithParams.
