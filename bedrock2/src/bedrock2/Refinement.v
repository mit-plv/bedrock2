(* These lemmas can be useful when proving a refinement and induction over the
   statement rather than over its exec derivation is preferred *)

Require Import Coq.ZArith.ZArith.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import bedrock2.Syntax bedrock2.Semantics.

Section WithParams.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.

  Definition refinement(c1 c2: cmd) := forall functions t m l post,
      Semantics.exec.exec functions c1 t m l post ->
      Semantics.exec.exec functions c2 t m l post.

  Lemma refinement_while: forall test body1 body2,
      refinement body1 body2 ->
      refinement (cmd.while test body1) (cmd.while test body2).
  Proof.
    unfold refinement. intros * R *.
    remember (cmd.while test body1) as c1. intros. revert Heqc1.
    induction H; intros; subst; inversion Heqc1; subst.
    - eapply Semantics.exec.while_false; eassumption.
    - eapply Semantics.exec.while_true; try eassumption.
      { unfold refinement in R.
        eapply R. eassumption. }
      intros.
      eapply H3; eauto.
  Qed.

  Lemma refinement_seq: forall c1 c2 c1' c2',
      refinement c1 c1' ->
      refinement c2 c2' ->
      refinement (cmd.seq c1 c2) (cmd.seq c1' c2').
  Proof.
    intros * R1 R2 functions t m l post H.
    unfold refinement in *.
    inversion H. subst. clear H.
    eapply Semantics.exec.seq.
    - eapply R1. eassumption.
    - intros * Hmid. eapply R2. eauto.
  Qed.
End WithParams.
