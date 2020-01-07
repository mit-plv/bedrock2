Require Coq.Init.Notations.
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False := .
End LocalFalse.
Axiom proof_admitted : False.
Import Coq.Init.Notations.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Require Top.bedrock2.src.bedrock2.WeakestPrecondition.
(* -*- mode: coq; coq-prog-args: ("-emacs" "-Q" "./bedrock2/src/bedrock2" "bedrock2" "-Q" "deps/coqutil/src/coqutil" "coqutil" "-top" "WeakestPreconditionProperties") -*- *)
(* File reduced by coq-bug-finder from original input, then from 152 lines to 149 lines *)
(* coqc version 8.12+alpha (December 2019) compiled on Dec 31 2019 9:59:24 with OCaml 4.09.0
   coqtop version samsdell:/home/sam/installs/coqmaster/coq,master (37254871c8e5ece576af7efddc20a9ed7f197e04) *)
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
Import coqutil.Macros.unique.
Import Coq.Classes.Morphisms.

Section WeakestPrecondition.
  Context {p : unique! Semantics.parameters}.

  Ltac ind_on X :=
    intros;
    repeat match goal with x : ?T |- _ => first [ constr_eq T X; move x at top | revert x ] end;
    match goal with x : X |- _ => induction x end;
    intros.

  Global Instance Proper_literal : Proper (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)) WeakestPrecondition.literal.
admit.
Defined.

  Global Instance Proper_get : Proper (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))) WeakestPrecondition.get.
admit.
Defined.

  Global Instance Proper_load : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) WeakestPrecondition.load.
admit.
Defined.

  Global Instance Proper_store : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))))) WeakestPrecondition.store.
admit.
Defined.

  Global Instance Proper_expr : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) WeakestPrecondition.expr.
admit.
Defined.

  Global Instance Proper_list_map {A B} :
    Proper ((pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) ==> pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) (WeakestPrecondition.list_map (A:=A) (B:=B)).
admit.
Defined.

  Context {p_ok : Semantics.parameters_ok p}.
  Global Instance Proper_cmd :
    Proper (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ (pointwise_relation _ Basics.impl))) ==> Basics.impl)))) ==>
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl))) ==>
     Basics.impl)))))) WeakestPrecondition.cmd.
  Proof.
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl]; ind_on Syntax.cmd.cmd;
      cbn in *; cbv [dlet.dlet] in *; intuition (try typeclasses eauto with core).
    {
 destruct H1 as (?&?&?).
eexists.
split.
      1: eapply Proper_expr.
      1: cbv [pointwise_relation Basics.impl]; intuition eauto 2.
      all: eauto.
}
    {
 destruct H1 as (?&?&?).
eexists.
split.
      {
 eapply Proper_expr.
        {
 cbv [pointwise_relation Basics.impl]; intuition eauto 2.
}
        {
 eauto.
}
 }
      {
 destruct H2 as (?&?&?).
eexists.
split.
        {
 eapply Proper_expr.
          {
 cbv [pointwise_relation Basics.impl]; intuition eauto 2.
}
          {
 eauto.
}
 }
        {
 eapply Proper_store; eauto; cbv [pointwise_relation Basics.impl]; eauto.
}
 }
 }
    {
 destruct H1 as (?&?&?).
eexists.
split.
      {
 eapply Proper_expr.
        {
 cbv [pointwise_relation Basics.impl]; intuition eauto 2.
}
        {
 eauto.
}
 }
      {
 intuition eauto 6.
}
 }
    {
 destruct H1 as (?&?&?&?&?&HH).
      eassumption || eexists.
      eassumption || eexists.
      eassumption || eexists.
      eassumption || eexists.
{
 eassumption || eexists.
}
      eassumption || eexists.
{
 eassumption || eexists.
}
      intros X Y Z T W.
      specialize (HH X Y Z T W).
      destruct HH as (?&?&?).
eexists.
split.
      1: eapply Proper_expr.
      1: cbv [pointwise_relation Basics.impl].
      all:intuition eauto 2.
      -
 eapply H2; eauto; cbn; intros.
        match goal with H:_ |- _ => destruct H as (?&?&?); solve[eauto] end.
      -
 intuition eauto.
}
    {
 destruct H1 as (?&?&?).
eexists.
split.
      {
 eapply Proper_list_map; eauto; try exact H4; cbv [respectful pointwise_relation Basics.impl]; intuition eauto 2.
        eapply Proper_expr; eauto.
}
      {
 eapply H; eauto.
Timeout 10 firstorder eauto.
