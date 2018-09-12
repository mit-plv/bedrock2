Require Import bedrock2.Macros.
Require bedrock2.WeakestPrecondition.

Require Import Coq.Classes.Morphisms.

Inductive Roption {T} : option T -> option T -> Prop :=
| Rnone {x} : Roption None x
| Rsome {x} : Roption (Some x) (Some x).

Global Instance Reflexive_Roption {T} : Reflexive (@Roption T).
Proof. compute. destruct x; constructor. Qed.

Global Instance Transitive_Roption {T} : Transitive (@Roption T).
Proof. compute. destruct 1; inversion 1; subst; auto. constructor. Qed.

Section WeakestPrecondition.
  Context {p : unique! Semantics.parameters}.

  Ltac ind_on X :=
    intros;
    repeat match goal with x : ?T |- _ => first [ constr_eq T X; move x at top | revert x ] end;
    match goal with x : X |- _ => induction x end;
    intros.

  Global Instance Proper_literal : Proper (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)) WeakestPrecondition.literal.
  Proof. cbv [WeakestPrecondition.literal]; cbv [Proper respectful pointwise_relation Basics.impl]; firstorder idtac. Qed.

  Global Instance Proper_get : Proper (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))) WeakestPrecondition.get.
  Proof. cbv [WeakestPrecondition.get]; cbv [Proper respectful pointwise_relation Basics.impl]; firstorder idtac. Qed.

  Global Instance Proper_global : Proper ((pointwise_relation _ Roption) ==> (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))) WeakestPrecondition.global.
  Proof.
    cbv [WeakestPrecondition.global]; cbv [Proper respectful pointwise_relation Basics.impl]; firstorder idtac.
    destruct (H a); try congruence.
    injection H1; clear H1; intros; subst.
    eexists; split; eauto.
  Qed.

  Global Instance Proper_load : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) WeakestPrecondition.load.
  Proof. cbv [WeakestPrecondition.load]; cbv [Proper respectful pointwise_relation Basics.impl]; firstorder idtac. Qed.

  Global Instance Proper_store : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))))) WeakestPrecondition.store.
  Proof. cbv [WeakestPrecondition.load]; cbv [Proper respectful pointwise_relation Basics.impl]; firstorder idtac. Qed.

  Global Instance Proper_expr
  : Proper (pointwise_relation _ Roption ==> (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))))) WeakestPrecondition.expr.
  Proof.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on Syntax.expr.expr;
      cbn in *; intuition (try typeclasses eauto with core).
    eapply Proper_literal; eauto.
    eapply Proper_get; eauto.
    eapply Proper_global; eauto.
    { eapply IHa1; eauto; intuition idtac. eapply Proper_load; eauto using Proper_load. }
  Qed.

  Global Instance Proper_list_map {A B} :
    Proper ((pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) ==> pointwise_relation _ (pointwise_relation _ Basics.impl ==> Basics.impl)) (WeakestPrecondition.list_map (A:=A) (B:=B)).
  Proof.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on (list A);
      cbn in *; intuition (try typeclasses eauto with core).
  Qed.

  Global Instance Proper_cmd :
    Proper (
     (pointwise_relation _ (Basics.flip Basics.impl)) ==> (
     (pointwise_relation _ Basics.impl) ==> (
     (pointwise_relation _ (pointwise_relation _ Basics.impl)) ==> (
     (pointwise_relation _ Roption) ==> (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ (pointwise_relation _ Basics.impl))) ==> Basics.impl)))) ==>
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl))) ==>
     Basics.impl)))))))))) WeakestPrecondition.cmd.
  Proof.
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl]; ind_on Syntax.cmd.cmd;
      cbn in *; intuition (try typeclasses eauto with core).
    { eapply Proper_expr; eauto; cbv [pointwise_relation Basics.impl]. eauto. }
    { eapply Proper_expr; eauto; cbv [pointwise_relation Basics.impl]; intros.
      eapply Proper_expr; eauto; cbv [pointwise_relation Basics.impl]; intros.
      eapply Proper_store; eauto; cbv [pointwise_relation Basics.impl]; eauto. }
    { eapply Proper_expr; eauto; cbv [pointwise_relation Basics.impl]; intuition eauto 6. }
    { eapply IHa1; try solve [typeclasses eauto with core]. eapply H.
      intros. eapply IHa2; try solve [typeclasses eauto with core]. eapply H.
      eauto. }
    { destruct H5 as (?&?&?&?&?&HH).
      eassumption || eexists.
      eassumption || eexists.
      eassumption || eexists.
      eassumption || eexists.
      eassumption || eexists.
      eassumption || eexists.
      eassumption || eexists.
      intros X Y Z T W.
      specialize (HH X Y Z T W).
      eapply Proper_expr; eauto; cbv [pointwise_relation Basics.impl]; intuition eauto 2.
      eapply IHa; eauto; cbn; intros.
      destruct H8 as (v'&H8); exists v'.
      intuition eauto. }
    { eapply Proper_list_map; eauto; cbv [respectful pointwise_relation Basics.impl]; intuition eauto 2.
      { eapply Proper_expr; eauto. }
      { eapply Proper_global; eauto. do 2 red. intros.
        eapply H3; eauto; firstorder eauto. } }
    { eapply Proper_list_map; eauto; cbv [respectful pointwise_relation Basics.impl].
      { eapply Proper_expr; eauto. }
      intros.
      edestruct H6.
      split; [solve [eauto]|]; intros.
      destruct (H8 ltac:(eauto)); intuition eauto. }
  Qed.

  Global Instance Proper_func :
    Proper (
     (pointwise_relation _ (Basics.flip Basics.impl)) ==> (
     (pointwise_relation _ Basics.impl) ==> (
     (pointwise_relation _ (pointwise_relation _ Basics.impl)) ==> (
     (pointwise_relation _ Roption) ==>
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ (pointwise_relation _ Basics.impl))) ==> Basics.impl)))) ==>
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl))) ==>
     Basics.impl))))))))) WeakestPrecondition.func.
  Proof.
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func]; intros.
    destruct a. destruct p0.
    destruct H5; intuition idtac.
    eexists.
    split.
    eauto.
    eapply Proper_cmd;
      cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func];
      try solve [typeclasses eauto with core]. eapply H.
    intros.
    eapply Proper_list_map;
      cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func];
      try solve [typeclasses eauto with core].
    intros.
    eapply Proper_get;
      cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func];
      eauto.
    eauto.
  Qed.

  Global Instance Proper_call :
    Proper (
     (pointwise_relation _ (Basics.flip Basics.impl)) ==> (
     (pointwise_relation _ Basics.impl) ==> (
     (pointwise_relation _ (pointwise_relation _ Basics.impl)) ==> (
     pointwise_relation _ Roption ==>
     (pointwise_relation _ (
     (pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl))) ==>
     Basics.impl))))))))))) WeakestPrecondition.call.
  Proof.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on (list (Semantics.word * (list Syntax.varname * list Syntax.varname * Syntax.cmd.cmd)));
      cbn in *; intuition (try typeclasses eauto with core).
    destruct a.
    destruct (Semantics.word_eqb w a1); eauto.
    eapply Proper_func; 
      cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func];
      eauto.
  Qed.

  Global Instance Proper_program :
    Proper (
     (pointwise_relation _ (Basics.flip Basics.impl)) ==> (
     (pointwise_relation _ Basics.impl) ==> (
     (pointwise_relation _ (pointwise_relation _ Basics.impl)) ==> (
     pointwise_relation _ Roption ==>
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl))) ==>
     Basics.impl))))))))) WeakestPrecondition.program.
  Proof.
    cbv [Proper respectful pointwise_relation Basics.impl  WeakestPrecondition.program]; intros.
    eapply Proper_cmd;
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func];
    try solve [typeclasses eauto with core].
    eapply H.
    intros.
    eapply Proper_call;
    cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func];
    try solve [typeclasses eauto with core].
    eauto.
  Qed.

End WeakestPrecondition.