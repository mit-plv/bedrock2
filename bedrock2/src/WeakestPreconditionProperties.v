Require Import bedrock2.Macros.
Require bedrock2.WeakestPrecondition.
Require bedrock2.Map.Decomp.

Require Import Coq.Classes.Morphisms.

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

  Global Instance Proper_load : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) WeakestPrecondition.load.
  Proof. cbv [WeakestPrecondition.load]; cbv [Proper respectful pointwise_relation Basics.impl]; firstorder idtac. Qed.

  Global Instance Proper_store : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl))))) WeakestPrecondition.store.
  Proof. cbv [WeakestPrecondition.load]; cbv [Proper respectful pointwise_relation Basics.impl]; firstorder idtac. Qed.

  Global Instance Proper_expr : Proper (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ Basics.impl) ==> Basics.impl)))) WeakestPrecondition.expr.
  Proof.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on Syntax.expr.expr;
      cbn in *; intuition (try typeclasses eauto with core).
    eapply Proper_literal; eauto.
    eapply Proper_get; eauto.
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
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ ((pointwise_relation _ (pointwise_relation _ Basics.impl))) ==> Basics.impl)))) ==>
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl))) ==>
     Basics.impl))))))))) WeakestPrecondition.cmd.
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
    { destruct H4 as (?&?&?&?&?&HH).
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
      destruct H7 as (v'&H7); exists v'.
      intuition eauto. }
    { eapply Proper_list_map; eauto; cbv [respectful pointwise_relation Basics.impl]; intuition eauto 2.
      { eapply Proper_expr; eauto. }
      { eapply H2; eauto; firstorder eauto. } }
    { eapply Proper_list_map; eauto; cbv [respectful pointwise_relation Basics.impl].
      { eapply Proper_expr; eauto. }
      intros.
      edestruct H5.
      split; [solve [eauto]|]; intros.
      destruct (H7 ltac:(eauto)); intuition eauto. }
  Qed.

  Global Instance Proper_func :
    Proper (
     (pointwise_relation _ (Basics.flip Basics.impl)) ==> (
     (pointwise_relation _ Basics.impl) ==> (
     (pointwise_relation _ (pointwise_relation _ Basics.impl)) ==> (
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
    destruct H4; intuition idtac.
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
     (pointwise_relation _ (
     (pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     pointwise_relation _ (
     (pointwise_relation _ (pointwise_relation _ (pointwise_relation _ Basics.impl))) ==>
     Basics.impl))))))))))) WeakestPrecondition.call.
  Proof.
    cbv [Proper respectful pointwise_relation Basics.impl]; ind_on (list (Syntax.funname * (list Syntax.varname * list Syntax.varname * Syntax.cmd.cmd)));
      cbn in *; intuition (try typeclasses eauto with core).
    destruct a.
    destruct (Semantics.funname_eqb f a1); eauto.
    eapply Proper_func; 
      cbv [Proper respectful pointwise_relation Basics.flip Basics.impl  WeakestPrecondition.func];
      eauto.
  Qed.

  Global Instance Proper_program :
    Proper (
     (pointwise_relation _ (Basics.flip Basics.impl)) ==> (
     (pointwise_relation _ Basics.impl) ==> (
     (pointwise_relation _ (pointwise_relation _ Basics.impl)) ==> (
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

  Import Map.map.
  Lemma tailrecursion {measure} (P Q:_->_->_->_->Prop) lt 
    rely guarantee progress call test body t m l (post:_->_->_->Prop)
    (Hwf : well_founded lt) (v : measure)
    : forall p0 R (Hm0 : split m p0 R) (Pp0 : P v t p0 l)
    (Hbody : forall v0 t0 m0 l0, forall p R, split m0 p R -> P v0 t0 p l0 ->
     WeakestPrecondition.expr m0 l0 test (fun br =>
       (Semantics.word_test br = true ->
         WeakestPrecondition.cmd rely guarantee progress call body t0 m0 l0
           (fun t1 m1 l1 => exists p1, split m1 p1 R /\ exists q d, split p1 q d /\ exists v1, P v1 t1 q l1 /\ (progress t1 t0 \/ lt v1 v0)
             /\ forall t2 m2 l2, forall p2, split m2 p2 R -> forall q2, split p2 q2 d -> Q v1 t2 q2 l2 -> Q v0 t2 p2 l2)) /\
       (Semantics.word_test br = false -> Q v0 t0 p l0))
    )
    (Hcont : forall t m l p, split m p R -> Q v t p l -> post t m l)
  , WeakestPrecondition.cmd rely guarantee progress call (Syntax.cmd.while test body) t m l post.
  Proof.
    assert (FIXME: ok Semantics.mem) by admit.
    intros.
    exists measure, lt.
    exists (let v0 := v in fun v t m l => exists p, split m p R /\ exists q D, split p q D /\ P v t q l /\ (forall t2 m2 l2, forall p2, split m2 p2 R -> forall q2, split p2 q2 D -> Q v t2 q2 l2 -> Q v0 t2 p2 l2)).
    split; [solve[eauto]|].
    split.
    { eexists v, p0. split. auto.
      eexists p0. exists empty.
      split. solve [apply (Decomp.split_empty_r p0); trivial].
      split. solve[trivial].
      intros ? ? ? ? ? ? Hsplit ?.
      eapply Decomp.split_empty_r in Hsplit. subst. trivial. }
    clear dependent p0.
    intros v0 t0 m0 l0 (p0&?m0_p0_R&q0&D&p0_q0_D&P0&Himpl).
    eapply Proper_expr; cycle 1; [|clear Hbody].
    { eapply Hbody with (R := union D R); cycle 1.
      eauto.
      revert p0_q0_D; revert m0_p0_R.
      assert (split m0 p0 R -> split p0 q0 D -> split m0 q0 (union D R)) by admit; assumption. }
    intros br [Htrue Hfalse]; split; [|solve[eauto]].
    intro Hbr; specialize (Htrue Hbr); clear Hfalse.
    { eapply Proper_cmd; [ reflexivity | reflexivity | reflexivity | | | eapply Htrue ]; clear Htrue.
      { admit. (* Proper_call *) }
      intros t1 m1 l1 (p1&?&q&d&?&v1&P1&?&impl1).
      exists v1. split; cycle 1. solve[eauto].
      exists (union p1 D); split. admit.
      eexists q, (union d D). split. admit.
      split.
      auto.
      intros.
      eapply Himpl. eauto. instantiate (1:=union q2 d). admit.
      eapply impl1. instantiate (1:=m2). admit.
      { eapply Decomp.split_disjoint_union.
        destruct H3. eapply Decomp.disjoint_union_r in H5. intuition idtac. }
      assumption.
    }
  Admitted.
End WeakestPrecondition.