Require Import compiler.util.Common.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Require Import compiler.UseImmediateDef.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.MetricCosts.

Local Notation var := String.string (only parsing).

Section WithArguments.
  Context {width : Z}.
  Context {BW :  Bitwidth.Bitwidth width }.
  Context {word :  word width } {word_ok : word.ok word}.
  Context {env :  map.map string (list var * list var * stmt var) } {env_ok : map.ok env}.
  Context {mem :  map.map word (Init.Byte.byte : Type) } {mem_ok: map.ok mem}.
  Context {locals :  map.map string word } {locals_ok: map.ok locals}.
  Context {ext_spec : Semantics.ExtSpec} {ext_spec_ok: Semantics.ext_spec.ok ext_spec}.
  Context (is5BitImmediate : Z -> bool).
  Context (is12BitImmediate  : Z -> bool).

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
        constants [word_cst]).

  Local Notation exec := (exec PreSpill isRegStr).

  Open Scope MetricH_scope.

  Ltac tandem H := (
    repeat match goal with
           | |- exists _, _ => let x := fresh in destruct H as (x&?); exists x
           | |- _ /\ _ => destruct H as (?&H); split; try eassumption
           | _ => let x := fresh in intro x; specialize (H x)
           end
  ).

  Ltac finish := (
    simpl;
    intros *;
    repeat match goal with
           | |- (exists _, _ /\ _) -> _ => intros (?&?&?)
           | |- _ /\ _ => split; eauto
           | |- exists _, _ => eexists
           end;
    repeat match goal with
           | H : _ <= _ |- _ => revert H
           end;
    clear;
    FlatImp.scost_hammer
  ).

  (* TODO these two lemmas are somewhat slow *)
  Lemma op_cost_y : forall x0 y v0 mcH' mc v mcL lit,
    exec.cost_SOp isRegStr x0 y (Var v0) EmptyMetricLog - EmptyMetricLog <=
      mcH' - cost_lit isRegStr lit mc ->
    exec.cost_SOp isRegStr x0 y (Const v) (cost_lit isRegStr lit mcL) - mcL <=
      mcH' - mc.
  Proof. finish. Qed.

  Lemma op_cost_v0 : forall x0 y v0 mcH' mc v mcL lit,
    exec.cost_SOp isRegStr x0 y (Var v0) EmptyMetricLog - EmptyMetricLog <=
      mcH' - cost_lit isRegStr lit mc ->
    exec.cost_SOp isRegStr x0 v0 (Const v) (cost_lit isRegStr lit mcL) - mcL <=
      mcH' - mc.
  Proof. finish. Qed.

  Lemma useImmediate_correct_aux:
    forall eH eL,
       (useimmediate_functions is5BitImmediate is12BitImmediate) eH = Success eL ->
       forall sH t m mcH lH post,
       exec eH sH t m lH mcH post ->
       forall mcL,
       exec eL (useImmediate is5BitImmediate is12BitImmediate sH) t m lH mcL
       (fun t' m' l' mcL' => exists mcH', metricsLeq (mcL' - mcL) (mcH' - mcH) /\ post t' m' l' mcH').
  Proof.
    induction 2; try solve [
      simpl; econstructor; eauto;
      tandem H3;
      finish
    ].

    - (* SCall *)
      simpl; econstructor; eauto.
      { unfold useimmediate_functions in H.
        destruct (map.try_map_values_fw _ _ _ H _ _ H0) as (?&[=Huseimm]&Hmap).
        rewrite <- Huseimm in Hmap.
        exact Hmap. }
      cbv beta.
      intros * (?&?&Houtcome).
      destruct (H4 _ _ _ _ Houtcome) as (retvs&l'&Hpost).
      exists retvs, l'.
      tandem Hpost.
      finish.

    - (* SStackalloc *)
      simpl; econstructor; eauto.
      tandem H2.
      eapply exec.weaken; [eauto|].
      simpl; intros * (?&?&?&?&?&?&?).
      finish.

    - (* SIf true *)
      simpl; econstructor; eauto.
      eapply exec.weaken; [eauto|].
      finish.

    - (* SIf false *)
      simpl; intro; eapply exec.if_false; eauto.
      eapply exec.weaken; [eauto|].
      finish.

    - (* SLoop *)
      simpl; econstructor; eauto; simpl.
      { intros * (?&?&?); eauto. }
      { intros * (?&?&?) **. finish. }
      { intros * (?&?&?) **.
        eapply exec.weaken; [eauto|].
        simpl; intros * (?&?&?).
        instantiate (1 := fun t m l MC1 => exists MC2, MC1 - mcL <= MC2 - mc /\ mid2 t m l MC2).
        finish. }
      { intros * (?&?&?).
        eapply exec.weaken; [eauto|].
        finish. }

    - (* SSeq *)
      simpl. intro.

      repeat (
        match goal with
        | |- context[match ?x with _ => _ end] => destr x
        | |- context[if ?x then _ else _ ] => destr x
        end;
        try solve [
          eapply @exec.seq; eauto; simpl;
          intros * (?&?&?);
          eapply @exec.weaken; [eauto|];
          finish
        ]
      ).

      all: eapply @exec.seq_cps; eapply @exec.lit.

      all: match goal with
           | H: exec _ _ _ _ _ _ ?mid,
               H': forall t m l mc,
                 ?mid _ _ _ _ -> exec ?eL _ _ _ _ _ ?post
                 |- _ => inversion H
           end.

      all: match goal with
           | H: ?mid _ _ _ _,
             H0: forall t m l mc,
                 ?mid t m l mc -> forall mcL, exec ?eL _ _ _ _ mcL _
                 |- exec ?eL _ _ _ _ _ _
             => specialize (H0 _ _ _ _ H EmptyMetricLog); inversion H0
           end.

      all: simpl in *;
        match goal with
        | [ H: map.get (map.put _ ?x _) ?x = _ |- _ ]
          => rewrite map.get_put_same in H; fwd
        end.

      all: eapply @exec.op; simpl in *; [ eassumption | reflexivity | ].

      all: exists mcH'; split; [solve [eapply op_cost_y; eauto | eapply op_cost_v0; eauto]|eauto].

      + rewrite word.add_comm. assumption.
      + replace (word.add y' (word.of_Z (-v))) with (word.sub y' (word.of_Z v)) by ring. assumption.
      + rewrite word.and_comm. assumption.
      + rewrite word.or_comm. assumption.
      + rewrite word.xor_comm. assumption.

  (* this is slightly slow also *)
  Qed.

End WithArguments.
