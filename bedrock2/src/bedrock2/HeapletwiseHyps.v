Require Import Coq.Logic.PropExtensionality Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List. Import ListNotations. Open Scope list_scope.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.DisjointUnion.

Section HeapletwiseHyps.
  Context{key value: Type} {mem: map.map key value} {mem_ok: map.ok mem}
    {key_eqb: key -> key -> bool} {key_eqb_spec: EqDecider key_eqb}.

  (* like sep, but using disjoint union instead of map.split *)
  Definition star(P Q: mem -> Prop)(m: mem): Prop :=
    exists m1 m2, P m1 /\ Q m2 /\ Some m = mmap.du (Some m1) (Some m2).

  Lemma star_empty_r: forall P, star P (eq map.empty) = P.
  Proof.
    intros. extensionality m. apply propositional_extensionality.
    unfold star. split; intros; fwd.
    - rewrite mmap.du_empty_r in Hp2. inversion Hp2. subst. assumption.
    - do 2 eexists. ssplit. 1: eassumption. 1: reflexivity. rewrite mmap.du_empty_r.
      reflexivity.
  Qed.

  Fixpoint bigstar(Ps: list (mem -> Prop)): mem -> Prop :=
    match Ps with
    | nil => eq map.empty
    | h :: nil => h
    | h :: t => star h (bigstar t)
    end.

  Fixpoint bigstar'(Ps: list (mem -> Prop)): mem -> Prop :=
    match Ps with
    | nil => eq map.empty
    | h :: t => star h (bigstar' t)
    end.

  Lemma bigstar_bigstar' Ps: bigstar Ps = bigstar' Ps.
  Proof.
    induction Ps.
    - reflexivity.
    - simpl (bigstar' _). rewrite <- IHPs. destruct Ps; try reflexivity.
      simpl. symmetry. apply star_empty_r.
  Qed.

  Definition canceling(Ps: list (mem -> Prop))(oms: list (option mem)): Prop :=
    forall m, Some m = mmap.dus oms -> bigstar Ps m.

  Lemma canceling_start: forall Ps oms m,
      Some m = mmap.dus oms ->
      canceling Ps oms ->
      bigstar Ps m.
  Proof.
    unfold canceling. intros. apply H0. apply H.
  Qed.

  Lemma canceling_done: canceling [] [].
  Proof.
    unfold canceling. simpl. intros. inversion H. reflexivity.
  Qed.

  Let nth n xs := hd (@None mem) (skipn n xs).
  Let remove_nth n (xs : list (option mem)) := firstn n xs ++ tl (skipn n xs).

  Lemma cancel_head: forall n Ps (P: mem -> Prop) oms mn,
      nth n oms = Some mn ->
      P mn ->
      canceling Ps (remove_nth n oms) ->
      canceling (P :: Ps) oms.
  Proof.
    unfold canceling. intros.
    rewrite bigstar_bigstar'. simpl. rewrite <- bigstar_bigstar'.
    pose proof dus_remove_nth as A. specialize A with (1 := H) (2 := H2).
    fwd.
    specialize H1 with (1 := Ap0).
    unfold star. do 2 eexists. ssplit.
    - eassumption.
    - eassumption.
    - simpl. assumption.
  Qed.

  Hypothesis foo: nat -> nat -> mem -> Prop.

  Example test1: forall m v1 v2 v3 v4,
      (star (foo v1 1) (star (star (foo v2 2) (foo v3 3)) (foo v4 4))) m ->
      exists R a4 a3, star (foo a4 4) (star (foo a3 3) R) m.
  Proof.
    intros.

    (* destruct memory hyp into separate hypotheses: *)
    destruct H as (m1 & m2 & HM1 & HM2 & E).
    destruct HM2 as (m23 & m4 & HM23 & HM4 & E'). rewrite E' in E. clear m2 E'.
    destruct HM23 as (m2 & m3 & HM2 & HM3 & E'). rewrite E' in E. clear m23 E'.

    do 3 eexists. move HM1 before HM2. move m before m1.

(*
  v1, v2, v3, v4 : nat
  m, m1, m4, m2, m3 : mem
  HM1 : foo v1 1 m1
  HM2 : foo v2 2 m2
  HM3 : foo v3 3 m3
  HM4 : foo v4 4 m4
  E : Some m = Some m1 \*/ (Some m2 \*/ Some m3 \*/ Some m4)
  ============================
  star (foo ?a4 4) (star (foo ?a3 3) ?R) m
*)

    (* make goal a canceling goal: *)
    lazymatch goal with
    | |- star ?A (star ?B ?C) ?m => change (bigstar [A; B; C] m)
    end.
    rewrite mmap.du_assoc in E.
    change (Some m = mmap.dus [Some m1; Some m2; Some m3; Some m4]) in E.
    eapply canceling_start. 1: exact E. clear E.

(*
  ============================
  canceling [foo ?a4 4; foo ?a3 3; ?R] [Some m1; Some m2; Some m3; Some m4]
*)

    (* canceling steps: *)

    eapply (cancel_head 3). 1: reflexivity. 1: eassumption. cbn.

    eapply (cancel_head 2). 1: reflexivity. 1: eassumption. cbn.

    (* now that all the callee's hyps are satisfied, we need to construct the frame,
       and we use the same canceling lemma for that as well: *)

    eapply (cancel_head 0 (_ :: _)). 1: reflexivity. 1: exact HM1. cbn.

    eapply (cancel_head 0 nil). 1: reflexivity. 1: exact HM2. cbn.

    apply canceling_done.
  Qed.

End HeapletwiseHyps.

(* Print Assumptions test1.
   only propositional_extensionality and functional_extensionality_dep *)


Section PresentationWithSigmas. (* not sure if that works *)
  Context{key value: Type} {mem: map.map key value} {mem_ok: map.ok mem}
    {key_eqb: key -> key -> bool} {key_eqb_spec: EqDecider key_eqb}.

  (* sigma type {m: mem | P m} *)
  Inductive mem_hyp(P: mem -> Prop): Type :=
  | mk_mem_hyp(m: mem)(H: P m).

  Definition proj_mem{P: mem -> Prop}(M: mem_hyp P): mem :=
    match M with
    | mk_mem_hyp _ m _ => m
    end.

  Definition Star(P Q: mem -> Prop)(m: mem): Prop :=
    exists (M1: mem_hyp P) (M2: mem_hyp Q),
      Some m = mmap.du (Some (proj_mem M1)) (Some (proj_mem M2)).

  Hypothesis foo: nat -> nat -> mem -> Prop.

  Goal forall m v1 v2 v3 v4 (Rest: mem -> Prop),
      (Star (foo v1 1) (Star (Star (foo v2 2) (foo v3 3)) (foo v4 4))) m ->
      exists R a1 a2 (A1: mem_hyp (foo a1 1)) (A2: mem_hyp (foo a2 2)) (A3: mem_hyp R),
        Some m = mmap.du (Some (proj_mem A1))
                         (mmap.du (Some (proj_mem A2)) (Some (proj_mem A3))).
  Proof.
    intros.
    destruct H as (M1 & M2 & E).
    destruct M2 as (m2 & HM2). cbn [proj_mem] in E.
    destruct HM2 as (M2 & M4 & E2). rewrite E2 in E. clear m2 E2.
    destruct M2 as (m2 & HM2). cbn [proj_mem] in E.
    destruct HM2 as (M2 & M3 & E2). rewrite E2 in E. clear m2 E2.

    do 3 eexists.
  Abort.
End PresentationWithSigmas.
