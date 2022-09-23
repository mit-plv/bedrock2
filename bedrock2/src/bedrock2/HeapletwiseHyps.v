Require Import Coq.Logic.PropExtensionality Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List. Import ListNotations. Open Scope list_scope.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.DisjointUnion.
Require Import bedrock2.Map.SeparationLogic.

Section HeapletwiseHyps.
  Context {key value: Type} {mem: map.map key value} {mem_ok: map.ok mem}
          {key_eqb: key -> key -> bool} {key_eqb_spec: EqDecider key_eqb}.

  (* sigma type {m: mem | P m} *)
  Inductive mem_hyp(P: mem -> Prop): Type :=
  | mk_mem_hyp(m: mem)(H: P m).

  Definition proj_mem{P: mem -> Prop}(M: mem_hyp P): mem :=
    match M with
    | mk_mem_hyp _ m _ => m
    end.

  Lemma sep_assoc_eq: forall (p q r: mem -> Prop),
      sep (sep p q) r = sep p (sep q r).
  Proof.
    intros. eapply iff1ToEq. eapply sep_assoc.
  Qed.

  Lemma proj_mem_hyp{P: mem -> Prop}(M: mem_hyp P): P (proj_mem M).
  Proof. destruct M as (m & HM). simpl. assumption. Qed.

  Lemma sep_to_sep_and_sep: forall (P Q: mem -> Prop) m,
      sep P Q m -> exists m1 m2, P m1 /\ Q m2 /\ Some m = mmap.du (Some m1) (Some m2).
  Proof.
    unfold sep, map.split. intros. fwd. do 2 eexists. ssplit.
    1,2: eassumption.
    simpl. unfold map.du. eapply map.disjointb_spec in Hp0p1. rewrite Hp0p1.
    reflexivity.
  Qed.

  Lemma sep_to_mem_hyp_and_sep: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists (M1: mem_hyp P) m2, Q m2 /\ Some m = mmap.du (Some (proj_mem M1)) (Some m2).
  Proof.
    unfold sep, map.split. intros. fwd. unshelve eexists.
    1: econstructor; eassumption.
    eexists. split. 1: eassumption.
    simpl. unfold map.du. eapply map.disjointb_spec in Hp0p1. rewrite Hp0p1.
    reflexivity.
  Qed.

  Lemma sep_to_sep_and_mem_hyp: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists m1 (M2: mem_hyp Q), P m1 /\ Some m = mmap.du (Some m1) (Some (proj_mem M2)).
  Proof.
    unfold sep, map.split. intros. fwd.
    eexists. unshelve eexists.
    1: econstructor; eassumption.
    split. 1: eassumption.
    simpl. unfold map.du. eapply map.disjointb_spec in Hp0p1. rewrite Hp0p1.
    reflexivity.
  Qed.

  Lemma sep_to_mem_hyp_and_mem_hyp: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists (M1: mem_hyp P) (M2: mem_hyp Q),
        Some m = mmap.du (Some (proj_mem M1)) (Some (proj_mem M2)).
  Proof.
    unfold sep, map.split. intros. fwd. unshelve (do 2 eexists).
    1,2: econstructor; eassumption.
    simpl. unfold map.du. eapply map.disjointb_spec in Hp0p1. rewrite Hp0p1.
    reflexivity.
  Qed.

  Definition canceling(Ps: list (mem -> Prop))(oms: list (option mem)): Prop :=
    forall m, Some m = mmap.dus oms -> seps Ps m.

  Lemma canceling_done: canceling [] [].
  Proof.
    unfold canceling. simpl. intros. inversion H. unfold emp. auto.
  Qed.

  (* Separate definitions to avoid simplifying user-defined expressions that
     use the definitions from the standard library: *)
  Definition heaplets_hd: list (option mem) -> option mem :=
    Eval cbv delta in (@List.hd (option mem) None).
  Definition heaplets_tl: list (option mem) -> list (option mem) :=
    Eval cbv delta in (@List.tl (option mem)).
  Definition heaplets_firstn: nat -> list (option mem) -> list (option mem) :=
    Eval cbv delta in (@List.firstn (option mem)).
  Definition heaplets_skipn: nat -> list (option mem) -> list (option mem) :=
    Eval cbv delta in (@List.skipn (option mem)).
  Definition heaplets_app: list (option mem) -> list (option mem) -> list (option mem) :=
    Eval cbv delta in (@List.app (option mem)).
  Definition heaplets_nth(n: nat)(xs: list (option mem)): option mem :=
    heaplets_hd (skipn n xs).
  Definition heaplets_remove_nth(n: nat)(xs : list (option mem)): list (option mem) :=
    heaplets_app (heaplets_firstn n xs) (heaplets_tl (heaplets_skipn n xs)).

  Lemma cancel_head: forall n Ps (P: mem -> Prop) oms mn,
      heaplets_nth n oms = Some mn ->
      P mn ->
      canceling Ps (heaplets_remove_nth n oms) ->
      canceling (P :: Ps) oms.
  Proof.
    unfold canceling. intros.
    eapply seps_cons.
    pose proof dus_remove_nth as A. specialize A with (1 := H) (2 := H2).
    fwd.
    specialize H1 with (1 := Ap0).
    unfold sep. do 2 eexists. ssplit. 2,3: eassumption.
    unfold map.split. unfold map.du in Ap1. fwd.
    eapply map.disjointb_spec in E. auto.
  Qed.
End HeapletwiseHyps.

Ltac reify_dus e :=
  lazymatch e with
  | mmap.du ?h ?t => let rt := reify_dus t in constr:(cons h rt)
  | _ => constr:(cons e nil)
  end.

Ltac reify_seps e :=
  lazymatch e with
  | sep ?h ?t => let rt := reify_seps t in constr:(cons h rt)
  | _ => constr:(cons e nil)
  end.

Ltac split_sep_step :=
  let D := fresh "D" in
  lazymatch goal with
  | H: sep (sep _ _) (sep _ _) _ |- _ =>
      eapply sep_to_sep_and_sep in H;
      let m1 := fresh "m0" in
      let m2 := fresh "m0" in
      destruct H as (m1 & m2 & ? & ? & D)
  | H: sep _ (sep _ _) _ |- _ =>
      eapply sep_to_mem_hyp_and_sep in H;
      let M1 := fresh "M0" in
      let m2 := fresh "m0" in
      destruct H as (M1 & m2 & ? & D)
  | H: sep (sep _ _) _ _ |- _ =>
      eapply sep_to_sep_and_mem_hyp in H;
      let m1 := fresh "m0" in
      let M2 := fresh "M0" in
      destruct H as (m1 & M2 & ? & D)
  | H: sep _ _ _ |- _ =>
      eapply sep_to_mem_hyp_and_mem_hyp in H;
      let M1 := fresh "M0" in
      let M2 := fresh "M0" in
      destruct H as (M1 & M2 & D)
  end.

Ltac merge_du_step :=
  lazymatch reverse goal with
  | H: Some ?m = mmap.du _ _ |- _ => rewrite H in *; clear m H
  end.


Section HeapletwiseHypsTests.
  Context {key value: Type} {mem: map.map key value} {mem_ok: map.ok mem}
          {key_eqb: key -> key -> bool} {key_eqb_spec: EqDecider key_eqb}.

  Hypothesis foo: nat -> nat -> mem -> Prop.

  Goal forall m v1 v2 v3 v4 (Rest: mem -> Prop),
      (sep (foo v1 1) (sep (sep (foo v2 2) (foo v3 3)) (sep (foo v4 4) Rest))) m ->
      exists R a4 a3, sep (sep (foo a4 4) (foo a3 3)) R m.
  Proof.
    intros.
    repeat split_sep_step.
    repeat merge_du_step.

    do 3 eexists.


    lazymatch goal with
    | D: Some ?m = mmap.du _ _ |- _ ?m =>
        rewrite ?mmap.du_assoc in D;
        let memtree := lazymatch type of D with Some m = ?e => e end in
        let memlist := reify_dus memtree in
        rewrite ?sep_assoc_eq;
        let clausetree := lazymatch goal with |- ?e m => e end in
        let clauselist := reify_seps clausetree in
        revert m D;

        lazymatch goal with
        | |- ?g => assert (g = canceling clauselist memlist)
        end

    end.
    {
      unfold canceling.
      (* simpl. (* https://github.com/coq/coq/issues/5378 ? *) *)
      cbn [seps mmap.dus].
      reflexivity.
    }
    rewrite H. clear H.

(*
  M0 : mem_hyp (foo v1 1)
  M3 : mem_hyp (foo v2 2)
  M4 : mem_hyp (foo v3 3)
  M1 : mem_hyp (foo v4 4)
  M2 : mem_hyp Rest
  ============================
  canceling [foo ?a4 4; foo ?a3 3; ?R]
    [Some (proj_mem M0); Some (proj_mem M3); Some (proj_mem M4);
    Some (proj_mem M1); Some (proj_mem M2)]
*)

    (* canceling steps: *)

    eapply (cancel_head 3). 1: reflexivity. 1: eapply proj_mem_hyp. cbn.

    eapply (cancel_head 2). 1: reflexivity. 1: eapply proj_mem_hyp. cbn.

    (* now that all the callee's hyps are satisfied, we need to construct the frame,
       and we use the same canceling lemma for that as well: *)

    eapply (cancel_head 0 (_ :: _)). 1: reflexivity. 1: eapply proj_mem_hyp. cbn.

    eapply (cancel_head 0 (_ :: _)). 1: reflexivity. 1: eapply proj_mem_hyp. cbn.

    eapply (cancel_head 0 nil). 1: reflexivity. 1: eapply proj_mem_hyp. cbn.

    apply canceling_done.
  Qed.

End HeapletwiseHypsTests.
