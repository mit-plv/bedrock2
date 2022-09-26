Require Import Coq.Logic.PropExtensionality Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List. Import ListNotations. Open Scope list_scope.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.syntactic_unify.
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

  Lemma sep_to_unpacked_and_unpacked: forall (P Q: mem -> Prop) m,
      sep P Q m -> exists m1 m2, P m1 /\ Q m2 /\ Some m = mmap.du (Some m1) (Some m2).
  Proof.
    unfold sep, map.split. intros. fwd. do 2 eexists. ssplit.
    1,2: eassumption.
    simpl. unfold map.du. eapply map.disjointb_spec in Hp0p1. rewrite Hp0p1.
    reflexivity.
  Qed.

  Lemma sep_to_mem_hyp_and_unpacked: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists (M1: mem_hyp P) m2, Q m2 /\ Some m = mmap.du (Some (proj_mem M1)) (Some m2).
  Proof.
    unfold sep, map.split. intros. fwd. unshelve eexists.
    1: econstructor; eassumption.
    eexists. split. 1: eassumption.
    simpl. unfold map.du. eapply map.disjointb_spec in Hp0p1. rewrite Hp0p1.
    reflexivity.
  Qed.

  Lemma sep_to_unpacked_and_mem_hyp: forall (P Q: mem -> Prop) m,
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

  Lemma canceling_start: forall {Ps oms m},
      Some m = mmap.dus oms ->
      canceling Ps oms ->
      seps Ps m.
  Proof.
    unfold canceling. intros. apply H0. apply H.
  Qed.

  Lemma canceling_done_empty: canceling [] [].
  Proof.
    unfold canceling. simpl. intros. inversion H. unfold emp. auto.
  Qed.

  Lemma canceling_done_frame: forall oms, canceling [fun m => Some m = mmap.dus oms] oms.
  Proof.
    unfold canceling. simpl. intros. assumption.
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

  Lemma cancel_head: forall n {P: mem -> Prop} {Ps oms mn},
      P mn ->
      heaplets_nth n oms = Some mn ->
      canceling Ps (heaplets_remove_nth n oms) ->
      canceling (P :: Ps) oms.
  Proof.
    unfold canceling. intros.
    eapply seps_cons.
    pose proof dus_remove_nth as A. specialize A with (1 := H0) (2 := H2).
    fwd.
    specialize H1 with (1 := Ap0).
    unfold sep. do 2 eexists. ssplit. 2,3: eassumption.
    unfold map.split. unfold map.du in Ap1. fwd.
    eapply map.disjointb_spec in E. auto.
  Qed.

  (* for home-made rewrite *)
  Lemma subst_mem_eq(mSmall mBig: mem){rhsSmall: option mem}(C: option mem -> option mem):
    Some mSmall = rhsSmall ->
    Some mBig = C (Some mSmall) ->
    Some mBig = C rhsSmall.
  Proof. intros. rewrite H in H0. exact H0. Qed.
End HeapletwiseHyps.

Ltac cbn_heaplets :=
  cbn [heaplets_hd heaplets_tl heaplets_firstn heaplets_skipn
       heaplets_app heaplets_nth heaplets_remove_nth].

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

Ltac should_unpack P :=
 lazymatch P with
 | sep _ _ => constr:(true)
 | (fun m => Some m = _) => constr:(true)
 | _ => constr:(false)
 end.

Ltac split_sep_step :=
  let D := fresh "D" in
  lazymatch goal with
  | H: sep ?P ?Q _ |- _ =>
      let unpackP := should_unpack P in
      let unpackQ := should_unpack Q in
      lazymatch constr:((unpackP, unpackQ)) with
      | (true, true) =>
          eapply sep_to_unpacked_and_unpacked in H;
          let m1 := fresh "m0" in
          let m2 := fresh "m0" in
          destruct H as (m1 & m2 & ? & ? & D)
      | (false, true) =>
          eapply sep_to_mem_hyp_and_unpacked in H;
          let M1 := fresh "M0" in
          let m2 := fresh "m0" in
          destruct H as (M1 & m2 & ? & D)
      | (true, false) =>
          eapply sep_to_unpacked_and_mem_hyp in H;
          let m1 := fresh "m0" in
          let M2 := fresh "M0" in
          destruct H as (m1 & M2 & ? & D)
      | (false, false) =>
          eapply sep_to_mem_hyp_and_mem_hyp in H;
          let M1 := fresh "M0" in
          let M2 := fresh "M0" in
          destruct H as (M1 & M2 & D)
      end
  end.

Ltac merge_du_step :=
  match reverse goal with
  | E1: @Some ?Mem ?m = mmap.du ?o1 ?o2, E2: Some ?m' = ?rhs |- _ =>
      lazymatch rhs with
      | context C[Some m] =>
          (* home-made rewrite *)
          eapply (subst_mem_eq m m'
                    (fun hole: option Mem => ltac:(let r := context C[hole] in exact r))
                    E1) in E2;
          clear m E1
      end
  end.

Ltac start_canceling :=
  rewrite ?sep_assoc_eq;
  lazymatch goal with
  | |- ?e ?m =>
      let clauselist := reify_seps e in change (seps clauselist m)
  end;
  lazymatch goal with
  | D: Some ?m = mmap.du _ _ |- _ ?m =>
      rewrite ?mmap.du_assoc in D;
      let e := lazymatch type of D with Some m = ?e => e end in
      let memlist := reify_dus e in
      change (Some m = mmap.dus memlist) in D;
      eapply (canceling_start D);
      clear D
  end.

Ltac index_of_Some_proj_mem M oms :=
  lazymatch oms with
  | cons (Some (proj_mem M)) _ => constr:(O)
  | cons _ ?tl => let n := index_of_Some_proj_mem M tl in constr:(S n)
  end.

Ltac canceling_step :=
  lazymatch goal with
  | |- canceling (cons ?P ?Ps) ?oms =>
      tryif is_evar P then fail "reached frame (or other evar)" else
      let M := match goal with
               | M: mem_hyp ?P' |- _ =>
                   let __ := match constr:(Set) with _ => syntactic_unify P' P end in M
               end in
      let oms := lazymatch goal with |- canceling _ ?oms => oms end in
      let n := index_of_Some_proj_mem M oms in
      eapply (cancel_head n (proj_mem_hyp M)); [ reflexivity | cbn_heaplets ]
  end.

Ltac clear_unused_mem_hyps_step :=
  match goal with
  | HOld: Some ?mOld = mmap.du _ _, HNew: Some ?mNew = mmap.du _ _ |- _ =>
      clear mOld HOld; rename mNew into mOld, HNew into HOld
  | H: mem_hyp _ |- _ => clear H
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
    start_canceling.

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

    repeat canceling_step.
    eapply canceling_done_frame.
  Qed.

  Context (cmd: Type).
  Context (wp: cmd -> mem -> (mem -> Prop) -> Prop).
  Context (frobenicate: nat -> nat -> cmd).
  (* sample callee: *)
  Context (frobenicate_ok: forall (a1 a2 v1 v2: nat) (m: mem) (R: mem -> Prop)
                                  (P: mem -> Prop),
              sep (foo v1 a1) (sep (foo v2 a2) R) m /\
              (forall m', sep (foo (v1 + v2) a1) (sep (foo (v1 - v2) a2) R) m' -> P m') ->
              wp (frobenicate a1 a2) m P).

  (* sample caller: *)
  Goal forall (p1 p2 p3 x y: nat) (m: mem) (R: mem -> Prop),
      sep (foo x p1) (sep (foo y p2) (sep (foo x p3) R)) m ->
      wp (frobenicate p1 p3) m (fun m' =>
        wp (frobenicate p3 p1) m' (fun m'' =>
           sep (foo 0 p1) (sep (foo y p2) (sep (foo 0 p3) R)) m'')).
  Proof.
    intros.
    repeat split_sep_step.
    repeat merge_du_step.

    eapply frobenicate_ok.
    split. {
      start_canceling.
      repeat canceling_step.
      eapply canceling_done_frame.
    }
    cbn [mmap.dus].
    intros.
    repeat split_sep_step.
    repeat merge_du_step.
    repeat clear_unused_mem_hyps_step.

    eapply frobenicate_ok.
    split. {
      start_canceling.
      repeat canceling_step.
      eapply canceling_done_frame.
    }
    cbn [mmap.dus].
    intros.
    repeat split_sep_step.
    repeat merge_du_step.
    repeat clear_unused_mem_hyps_step.

    Fail rewrite PeanoNat.Nat.sub_diag in M0.

  Abort.

  Let foo_pair(v1 v2 a1 a2: nat) := sep (foo v1 a1) (foo v2 a2).


End HeapletwiseHypsTests.
