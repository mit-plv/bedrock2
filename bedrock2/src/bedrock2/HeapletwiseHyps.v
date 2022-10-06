Require Import Coq.Logic.PropExtensionality Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List. Import ListNotations. Open Scope list_scope.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.syntactic_unify.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.DisjointUnion.
Require Import bedrock2.Map.SeparationLogic.

(* to mark hypotheses about heaplets *)
Definition with_mem{mem: Type}(m: mem)(P: mem -> Prop): Prop := P m.

Declare Scope heapletwise_scope.
Open Scope heapletwise_scope.

Notation "m |= P" := (with_mem m P) (at level 72) : heapletwise_scope.

Notation "m 'is' 'split' 'into' m1 , .. , m2 , m3" :=
  (Some m = mmap.dus (cons (Some m1) .. (cons (Some m2) (cons (Some m3) nil)) ..))
  (at level 10, m1 at level 0, m2 at level 0, m3 at level 0)
: heapletwise_scope.

Section HeapletwiseHyps.
  Context {key value: Type} {mem: map.map key value} {mem_ok: map.ok mem}
          {key_eqb: key -> key -> bool} {key_eqb_spec: EqDecider key_eqb}.

  Lemma split_du: forall (m m1 m2: mem),
      map.split m m1 m2 <-> Some m = mmap.du (Some m1) (Some m2).
  Proof.
    unfold map.split, mmap.du, map.du. split; intros; fwd.
    - eapply map.disjointb_spec in Hp1. rewrite Hp1. reflexivity.
    - eapply map.disjointb_spec in E. auto.
  Qed.

  (* with mmap.du instead of map.split:
  Definition wand(P1 P2: mem -> Prop): mem -> Prop :=
    fun mdiff => forall m1 m2, Some m2 = mmap.du (Some m1) (Some mdiff) -> P1 m1 -> P2 m2. *)

  Definition wand(P1 P2: mem -> Prop): mem -> Prop :=
    fun mdiff => forall m1 m2, map.split m2 mdiff m1 -> P1 m1 -> P2 m2.

  Lemma wand_adjoint: forall (P Q R: mem -> Prop),
      impl1 (sep P Q) R <-> impl1 P (wand Q R).
  Proof.
    unfold impl1, sep, wand. intros; split; intros; fwd; eauto 7.
  Qed.

  (* modus ponens for wand only holds in one direction! *)
  Lemma wand_mp: forall P Q,
      impl1 (sep P (wand P Q)) Q.
  Proof.
    intros. rewrite sep_comm. rewrite (wand_adjoint (wand P Q) P Q). reflexivity.
  Qed.

  Lemma ramify_funspec_hyp: forall (calleePre calleePost callerPost: mem -> Prop) m,
      (* non-ramified hypothesis: requires creating an evar for Frame too early *)
      (exists Frame,
          sep calleePre Frame m /\ (forall m', sep calleePost Frame m' -> callerPost m')) <->
      (* ramified hypothesis: no frame needed *)
      sep calleePre (wand calleePost callerPost) m.
  Proof.
    split; intros; fwd.
    - revert m Hp0.
      change (impl1 (sep calleePre Frame) (sep calleePre (wand calleePost callerPost))).
      reify_goal. ecancel_step_by_implication. cbn [seps].
      eapply (wand_adjoint Frame calleePost callerPost). rewrite sep_comm. unfold impl1.
      exact Hp1.
    - eexists. split. 1: exact H.
      change (impl1 (sep calleePost (wand calleePost callerPost)) callerPost).
      eapply wand_mp.
  Qed.

  Lemma sep_assoc_eq: forall (p q r: mem -> Prop),
      sep (sep p q) r = sep p (sep q r).
  Proof.
    intros. eapply iff1ToEq. eapply sep_assoc.
  Qed.

  Lemma sep_to_with_mem_and_with_mem: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists m1 m2, with_mem m1 P /\ with_mem m2 Q /\ Some m = mmap.du (Some m1) (Some m2).
  Proof.
    unfold with_mem, sep, map.split. intros. fwd. do 2 eexists. ssplit.
    1,2: eassumption.
    simpl. unfold map.du. eapply map.disjointb_spec in Hp0p1. rewrite Hp0p1.
    reflexivity.
  Qed.

  Lemma sep_to_with_mem_and_unpacked: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists m1 m2, with_mem m1 P /\ Q m2 /\ Some m = mmap.du (Some m1) (Some m2).
  Proof. exact sep_to_with_mem_and_with_mem. Qed.

  Lemma sep_to_unpacked_and_with_mem: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists m1 m2, P m1 /\ with_mem m2 Q /\ Some m = mmap.du (Some m1) (Some m2).
  Proof. exact sep_to_with_mem_and_with_mem. Qed.

  Lemma sep_to_unpacked_and_unpacked: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists m1 m2, P m1 /\ Q m2 /\ Some m = mmap.du (Some m1) (Some m2).
  Proof. exact sep_to_with_mem_and_with_mem. Qed.

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
      with_mem mn P ->
      heaplets_nth n oms = Some mn ->
      canceling Ps (heaplets_remove_nth n oms) ->
      canceling (P :: Ps) oms.
  Proof.
    unfold with_mem, canceling. intros.
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
  let m1 := fresh "m0" in
  let m2 := fresh "m0" in
  let H1 := fresh "H0" in
  let H2 := fresh "H0" in
  lazymatch goal with
  | H: sep ?P ?Q ?parent_m |- _ =>
      let unpackP := should_unpack P in
      let unpackQ := should_unpack Q in
      lazymatch constr:((unpackP, unpackQ)) with
      | (true, true) => eapply sep_to_unpacked_and_unpacked in H
      | (false, true) => eapply sep_to_with_mem_and_unpacked in H
      | (true, false) => eapply sep_to_unpacked_and_with_mem in H
      | (false, false) => eapply sep_to_with_mem_and_with_mem in H
      end;
      destruct H as (m1 & m2 & H1 & H2 & D);
      move m1 before parent_m; (* before in direction of movement == below *)
      move m2 before m1
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

Ltac reify_disjointness_hyp :=
  lazymatch goal with
  | D: Some ?m = mmap.du _ _ |- _ =>
      rewrite ?mmap.du_assoc in D;
      let e := lazymatch type of D with Some m = ?e => e end in
      let memlist := reify_dus e in
      change (Some m = mmap.dus memlist) in D
  end.

Ltac start_canceling :=
  rewrite ?sep_assoc_eq;
  lazymatch goal with
  | |- ?e ?m =>
      let clauselist := reify_seps e in change (seps clauselist m)
  end;
  lazymatch goal with
  | D: Some ?m = mmap.dus _ |- _ ?m =>
      eapply (canceling_start D);
      clear D
  end.

Ltac index_of_Some m oms :=
  lazymatch oms with
  | cons (Some m) _ => constr:(O)
  | cons _ ?tl => let n := index_of_Some m tl in constr:(S n)
  end.

Ltac canceling_step :=
  lazymatch goal with
  | |- canceling (cons ?P ?Ps) ?oms =>
      tryif is_evar P then fail "reached frame (or other evar)" else
      let H := match goal with
               | H: with_mem _ ?P' |- _ =>
                   let __ := match constr:(Set) with _ => syntactic_unify P' P end in H
               end in
      let m := lazymatch type of H with with_mem ?m _ => m end in
      let oms := lazymatch goal with |- canceling _ ?oms => oms end in
      let n := index_of_Some m oms in
      eapply (cancel_head n H); [ reflexivity | cbn_heaplets ]
  end.

Ltac clear_unused_mem_hyps_step :=
  match goal with
  | H: with_mem ?m _ |- _ => clear m H
  end.

Ltac intros_after_mem_modification :=
  cbn [mmap.dus];
  lazymatch goal with
  | D: @Some ?mem ?m = mmap.dus _ |- forall (_: ?mem), _ =>
      let mOld := fresh "mOld" in
      rename m into mOld;
      intro m;
      intros;
      move m before mOld;
      clear D mOld
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
    reify_disjointness_hyp.
    do 3 eexists.
    start_canceling.

(*
  m, m0, m6, m7, m4, m5 : mem
  v1, v2, v3, v4 : nat
  Rest : mem -> Prop
  H0 : m0 |= foo v1 1
  H3 : m6 |= foo v2 2
  H5 : m7 |= foo v3 3
  H1 : m4 |= foo v4 4
  H4 : m5 |= Rest
  ============================
  canceling [foo ?a4 4; foo ?a3 3; ?R] [Some m0; Some m6; Some m7; Some m4; Some m5]
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
           sep (foo 0 p1) (sep (foo y p2) (sep (foo (x + x) p3) R)) m'')).
  Proof.
    intros.
    repeat split_sep_step.
    repeat merge_du_step.
    reify_disjointness_hyp.

    eapply frobenicate_ok.
    split. {
      start_canceling.
      repeat canceling_step.
      eapply canceling_done_frame.
    }
    intros_after_mem_modification.
    repeat split_sep_step.
    repeat merge_du_step.
    reify_disjointness_hyp.
    repeat clear_unused_mem_hyps_step.

    eapply frobenicate_ok.
    split. {
      start_canceling.

      (* if this was splitting memories, instantiating ?R with (eq the-split-memories),
         we'd get evar scoping problems!
         -> instantiate with mem predicates instead of eq?

         -> trick like ramified frame rule?
       *)

      canceling_step.
      canceling_step.
      eapply canceling_done_frame.
    }
    intros_after_mem_modification.
    repeat split_sep_step.
    repeat merge_du_step.
    reify_disjointness_hyp.
    repeat clear_unused_mem_hyps_step.

    rewrite PeanoNat.Nat.sub_diag in *.
    rewrite PeanoNat.Nat.add_0_l in *.
    rewrite PeanoNat.Nat.sub_0_l in *.

    start_canceling.
    repeat canceling_step.
    eapply canceling_done_empty.
  Qed.

  Lemma frobenicate_ok_ramified: forall (a1 a2 v1 v2: nat) (m: mem) (P: mem -> Prop),
      sep (foo v1 a1) (sep (foo v2 a2) (* <-- calleePre *)
        (wand (sep (foo (v1 + v2) a1) (foo (v1 - v2) a2)) (* <-- calleePost *)
              P (* <-- callerPost *))) m ->
      wp (frobenicate a1 a2) m P.
  Proof.
    intros. eapply sep_assoc in H. eapply ramify_funspec_hyp in H. fwd.
    eapply frobenicate_ok. split.
    - eapply sep_assoc. eassumption.
    - rewrite <- sep_assoc_eq. assumption.
  Qed.

  (* sample caller: *)
  Goal forall (p1 p2 p3 x y: nat) (m: mem) (R: mem -> Prop),
      sep (foo x p1) (sep (foo y p2) (sep (foo x p3) R)) m ->
      wp (frobenicate p1 p3) m (fun m' =>
        wp (frobenicate p3 p1) m' (fun m'' =>
           sep (foo 0 p1) (sep (foo y p2) (sep (foo (x + x) p3) R)) m'')).
  Proof.
    intros.
    repeat split_sep_step.
    repeat merge_du_step.
    reify_disjointness_hyp.

    eapply frobenicate_ok_ramified. (* <- evars created for arguments, but not for frame! *)
    start_canceling.
    canceling_step.
    canceling_step.
    unfold wand.
    unfold canceling.
    unfold seps.
    setoid_rewrite split_du.
    unfold mmap.dus.
    intros.
    repeat split_sep_step.
    repeat merge_du_step.
    reify_disjointness_hyp.
    repeat clear_unused_mem_hyps_step.
    clear m.

    eapply frobenicate_ok_ramified. (* <- evars created for arguments, but not for frame! *)
    start_canceling.
    canceling_step.
    canceling_step.
    unfold wand.
    unfold canceling.
    unfold seps.
    setoid_rewrite split_du.
    unfold mmap.dus.
    intros.
    repeat split_sep_step.
    repeat merge_du_step.
    reify_disjointness_hyp.
    repeat clear_unused_mem_hyps_step.

    rewrite PeanoNat.Nat.sub_diag in *.
    rewrite PeanoNat.Nat.add_0_l in *.
    rewrite PeanoNat.Nat.sub_0_l in *.

    start_canceling.
    repeat canceling_step.
    eapply canceling_done_empty.
  Qed.

  Let foo_pair(v1 v2 a1 a2: nat) := sep (foo v1 a1) (foo v2 a2).

  (* sample caller where argument is a field: *)
  Goal forall (p1 p2 p3 x y: nat) (m: mem) (R: mem -> Prop),
      sep (foo x p1) (sep (foo_pair y x p2 p3) R) m ->
      wp (frobenicate p1 p3) m (fun m' =>
        wp (frobenicate p3 p1) m' (fun m'' =>
           sep (foo 0 p1) (sep (foo_pair y (x + x) p2 p3) R) m'')).
  Proof.
    intros.
    repeat split_sep_step.
    repeat merge_du_step.
    reify_disjointness_hyp.

    eapply frobenicate_ok.
    split. { (* <-- actually, should not split, but canceling mechanism doesn't support
      "seps m /\ Rest" format yet, and it might actually not be needed at all *)
      start_canceling.
      canceling_step.

      (* need to modify hyps while canceling: *)
      unfold foo_pair in H2.
      unfold with_mem in H2.
      split_sep_step.
      replace [Some m2; Some m3] with [Some m1; Some m4; Some m3] by admit.
      (* not literally, but implied by definition of canceling *)
      clear m2 D.

      (* now we can continue canceling: *)
      canceling_step.

      assert_fails (eapply canceling_done_frame).
      (* PROBLEM: Would like to instantiate ?R
         with (fun m => Some m = mmap.dus (Some m1) (Some m4))
         but m1 and m4 are not in ?R's scope!

  H0 : m0 |= foo x p1
  H1 : m1 |= foo y p2
  H4 : m4 |= foo x p3
  H3 : m3 |= R
  ============================
  canceling [?R] [Some m1; Some m3]     *)

  Abort.

  (* sample caller where argument is a field: *)
  Goal forall (p1 p2 p3 x y: nat) (m: mem) (R: mem -> Prop),
      sep (foo x p1) (sep (foo_pair y x p2 p3) R) m ->
      wp (frobenicate p1 p3) m (fun m' =>
        wp (frobenicate p3 p1) m' (fun m'' =>
           sep (foo 0 p1) (sep (foo_pair y (x + x) p2 p3) R) m'')).
  Proof.
    intros.
    repeat split_sep_step.
    repeat merge_du_step.
    reify_disjointness_hyp.

    eapply frobenicate_ok_ramified.
    start_canceling.
    canceling_step.
    unfold foo_pair in H2.
    unfold with_mem in H2.
    split_sep_step.
    replace [Some m2; Some m3] with [Some m1; Some m4; Some m3] by admit.
    (* not literally, but implied by definition of canceling *)
    clear m2 D.
    canceling_step.
    (* here, there's no frame left that we would need to instantiate with
       (fun m => Some m = mmap.dus (Some m1) (Some m4))
       which would violate evar scopes because m1 and m4 were introduced after the frame *)
    unfold wand.
    unfold canceling.
    unfold seps.
    setoid_rewrite split_du.
    unfold mmap.dus.
    intros.
    repeat split_sep_step.
    repeat merge_du_step.
    reify_disjointness_hyp.
    repeat clear_unused_mem_hyps_step.
    clear m.

    (* rest should work as well *)
  Abort.

End HeapletwiseHypsTests.
