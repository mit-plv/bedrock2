Require Import Coq.Logic.PropExtensionality Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List. Import ListNotations. Open Scope list_scope.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.syntactic_unify.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.DisjointUnion.
Require Import bedrock2.Map.SeparationLogic. Local Open Scope sep_scope.

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

  Definition anymem: mem -> Prop := fun _ => True.

  Definition wand(P1 P2: mem -> Prop): mem -> Prop :=
    fun mdiff => forall m1 m2, map.split m2 mdiff m1 -> P1 m1 -> P2 m2.

  (* with mmap.du instead of map.split: *)
  Definition wand'(P1 P2: mem -> Prop): mem -> Prop :=
    fun mdiff => forall m1 m2, Some m2 = mmap.du (Some mdiff) (Some m1) -> P1 m1 -> P2 m2.

  Lemma wand_alt: wand = wand'.
  Proof.
    extensionality P. extensionality Q. extensionality m.
    eapply propositional_extensionality. unfold wand, wand';
      split; intros; eapply split_du in H0; eauto.
  Qed.

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

  Definition canceling(Ps: list (mem -> Prop))(oms: list (option mem))(Rest: Prop): Prop :=
    (forall m, Some m = mmap.dus oms -> seps Ps m) /\ Rest.

  Lemma canceling_equiv_heaplets: forall Ps oms1 oms2 Rest,
      mmap.dus oms1 = mmap.dus oms2 ->
      canceling Ps oms1 Rest ->
      canceling Ps oms2 Rest.
  Proof. unfold canceling. intros. rewrite <- H. assumption. Qed.

  Lemma canceling_start_and: forall {Ps oms m Rest},
      Some m = mmap.dus oms ->
      canceling Ps oms Rest ->
      seps Ps m /\ Rest.
  Proof.
    unfold canceling. intros. fwd. eauto.
  Qed.

  Lemma canceling_start_noand: forall {Ps oms m},
      Some m = mmap.dus oms ->
      canceling Ps oms True ->
      seps Ps m.
  Proof.
    unfold canceling. intros. fwd. eauto.
  Qed.

  Lemma canceling_done_empty: canceling [] [] True.
  Proof.
    unfold canceling. simpl. intros. split. 2: constructor.
    intros. inversion H. unfold emp. auto.
  Qed.

  Lemma canceling_done_anymem: forall {oms} {Rest: Prop},
      Rest -> canceling [anymem] oms Rest.
  Proof.
    unfold canceling, anymem. simpl. intros. auto.
  Qed.

  Lemma canceling_done_frame_generic: forall oms (P: (mem -> Prop) -> Prop),
      (* This hypothesis holds for all (P F) of the form
         "forall m', (calleePost * F) m' -> callerPost m'"
         even if it has some additional foralls and existentials that can't
         be abstracted easily, so we'll prove this hyp with a generic Ltac *)
      P (fun mFrame : mem => P (eq mFrame)) ->
      (* This hypothesis verifies the rest of the program: *)
      (forall mFrame, Some mFrame = mmap.dus oms -> P (eq mFrame)) ->
      canceling [fun mFrame => P (eq mFrame)] oms (P (fun mFrame => P (eq mFrame))).
  Proof.
    intros. split; assumption.
  Qed.

  (* used to instantiate the frame with a magic wand
     (ramification trick to avoid evar scoping issues) *)
  Lemma canceling_done_frame_wand: forall oms (calleePost callerPost: mem -> Prop),
      let F := (wand calleePost callerPost) in
      (forall mFrame, Some mFrame = mmap.dus oms -> F mFrame) ->
      canceling [F] oms (forall m', sep calleePost F m' -> callerPost m').
  Proof.
    unfold canceling. cbn [seps]. intros. split. 1: assumption.
    change (impl1 (sep calleePost (wand calleePost callerPost)) callerPost).
    eapply wand_mp.
  Qed.

  (* used to instantiate the frame with an unfolded magic wand
     (ramification trick to avoid evar scoping issues) *)
  Lemma canceling_done_frame: forall oms (calleePost callerPost: mem -> Prop),
      (forall mNew mModified,
          Some mNew = mmap.du (mmap.dus oms) (Some mModified) ->
          calleePost mModified -> callerPost mNew) ->
      (* F is (wand calleePost callerPost) unfolded *)
      let F := (fun mFrame => forall mModified mNew,
                    Some mNew = mmap.du (Some mFrame) (Some mModified) ->
                    calleePost mModified -> callerPost mNew) in
      canceling [F] oms (forall m', sep calleePost F m' -> callerPost m').
  Proof.
    intros.
    pose proof (canceling_done_frame_wand oms calleePost callerPost) as P.
    rewrite wand_alt in P. eapply P. clear P F.
    unfold wand'. intros. eapply H. 2: eassumption. rewrite <- H0. assumption.
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

  Lemma cancel_head: forall n {P: mem -> Prop} {Ps oms mn Rest},
      with_mem mn P ->
      heaplets_nth n oms = Some mn ->
      canceling Ps (heaplets_remove_nth n oms) Rest ->
      canceling (P :: Ps) oms Rest.
  Proof.
    unfold with_mem, canceling. intros. destruct H1 as [H1 HR]. split; [intros |exact HR].
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

Ltac replace_with_new_mem_hyp H :=
  lazymatch type of H with
  | with_mem _ (?pred ?val ?addr) =>
      lazymatch reverse goal with
      | HOld: with_mem ?mOld (pred ?newval addr) |- _ =>
          move H before HOld;
          clear mOld HOld;
          rename H into HOld
      end
  end.

Ltac split_sep_step :=
  let D := fresh "D" in
  let m1 := fresh "m0" in
  let m2 := fresh "m0" in
  let H1 := fresh "H0" in
  let H2 := fresh "H0" in
  lazymatch goal with
  | H: with_mem ?m1 (eq ?m2) |- _ => unfold with_mem in H; subst m1
  | H: @sep _ _ ?mem ?P ?Q ?parent_m |- _ =>
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
      move m2 before m1;
      try replace_with_new_mem_hyp H1;
      try replace_with_new_mem_hyp H2;
      let E := match goal with
               | E: @Some (@map.rep _ _ mem) ?mBig = ?rhs |- _ =>
                   lazymatch rhs with
                   | context C[Some parent_m] => E
                   end
               | |- _ => constr:(tt) (* in first sep destruct step, there's no E yet *)
               end in
      (* re-match, but this time lazily, to preserve error messages: *)
      lazymatch type of E with
      | @Some (@map.rep _ _ mem) ?mBig = ?rhs =>
          lazymatch rhs with
          | context C[Some parent_m] =>
              (* home-made rewrite in hyp because we already have context C *)
              eapply (subst_mem_eq parent_m mBig
                        (fun hole: option mem =>
                           ltac:(let r := context C[hole] in exact r))
                        D) in E;
              (* (Some parent_m) might also appear in below the line (if canceling) *)
              rewrite ?D;
              clear parent_m D
          end
      | unit => idtac
      end
  end.

(* usually already done by split_sep_step, but when introducing hyps from the
   frame after a call, separate merging might still be needed: *)
Ltac merge_du_step :=
  match reverse goal with
  | E1: @Some ?Mem ?m = ?rhs1, E2: Some ?m' = ?rhs2 |- _ =>
      lazymatch rhs1 with
      | mmap.du _ _ => idtac
      | mmap.dus _ => cbn [mmap.dus] in E1
      end;
      lazymatch rhs2 with
      | mmap.du _ _ => idtac
      | mmap.dus _ => cbn [mmap.dus] in E2
      end;
      lazymatch rhs2 with
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
  | D: Some ?m = mmap.dus ?oms |- _ =>
      lazymatch oms with
      | context[mmap.du _ _] =>
          cbn [mmap.dus] in D
          (* and next iteration will actually reify it *)
      end
  end.

Ltac rereify_canceling_heaplets :=
  lazymatch goal with
  | |- canceling _ ?oms _ =>
      lazymatch oms with
      | context[mmap.du _ _] => eapply canceling_equiv_heaplets
      end
  end;
  [ cbn [mmap.dus];
    rewrite ?mmap.du_assoc;
    lazymatch goal with
    | |- mmap.dus ?e = ?rhs =>
        is_evar e;
        let r := reify_dus rhs in unify e r
    end;
    reflexivity
  | ].

Ltac start_canceling :=
  rewrite ?sep_assoc_eq;
  (* TODO support multiple D's and a way to pick the right one *)
  lazymatch goal with
  | D: Some ?m = mmap.dus _ |- sep ?eh ?et ?m /\ ?Rest =>
      let clauselist := reify_seps (sep eh et) in change (seps clauselist m /\ Rest);
      eapply (canceling_start_and D)
  | D: Some ?m = mmap.dus _ |- sep ?eh ?et ?m =>
      let clauselist := reify_seps (sep eh et) in change (seps clauselist m);
      eapply (canceling_start_noand D)
  end.

Ltac index_of_Some m oms :=
  lazymatch oms with
  | cons (Some m) _ => constr:(O)
  | cons _ ?tl => let n := index_of_Some m tl in constr:(S n)
  end.

Ltac canceling_step :=
  lazymatch goal with
  | |- canceling (cons ?P ?Ps) ?oms ?Rest =>
      tryif is_evar P then fail "reached frame (or other evar)" else
      let H := match goal with
               | H: with_mem _ ?P' |- _ =>
                   let __ := match constr:(Set) with _ => syntactic_unify P' P end in H
               end in
      let m := lazymatch type of H with with_mem ?m _ => m end in
      let oms := lazymatch goal with |- canceling _ ?oms _ => oms end in
      let n := index_of_Some m oms in
      eapply (cancel_head n H); [ reflexivity | cbn_heaplets ]
  end.

Ltac canceling_done :=
  lazymatch goal with
  | |- canceling [] [] True => eapply canceling_done_empty
  | |- canceling [anymem] _ _ => eapply canceling_done_anymem
  | |- canceling [?R] ?oms ?P =>
      is_evar R;
      let P := lazymatch eval pattern R in P with ?f _ => f end in
      lazymatch P with
      | (fun _ => ?doesNotDependOnArg) => eapply canceling_done_anymem
      | _ => eapply (canceling_done_frame_generic oms P);
             [ clear; unfold sep; intros; fwd; eauto 20 | ]
      end
  end.

Ltac clear_unused_mem_hyps_step :=
  match goal with
  | H: with_mem ?m _ |- _ => clear m H
  end.

Ltac intro_step :=
  lazymatch goal with
  | m: ?mem, H: @with_mem ?mem _ _ |- forall (_: ?mem), _ =>
      let m' := fresh "m0" in intro m'; move m' before m
  | |- Some _ = mmap.dus _ -> _ => cbn [mmap.dus]
  | HOld: Some ?mOld = mmap.dus _ |- Some _ = mmap.du _ _ -> _ =>
      let tmp := fresh "tmp" in
      intro tmp; move tmp before HOld; clear mOld HOld; rename tmp into HOld;
      cbn [mmap.dus] in HOld
  | H: with_mem _ _ |- sep _ _ _ -> _ =>
      let H' := fresh "H0" in
      intro H'; move H' before H
  | H: with_mem ?mOld (?pred ?oldVal ?addr) |- ?pred ?newVal ?addr ?mNew -> _ =>
      let tmp := fresh "tmp" in
      intro tmp;
      move tmp before H;
      clear H mOld;
      rename tmp into H;
      change (with_mem mNew (pred newVal addr)) in H
  end.

Ltac and_step :=
  lazymatch goal with
  | |- (fun _ => _ /\ _) _ /\ _ => cbv beta
  | |- (_ /\ _) /\ _ => eapply and_assoc
  end.

Ltac heapletwise_step :=
  first
    [ intro_step
    | split_sep_step
    | merge_du_step
    | reify_disjointness_hyp
    | and_step
    | start_canceling
    | rereify_canceling_heaplets
    | canceling_step
    | canceling_done ].

Section HeapletwiseHypsTests.
  Context {key value: Type} {mem: map.map key value} {mem_ok: map.ok mem}
          {key_eqb: key -> key -> bool} {key_eqb_spec: EqDecider key_eqb}.

  Hypothesis scalar: nat -> nat -> mem -> Prop.

  Context (fname: Type).
  Context (cmd: Type) (trace: Type) (locals: Type).
  Context (cmd_call: fname -> list nat -> cmd).
  Context (wp: cmd -> trace -> mem -> locals -> (trace -> mem -> locals -> Prop) -> Prop).

  Context (call: fname -> trace -> mem -> list nat ->
                 (trace -> mem -> list nat -> Prop) -> Prop).

  Context (update_locals: locals -> list nat -> locals -> Prop).

  (* each program logic needs to prove & apply a lemma to shoehorn its function specs
     from the definition-site format into the use-site format: *)
  Hypothesis wp_call: forall f t m args l
      (calleePre: Prop)
      (calleePost: trace -> mem -> list nat -> Prop)
      (callerPost: trace -> mem -> locals -> Prop),
      (* definition-site format: *)
      (calleePre -> call f t m args calleePost) ->
      (* use-site format: *)
      (calleePre /\
         forall t' m' l' rets,
           calleePost t' m' rets -> update_locals l rets l' -> callerPost t' m' l') ->
      (* conclusion: *)
      wp (cmd_call f args) t m l callerPost.

  Context (frobnicate: fname).
  Context (frobnicate_ok: forall (a1 a2 v1 v2: nat) t m (R: mem -> Prop),
              sep (scalar v1 a1) (sep (scalar v2 a2) R) m ->
              call frobnicate t m [a1; a2] (fun t' m' rets =>
                   exists d, rets = [d] /\ d <= v1 /\
                   sep (scalar (v1 + v2 + d) a1) (sep (scalar (v1 - v2 - d) a2) R) m')).

  Ltac program_logic_step :=
    match goal with
    | |- forall _, _ => intro
    | H: with_mem _ (scalar ?v ?a) |- canceling (cons (scalar ?v' ?a) _) _ _ =>
        replace v with v' in H by Lia.lia
    | |- _ => progress fwd
    | |- wp (cmd_call frobnicate _) _ _ _ _ => eapply wp_call; [eapply frobnicate_ok | ]
    | |- exists _, _ => eexists
    end.

  Ltac step := first [ heapletwise_step | program_logic_step ].

  Goal forall m v1 v2 v3 v4 (Rest: mem -> Prop),
      (sep (scalar v1 1) (sep (sep (scalar v2 2) (scalar v3 3)) (sep (scalar v4 4) Rest))) m ->
      exists R a4 a3, sep (sep (scalar a4 4) (scalar a3 3)) R m.
  Proof.
    step. step. step. step. step. step. step. step. step. step. step. step. step. step. step.
    start_canceling.

(*
  m, m0, m6, m7, m4, m5 : mem
  v1, v2, v3, v4 : nat
  Rest : mem -> Prop
  H0 : m0 |= scalar v1 1
  H3 : m6 |= scalar v2 2
  H5 : m7 |= scalar v3 3
  H1 : m4 |= scalar v4 4
  H4 : m5 |= Rest
  ============================
  canceling [scalar ?a4 4; scalar ?a3 3; ?R] [Some m0; Some m6; Some m7; Some m4; Some m5] True
*)

    repeat canceling_step.
    eapply (canceling_done_anymem I).
  Qed.

  (* sample caller: *)
  Goal forall (p1 p2 p3 x y: nat) t (m: mem) l (R: mem -> Prop),
      sep (scalar x p1) (sep (scalar y p2) (sep (scalar x p3) R)) m ->
      wp (cmd_call frobnicate [p1; p3]) t m l (fun t m l =>
        wp (cmd_call frobnicate [p3; p1]) t m l (fun t m l =>
           exists res,
           sep (scalar 0 p1) (sep (scalar y p2) (sep (scalar res p3) R)) m)).
  Proof.
    repeat step.
  Qed.

  Let scalar_pair(v1 v2 a1 a2: nat) := sep (scalar v1 a1) (scalar v2 a2).

  (* sample caller where argument is a field: *)
  Goal forall (p1 p2 p3 x y: nat) t m l (R: mem -> Prop),
      sep (scalar x p1) (sep (scalar_pair y x p2 p3) R) m ->
      wp (cmd_call frobnicate [p1; p3]) t m l (fun t m l =>
        wp (cmd_call frobnicate [p3; p1]) t m l (fun t m l =>
           exists res, (* TODO: scalar_pair in postcondition *)
           sep (scalar 0 p1) (sep (scalar y p2) (sep (scalar res p3) R)) m)).
  Proof.
    repeat step.

    (* unfolding/splitting hyp during cancellation: *)
    unfold scalar_pair in H2.
    unfold with_mem in H2.

    step. step. step. step. step.
    step. (* <- instantiates the frame ?R with a P that gets passed itself as an argument,
                see canceling_done_frame_generic *)

    repeat step.
  Qed.

(* sample unfolded spec of indirect_add:

    forall (a b c va : word) (Ra : mem -> Prop) (vb : word)
         (Rb : mem -> Prop) (vc : word) (Rc : mem -> Prop) (t : trace)
         (m : mem),
       (scalar a va ⋆ Ra)%sep m /\ (scalar b vb ⋆ Rb)%sep m /\ (scalar c vc ⋆ Rc)%sep m ->
       call functions "indirect_add" t m [a; b; c]
         (fun (t' : trace) (m' : mem) (rets : list word) =>
          rets = [] /\ t = t' /\ (scalar a (word.add vb vc) ⋆ Ra)%sep m')

*)

  Context (aliasing_add: fname).
  Hypothesis aliasing_add_ok: forall a b c va vb vc (Ra Rb Rc: mem -> Prop) t m,
      sep (scalar va a) Ra m /\
      sep (scalar vb b) Rb m /\
      sep (scalar vc c) Rc m ->
      call aliasing_add t m [c; a; b] (fun t' m' rets =>
        sep (scalar (va + vb) c) Rc m').

  Goal forall x y z vx vy vz (R: mem -> Prop) t m l,
      sep (scalar vx x) (sep (scalar vy y) (sep (scalar vz z) R)) m ->
      wp (cmd_call aliasing_add [x; y; z]) t m l (fun t m l =>
        wp (cmd_call aliasing_add [x; y; y]) t m l (fun t m l =>
          wp (cmd_call aliasing_add [x; x; z]) t m l (fun t m l =>
            wp (cmd_call aliasing_add [x; x; x]) t m l (fun t m l =>
              sep (scalar (vy + vy + vz + (vy + vy + vz)) x)
                (sep (scalar vy y) (sep (scalar vz z) R)) m)))).
  Proof.
    clear frobnicate frobnicate_ok scalar_pair.
    intros.
    repeat step.
    eapply wp_call. 1: eapply aliasing_add_ok.
    repeat step.
    eapply wp_call. 1: eapply aliasing_add_ok.
    repeat step.
    eapply wp_call. 1: eapply aliasing_add_ok.
    repeat step.
    eapply wp_call. 1: eapply aliasing_add_ok.
    repeat step.
  Qed.

End HeapletwiseHypsTests.
