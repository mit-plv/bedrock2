Require Import Coq.Logic.PropExtensionality Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List. Import ListNotations. Open Scope list_scope.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.syntactic_unify.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.DisjointUnion.
Require Import bedrock2.TacticError.
Require Import bedrock2.PurifySep.
Require Import bedrock2.Map.SeparationLogic. Local Open Scope sep_scope.

(* to mark hypotheses about heaplets *)
Definition with_mem{mem: Type}(m: mem)(P: mem -> Prop): Prop := P m.

Declare Scope heapletwise_scope.
Open Scope heapletwise_scope.

Set Ltac Backtrace.

Notation "m |= P" := (with_mem m P) (at level 72) : heapletwise_scope.

Section HeapletwiseHyps.
  Context {key value: Type} {mem: map.map key value} {mem_ok: map.ok mem}
          {key_eqb: key -> key -> bool} {key_eqb_spec: EqDecider key_eqb}.

  Lemma split_du: forall (m m1 m2: mem),
      map.split m m1 m2 <-> mmap.du m1 m2 = m.
  Proof.
    unfold map.split, mmap.du, map.du, mmap.of_option. split; intros; fwd.
    - eapply map.disjointb_spec in Hp1. rewrite Hp1. reflexivity.
    - eapply map.disjointb_spec in E0. auto.
  Qed.

  Definition anymem: mem -> Prop := fun _ => True.

  Definition wand(P1 P2: mem -> Prop): mem -> Prop :=
    fun mdiff => forall m1 m2, map.split m2 mdiff m1 -> P1 m1 -> P2 m2.

  (* with mmap.du instead of map.split: *)
  Definition wand'(P1 P2: mem -> Prop): mem -> Prop :=
    fun mdiff => forall m1 m2, mmap.du (mmap.Def mdiff) (mmap.Def m1) = mmap.Def m2 ->
                               P1 m1 -> P2 m2.

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
      exists m1 m2, with_mem m1 P /\ with_mem m2 Q /\ m1 \*/ m2 = m.
  Proof.
    unfold with_mem, sep, map.split. intros. fwd. do 2 eexists. ssplit.
    1,2: eassumption.
    simpl. unfold map.du. eapply map.disjointb_spec in Hp0p1. rewrite Hp0p1.
    reflexivity.
  Qed.

  Lemma sep_to_with_mem_and_unpacked: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists m1 m2, with_mem m1 P /\ Q m2 /\ m1 \*/ m2 = m.
  Proof. exact sep_to_with_mem_and_with_mem. Qed.

  Lemma sep_to_unpacked_and_with_mem: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists m1 m2, P m1 /\ with_mem m2 Q /\ m1 \*/ m2 = m.
  Proof. exact sep_to_with_mem_and_with_mem. Qed.

  Lemma sep_to_unpacked_and_unpacked: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists m1 m2, P m1 /\ Q m2 /\ m1 \*/ m2 = m.
  Proof. exact sep_to_with_mem_and_with_mem. Qed.

  Lemma merge_two_split_equations: forall {m} {om1 om2: mmap mem},
      om1 = mmap.Def m ->
      om2 = mmap.Def m ->
      om1 \=/ om2 = mmap.Def m.
  Proof.
    unfold mmap.equal_union. intros. subst. destr (mmap.map__eqb m m); congruence.
  Qed.

  Inductive mem_tree :=
  | NLeaf(m: mem)
  | NDisjointUnion(t1 t2: mem_tree)
  | NEqualUnion(t1 t2: mem_tree).

  Lemma invert_Some_eq_equal_union: forall m (om1 om2: mmap mem),
      mmap.equal_union om1 om2 = mmap.Def m ->
      om1 = mmap.Def m /\ om2 = mmap.Def m.
  Proof.
    unfold mmap.equal_union. intros. fwd. auto.
  Qed.

  Fixpoint interp_mem_tree(t: mem_tree): mmap mem :=
    match t with
    | NLeaf m => mmap.Def m
    | NDisjointUnion t1 t2 => mmap.du (interp_mem_tree t1) (interp_mem_tree t2)
    | NEqualUnion t1 t2 => mmap.equal_union (interp_mem_tree t1) (interp_mem_tree t2)
    end.

  Fixpoint mem_tree_lookup(t: mem_tree)(path: list bool): option mem :=
    match t with
    | NLeaf m =>
        match path with
        | nil => Some m
        | cons _ _ => None
        end
    | NDisjointUnion t1 t2 | NEqualUnion t1 t2 =>
        match path with
        | nil => None
        | cons b rest => mem_tree_lookup (if b then t2 else t1) rest
        end
    end.

  (* outer option is for Success/Failure, inner option is for whether the result
     is empty *)
  Fixpoint mem_tree_remove(t: mem_tree)(path: list bool): option (option mem_tree) :=
    match t with
    | NLeaf m =>
        match path with
        | nil => Some None
        | cons _ _ => None
        end
    | NDisjointUnion t1 t2 =>
        match path with
        | nil => None (* can only remove leaves *)
        | cons b rest =>
            if b then
              match mem_tree_remove t2 rest with
              | Some (Some t2') => Some (Some (NDisjointUnion t1 t2'))
              | Some None => Some (Some t1)
              | None => None
              end
            else
              match mem_tree_remove t1 rest with
              | Some (Some t1') => Some (Some (NDisjointUnion t1' t2))
              | Some None => Some (Some t2)
              | None => None
              end
        end
    | NEqualUnion t1 t2 =>
        match path with
        | nil => None (* can only remove leaves *)
        | cons b rest =>
            (* Note: only one subtree survives (and gets one leaf removed),
               while the other subtree is completely discarded *)
            mem_tree_remove (if b then t2 else t1) rest
        end
    end.

  Definition canceling(Ps: list (mem -> Prop))(om: mmap mem)(Rest: Prop): Prop :=
    (forall m, om = mmap.Def m -> seps Ps m) /\ Rest.

  Lemma canceling_start_and: forall {Ps m om Rest},
      om = mmap.Def m ->
      canceling (Tree.flatten Ps) om Rest ->
      Tree.to_sep Ps m /\ Rest.
  Proof.
    unfold canceling. intros. fwd. split. 2: assumption.
    eapply Tree.flatten_iff1_to_sep. eauto.
  Qed.

  Lemma canceling_start_noand: forall {Ps m om},
      om = mmap.Def m ->
      canceling (Tree.flatten Ps) om True ->
      Tree.to_sep Ps m.
  Proof.
    unfold canceling. intros. fwd. eapply Tree.flatten_iff1_to_sep. eauto.
  Qed.

  Lemma canceling_done_anymem: forall {om} {Rest: Prop},
      Rest -> canceling [anymem] om Rest.
  Proof.
    unfold canceling, anymem. simpl. intros. auto.
  Qed.

  Lemma canceling_done_frame_generic: forall om (P: (mem -> Prop) -> Prop),
      (* This hypothesis holds for all (P F) of the form
         "forall m', (calleePost * F) m' -> callerPost m'"
         even if it has some additional foralls and existentials that can't
         be abstracted easily, so we'll prove this hyp with a generic Ltac *)
      P (fun mFrame : mem => P (eq mFrame)) ->
      (* This hypothesis verifies the rest of the program: *)
      (forall mFrame, om = mmap.Def mFrame -> P (eq mFrame)) ->
      canceling [fun mFrame => P (eq mFrame)] om (P (fun mFrame => P (eq mFrame))).
  Proof.
    intros. split; assumption.
  Qed.

  (* used to instantiate the frame with a magic wand
     (ramification trick to avoid evar scoping issues) *)
  Lemma canceling_done_frame_wand: forall om (calleePost callerPost: mem -> Prop),
      let F := (wand calleePost callerPost) in
      (forall mFrame, om = mmap.Def mFrame -> F mFrame) ->
      canceling [F] om (forall m', sep calleePost F m' -> callerPost m').
  Proof.
    unfold canceling. cbn [seps]. intros. split. 1: assumption.
    change (impl1 (sep calleePost (wand calleePost callerPost)) callerPost).
    eapply wand_mp.
  Qed.

  (* used to instantiate the frame with an unfolded magic wand
     (ramification trick to avoid evar scoping issues) *)
  Lemma canceling_done_frame: forall om (calleePost callerPost: mem -> Prop),
      (forall mNew mModified,
          mmap.du om (mmap.Def mModified) = mmap.Def mNew ->
          calleePost mModified -> callerPost mNew) ->
      (* F is (wand calleePost callerPost) unfolded *)
      let F := (fun mFrame => forall mModified mNew,
                    mmap.du (mmap.Def mFrame) (mmap.Def mModified) = mmap.Def mNew ->
                    calleePost mModified -> callerPost mNew) in
      canceling [F] om (forall m', sep calleePost F m' -> callerPost m').
  Proof.
    intros.
    pose proof (canceling_done_frame_wand om calleePost callerPost) as P.
    rewrite wand_alt in P. eapply P. clear P F.
    unfold wand'. intros. eapply H. 2: eassumption. rewrite H0. assumption.
  Qed.

  Lemma consume_mem_tree: forall {hs path m mFull},
      mem_tree_lookup hs path = Some m ->
      mem_tree_remove hs path = Some None ->
      interp_mem_tree hs = mmap.Def mFull ->
      m = mFull.
  Proof.
    induction hs; simpl; intros; fwd.
    - reflexivity.
    - destruct b; fwd; destruct o; simpl in *; fwd; discriminate.
    - eapply invert_Some_eq_equal_union in H1. fwd.
      destruct b; fwd; eauto.
  Qed.

  Lemma split_mem_tree: forall {hs hs' path m mFull},
      mem_tree_lookup hs path = Some m ->
      mem_tree_remove hs path = Some (Some hs') ->
      interp_mem_tree hs = mmap.Def mFull ->
      mmap.du (interp_mem_tree hs') (mmap.Def m) = mmap.Def mFull.
  Proof.
    induction hs; simpl; intros; fwd.
    - discriminate.
    - unfold mmap.du in H1. fwd.
      destruct b; fwd.
      + destruct o; fwd; simpl.
        * specialize IHhs2 with (1 := H) (2 := E1) (3 := eq_refl).
          rewrite mmap.du_assoc. rewrite IHhs2.
          rewrite E. exact H1.
        * pose proof (consume_mem_tree H E1 E0). subst.
          rewrite E. exact H1.
      + destruct o; fwd; simpl.
        * specialize IHhs1 with (1 := H) (2 := E1) (3 := eq_refl).
          rewrite mmap.du_assoc.
          rewrite (mmap.du_comm (interp_mem_tree hs2) m).
          rewrite <- mmap.du_assoc.
          rewrite IHhs1.
          rewrite E0. exact H1.
        * epose proof (consume_mem_tree H E1 E). subst.
          rewrite E0. rewrite mmap.du_comm. exact H1.
    - eapply invert_Some_eq_equal_union in H1. fwd.
      destruct b; fwd; eauto.
  Qed.

  Lemma cancel_head: forall hs path {P: mem -> Prop} {Ps hs' m Rest},
      with_mem m P ->
      mem_tree_lookup hs path = Some m ->
      mem_tree_remove hs path = Some (Some hs') ->
      canceling Ps (interp_mem_tree hs') Rest ->
      canceling (P :: Ps) (interp_mem_tree hs) Rest.
  Proof.
    unfold with_mem, canceling. intros. destruct H2 as [H2 HR]. split; [intros |exact HR].
    eapply seps_cons.
    pose proof (split_mem_tree H0 H1 H3) as A.
    unfold mmap.du in A. fwd.
    specialize (H2 _ eq_refl).
    eapply split_du in A.
    eapply sep_comm.
    exists m1, m. auto.
  Qed.

  Lemma cancel_pure_head: forall {P: Prop} {Ps om Rest},
      P ->
      canceling Ps om Rest ->
      canceling (emp P :: Ps) om Rest.
  Proof.
    unfold canceling. intros. destruct H0 as [H2 HR]. split; [intros |exact HR].
    eapply seps_cons. eapply sep_emp_l. eauto.
  Qed.

  Lemma canceling_last_step: forall hs path {P m} {Rest: Prop},
      with_mem m P ->
      mem_tree_lookup hs path = Some m ->
      mem_tree_remove hs path = Some None ->
      Rest ->
      canceling [P] (interp_mem_tree hs) Rest.
  Proof.
    unfold canceling. simpl. intros. split. 2: assumption.
    intros.
    pose proof (consume_mem_tree H0 H1 H3) as A. subst. assumption.
  Qed.

  (* for home-made rewrite *)
  Lemma subst_mem_eq(mSmall mBig: mem){omSmall: mmap mem}(C: mmap mem -> mmap mem):
    omSmall = mmap.Def mSmall ->
    C (mmap.Def mSmall) = mmap.Def mBig ->
    C omSmall = mmap.Def mBig.
  Proof. intros. rewrite <- H in H0. exact H0. Qed.

  Lemma sep_from_disjointb: forall m1 m2 (P Q: mem -> Prop),
      map.disjointb m1 m2 = true ->
      P m1 ->
      Q m2 ->
      sep P Q (map.putmany m1 m2).
  Proof.
    intros. unfold sep, map.split. do 2 eexists. eapply map.disjointb_spec in H.
    ssplit. 1: reflexivity. all: eassumption.
  Qed.
End HeapletwiseHyps.

Ltac reify_mem_tree e :=
  lazymatch e with
  | mmap.du ?e1 ?e2 =>
      let t1 := reify_mem_tree e1 in
      let t2 := reify_mem_tree e2 in
      constr:(NDisjointUnion t1 t2)
  | mmap.equal_union ?e1 ?e2 =>
      let t1 := reify_mem_tree e1 in
      let t2 := reify_mem_tree e2 in
      constr:(NEqualUnion t1 t2)
  | mmap.Def ?m => constr:(NLeaf m)
  end.

Ltac should_unpack P :=
 lazymatch P with
 | sep _ _ => constr:(true)
 | (fun m => Some m = _) => constr:(true)
 | _ => constr:(false)
 end.

Ltac clear_if_dup H :=
  let t := type of H in
  match goal with
  | H': t |- _ => tryif constr_eq H H' then fail else clear H
  | |- _ => idtac
  end.

(* Purify H, but if that leads to something non-interesting (just `True` or an already
   known fact), clear H *)
Ltac purify_hyp_instead_of_clearing H :=
  let tHOrig := type of H in
  unfold with_mem in H;
  lazymatch type of H with
  | ?P ?m =>
      tryif is_var P then (
        (* It's a frame, nothing to purify, so just clear.
           If m is used elsewhere (eg in an (eq m) in a frame), we fail, so H remains. *)
        clear H m
      ) else (
        let g := open_constr:(purify P _) in
        let pf := match constr:(Set) with
                  | _ => constr:(ltac:(eauto with purify) : g)
                  | _ => constr:(tt)
                 end in
        lazymatch pf with
        | tt => pose_err Error:(g "can't be solved by" "eauto with purify");
                change tHOrig in H
        | _ => lazymatch g with
               | purify _ True => clear H; try clear m
               | purify _ _ => eapply pf in H; try clear m; clear_if_dup H
               end
        end
      )
  end.

Ltac purify_heapletwise_hyps_instead_of_clearing :=
  repeat match goal with
         | _: tactic_error _ |- _ => fail 1 (* pose at most one error *)
         | H: with_mem _ _ |- _ => purify_hyp_instead_of_clearing H
         end.

(* can be overridden using ::= *)
Ltac same_pred_and_addr P Q :=
  lazymatch P with
  | ?pred ?val1 ?addr =>
      lazymatch Q with
      | pred ?val2 addr => idtac
      end
  end.

(* given a new mem hyp H, replace the corresponding old mem hyp by H *)
Ltac replace_with_new_mem_hyp H :=
  let Pnew := lazymatch type of H with
              | with_mem _ ?Pnew => Pnew
              | ?Pnew ?m => let __ := match constr:(O) with
                                      | _ => change (with_mem m Pnew) in H
                                      end in Pnew
              end in
  lazymatch Pnew with
  | sep _ _ => fail "first destruct the sep"
  | _ => idtac
  end;
  let HOld := match reverse goal with
              | HOld: with_mem ?mOld ?Pold |- _ =>
                  let __ := match constr:(Set) with
                            | _ => tryif constr_eq HOld H then
                                    fail (*bad choice of HOld: don't replace H by itself*)
                                   else same_pred_and_addr Pnew Pold
                            end in HOld
              end in
  move H before HOld;
  purify_hyp_instead_of_clearing HOld;
  (try let HOld' := fresh HOld in rename HOld into HOld' (* fails if HOld got cleared *));
  rename H into HOld.

(* Called whenever a new heapletwise hyp is created whose type is not a star (that will
   get destructed further) *)
Ltac new_heapletwise_hyp_hook h := idtac.

Ltac split_sep_step :=
  let D := fresh "D" in
  let m1 := fresh "m0" in
  let m2 := fresh "m0" in
  let H1 := fresh "H0" in
  let H2 := fresh "H0" in
  lazymatch goal with
  | H: with_mem ?m1 (eq ?m2) |- _ =>
      match goal with
      | H': with_mem m2 _ |- _ => move H' after H
      | |- _ => idtac
      end;
      unfold with_mem in H; subst m1
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
      new_heapletwise_hyp_hook H1;
      new_heapletwise_hyp_hook H2;
      move m1 before parent_m; (* before in direction of movement == below *)
      move m2 before m1;
      try replace_with_new_mem_hyp H1;
      try replace_with_new_mem_hyp H2;
      let E := match goal with
               | E: ?om = mmap.Def ?mBig |- _ =>
                   lazymatch om with
                   | context C[mmap.Def parent_m] => E
                   end
               | |- _ => constr:(tt) (* in first sep destruct step, there's no E yet *)
               end in
      (* re-match, but this time lazily, to preserve error messages: *)
      lazymatch type of E with
      | ?om = mmap.Def ?mBig =>
          lazymatch om with
          | context C[mmap.Def parent_m] =>
              (* home-made rewrite in hyp because we already have context C *)
              eapply (subst_mem_eq parent_m mBig
                        (fun hole: mmap mem =>
                           ltac:(let r := context C[hole] in exact r))
                        D) in E;
              (* (Some parent_m) might also appear in below the line (if canceling) *)
              rewrite <-?D;
              clear parent_m D
          end
      | unit => idtac
      end
  end.

Ltac destruct_ex1_step :=
  lazymatch goal with
  | H: with_mem ?m (ex1 (fun name => _)) |- _ =>
      let x := fresh name in
      destruct H as [x H]
  end.

Ltac destruct_emp_step :=
  lazymatch goal with
  | H: with_mem ?m (emp ?P), D: _ = mmap.Def _ |- _ =>
      destruct H as [? H];
      subst m;
      rewrite ?mmap.du_empty_l, ?mmap.du_empty_r in D
  end.

(* usually already done by split_sep_step, but when introducing hyps from the
   frame after a call, separate merging might still be needed: *)
Ltac merge_du_step :=
  match reverse goal with
  | E1: ?om1 = mmap.Def ?m, E2: ?om2 = mmap.Def ?m |- _ =>
      let D := fresh "D" in
      pose proof (merge_two_split_equations E1 E2) as D;
      clear E1 E2
  | H: map.split _ _ _ |- _ => eapply split_du in H
  | E1: ?om1 = @mmap.Def _ _ ?Mem ?m, E2: ?om2 = mmap.Def ?m' |- _ =>
      lazymatch om1 with
      | mmap.du _ _ => idtac
      | mmap.equal_union _ _ => idtac
      end;
      lazymatch om2 with
      | mmap.du _ _ => idtac
      | mmap.equal_union _ _ => idtac
      end;
      lazymatch om2 with
      | context C[mmap.Def m] =>
          (* home-made rewrite *)
          eapply (subst_mem_eq m m'
                    (fun hole: mmap Mem => ltac:(let r := context C[hole] in exact r))
                    E1) in E2;
          clear m E1
      end
  | H: mmap.Def ?m1 = mmap.Def ?m2 |- _ =>
      is_var m1; is_var m2; apply mmap.eq_of_eq_Def in H; subst m1
  end.

Ltac start_canceling :=
  lazymatch goal with
  | D: _ = mmap.Def ?m |- sep ?P ?Q ?m /\ ?Rest =>
      let clausetree := reify (sep P Q) in change (Tree.to_sep clausetree m /\ Rest);
      eapply (canceling_start_and D)
  | D: _ = mmap.Def ?m |- sep ?P ?Q ?m =>
      let clausetree := reify (sep P Q) in change (Tree.to_sep clausetree m);
      eapply (canceling_start_noand D)
  end;
  cbn [Tree.flatten Tree.interp bedrock2.Map.SeparationLogic.app].

Ltac path_in_mem_tree om m :=
  lazymatch om with
  | NLeaf m => constr:(@nil bool)
  | NLeaf _ => fail "could not find" m "in" om
  | NDisjointUnion ?t1 ?t2 =>
      match constr:(O) with
      | _ => let p := path_in_mem_tree t1 m in constr:(cons false p)
      | _ => let p := path_in_mem_tree t2 m in constr:(cons true p)
      | _ => fail 1 "could not find" m "in" om
      end
  | NEqualUnion ?t1 ?t2 =>
      match constr:(O) with
      | _ => let p := path_in_mem_tree t1 m in constr:(cons false p)
      | _ => let p := path_in_mem_tree t2 m in constr:(cons true p)
      | _ => fail 1 "could not find" m "in" om
      end
  | _ => fail "Expected a mem_tree, but got" om
  end.

Ltac cancel_head_with_hyp H :=
  lazymatch goal with
  | |- canceling (cons _ ?Ps) ?om _ =>
      let m := lazymatch type of H with with_mem ?m _ => m end in
      let hs := reify_mem_tree om in
      let p := path_in_mem_tree hs m in
      let lem := lazymatch Ps with
                 | nil => open_constr:(canceling_last_step hs p H)
                 | cons _ _ => open_constr:(cancel_head hs p H)
                 end in
      eapply lem;
      [ reflexivity
      | reflexivity
      | cbn [interp_mem_tree] ]
  end.

Ltac canceling_step :=
  lazymatch goal with
  | |- canceling [anymem] _ _ => eapply canceling_done_anymem
  | |- canceling (cons ?R ?Ps) ?om ?P =>
      tryif is_evar R then
        lazymatch Ps with
        | nil =>
            let P := lazymatch eval pattern R in P with ?f _ => f end in
            lazymatch P with
            | (fun _ => ?doesNotDependOnArg) => eapply canceling_done_anymem
            | _ => eapply (canceling_done_frame_generic om P);
                   [ solve [clear; unfold sep; intros; fwd; eauto 20] | ]
            end
        | cons _ _ => fail 1000 "frame evar must be last in list"
        end
      else
        lazymatch R with
        | emp _ => eapply cancel_pure_head
        | _ => let H :=
                 match goal with
                 | H: with_mem _ ?P' |- _ =>
                     let __ := match constr:(Set) with _ => syntactic_unify P' R end in H
                 end in
               cancel_head_with_hyp H
        end
  | |- True => constructor
  end.

Ltac intro_step :=
  lazymatch goal with
  | m: ?mem, H: @with_mem ?mem _ _ |- forall (_: ?mem), _ =>
      let m' := fresh "m0" in intro m'; move m' before m
  | HOld: _ = mmap.Def ?mOld |- _ = mmap.Def _ -> _ =>
      let tmp := fresh "tmp" in
      intro tmp; move tmp before HOld; clear mOld HOld; rename tmp into HOld
  | H: with_mem _ _ |- sep _ _ _ -> _ =>
      let H' := fresh "H0" in
      intro H'; move H' before H
  | |- ?Q ?mNew -> ?nondependent_body =>
      let H := fresh "H0" in
      replace_with_new_mem_hyp H
  end.

Ltac and_step :=
  lazymatch goal with
  | |- (fun _ => _ /\ _) _ /\ _ => cbv beta
  | |- ?P /\ _ => is_destructible_and P; eapply and_assoc
  end.

Ltac heapletwise_step :=
  first
    [ intro_step
    | split_sep_step
    | destruct_ex1_step
    | destruct_emp_step
    | merge_du_step
    | and_step
    | start_canceling
    | canceling_step ].

Ltac collect_heaplets_into_one_sepclause M :=
  lazymatch goal with
  | D: _ = mmap.Def ?m |- _ =>
      eassert (_ m) as M;
      unfold mmap.du in D; unfold mmap.of_option, map.du in D; fwd;
      [ solve [ repeat lazymatch goal with
                  | WM: with_mem ?m _ |- _ ?m => exact WM
                  | D: map.disjointb ?m1 ?m2 = true |- _ (map.putmany ?m1 ?m2) =>
                      eapply sep_from_disjointb; [exact D | | ]
                  | |- ?g => fail 2 "no heaplet hypothesis for" g
                  end ]
      | ]
  end;
  repeat match goal with
    | H: with_mem _ _ |- _ => clear H
    | H: map.disjointb _ _ = true |- _ => clear H
    end;
  lazymatch type of M with
  | _ ?putmanys =>
      let m := fresh "m0" in forget putmanys as m;
      let mem := type of m in
      repeat match goal with
        | heaplet: mem |- _ => clear heaplet
        end
  end.

Section HeapletwiseHypsTests.
  Context {key value: Type} {mem: map.map key value} {mem_ok: map.ok mem}
          {key_eqb: key -> key -> bool} {key_eqb_spec: EqDecider key_eqb}.

  Hypothesis scalar: nat -> nat -> mem -> Prop.

  Lemma purify_scalar: forall v a, purify (scalar v a) True.
  Proof. unfold purify. intros. constructor. Qed.
  Hint Resolve purify_scalar: purify.

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
              sep (sep (emp True) (scalar v1 a1)) (sep (scalar v2 a2) R) m ->
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
    step. step. step. step. step. step. step.
    (* split seps into separate hyps: *)
    step. step. step. step.
    (* just for desting, join them back together: *)
    let H := fresh in collect_heaplets_into_one_sepclause H.
    (* and split again: *)
    step. step. step. step.
    (* existentials: *)
    step. step. step.
    start_canceling.

(*
  m, m0, m3, m5, m1, m4 : mem
  v1, v2, v3, v4 : nat
  Rest : mem -> Prop
  H0 : m0 |= scalar v1 1
  H3 : m3 |= scalar v2 2
  H5 : m5 |= scalar v3 3
  H1 : m1 |= scalar v4 4
  H4 : m4 |= Rest
  D : m0 \*/ ((m3 \*/ m5) \*/ (m1 \*/ m4)) = m
  ============================
  canceling [scalar ?a4 4; scalar ?a3 3; ?R] (m0 \*/ ((m3 \*/ m5) \*/ (m1 \*/ m4))) True
*)

    canceling_step.
    canceling_step.
    canceling_step.
    step.
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

  Lemma purify_scalar_pair: forall v1 v2 a1 a2, purify (scalar_pair v1 v2 a1 a2) True.
  Proof. unfold purify. intros. constructor. Qed.
  Hint Resolve purify_scalar_pair : purify.

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

    step. (* <-- substitutes (mmap.Def m2) both in D and in the goal *)
    step.
    step. (* <- instantiates the frame ?R with a P that gets passed itself as an argument,
                see canceling_done_frame_generic *)
    step. step. step. step. step. step. step. step. step. step. step. step. step.

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
