Require Import Coq.Logic.PropExtensionality Coq.Logic.FunctionalExtensionality.
Require Import Coq.Lists.List. Import ListNotations. Open Scope list_scope.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.syntactic_unify.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.DisjointUnion.
Require Import bedrock2.TacticError.
Require Import bedrock2.SuppressibleWarnings.
Require Import bedrock2.PurifySep.
Require Import bedrock2.is_emp.
Require Import bedrock2.anyval.
Require Import bedrock2.enable_frame_trick.
Require Import bedrock2.Map.SeparationLogic. Local Open Scope sep_scope.

(* to mark hypotheses about heaplets *)
Definition with_mem{mem: Type}(m: mem)(P: mem -> Prop): Prop := P m.

Declare Scope heapletwise_scope.
Open Scope heapletwise_scope.

Set Ltac Backtrace.

Notation "m |= P" := (with_mem m P) (at level 72) : heapletwise_scope.

Section HeapletwiseHyps.
  Context {key value: Type} {mem: map.map key value} {mem_ok: map.ok mem}
          {key_eqb: key -> key -> bool} {key_eqb_spec: EqDecider key_eqb}
          {value_eqb: value -> value -> bool} {value_eq_dec: EqDecider value_eqb}.

  Lemma split_du: forall (m m1 m2: mem),
      map.split m m1 m2 <-> mmap.du m1 m2 = m.
  Proof.
    unfold map.split, mmap.du, map.du, mmap.of_option. split; intros; fwd.
    - eapply map.disjointb_spec in Hp1. rewrite Hp1. reflexivity.
    - eapply map.disjointb_spec in E0. auto.
  Qed.

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
      exists m1 m2, with_mem m1 P /\ with_mem m2 Q /\ mmap.du m1 m2 = m.
  Proof.
    unfold with_mem, sep, map.split. intros. fwd. do 2 eexists. ssplit.
    1,2: eassumption.
    simpl. unfold map.du. eapply map.disjointb_spec in Hp0p1. rewrite Hp0p1.
    reflexivity.
  Qed.

  Lemma sep_to_with_mem_and_unpacked: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists m1 m2, with_mem m1 P /\ Q m2 /\ mmap.du m1 m2 = m.
  Proof. exact sep_to_with_mem_and_with_mem. Qed.

  Lemma sep_to_unpacked_and_with_mem: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists m1 m2, P m1 /\ with_mem m2 Q /\ mmap.du m1 m2 = m.
  Proof. exact sep_to_with_mem_and_with_mem. Qed.

  Lemma sep_to_unpacked_and_unpacked: forall (P Q: mem -> Prop) m,
      sep P Q m ->
      exists m1 m2, P m1 /\ Q m2 /\ mmap.du m1 m2 = m.
  Proof. exact sep_to_with_mem_and_with_mem. Qed.

  Lemma merge_two_split_equations: forall {m} {om1 om2: mmap mem},
      om1 = mmap.Def m ->
      om2 = mmap.Def m ->
      mmap.equal_union value_eqb om1 om2 = mmap.Def m.
  Proof.
    unfold mmap.equal_union. intros. subst. destr (map.eqb value_eqb m m); congruence.
  Qed.

  Inductive mem_tree :=
  | NEmpty
  | NLeaf(m: mem)
  | NDisjointUnion(t1 t2: mem_tree)
  | NEqualUnion(t1 t2: mem_tree).

  Lemma invert_Some_eq_equal_union: forall m (om1 om2: mmap mem),
      mmap.equal_union value_eqb om1 om2 = mmap.Def m ->
      om1 = mmap.Def m /\ om2 = mmap.Def m.
  Proof.
    unfold mmap.equal_union. intros. fwd. auto.
  Qed.

  Fixpoint interp_mem_tree(t: mem_tree): mmap mem :=
    match t with
    | NEmpty => mmap.Def map.empty
    | NLeaf m => mmap.Def m
    | NDisjointUnion t1 t2 => mmap.du (interp_mem_tree t1) (interp_mem_tree t2)
    | NEqualUnion t1 t2 =>
        mmap.equal_union value_eqb (interp_mem_tree t1) (interp_mem_tree t2)
    end.

  (* sound but not complete (because (NLeaf map.empty)) is considered non-empty *)
  Fixpoint mem_tree_is_empty(t: mem_tree): bool :=
    match t with
    | NEmpty => true
    | NLeaf _ => false
    | NDisjointUnion t1 t2 => andb (mem_tree_is_empty t1) (mem_tree_is_empty t2)
    | NEqualUnion t1 t2 => andb (mem_tree_is_empty t1) (mem_tree_is_empty t2)
    end.

  Lemma mem_tree_is_empty_sound: forall t,
      mem_tree_is_empty t = true ->
      interp_mem_tree t = mmap.Def map.empty.
  Proof.
    induction t; simpl; intros.
    - reflexivity.
    - discriminate.
    - fwd. rewrite IHt1, IHt2 by assumption. apply mmap.du_empty_l.
    - fwd. rewrite IHt1, IHt2 by assumption.
      unfold mmap.equal_union. destruct_one_match; congruence.
  Qed.

  Fixpoint mem_tree_lookup(t: mem_tree)(path: list bool): option mem :=
    match t with
    | NEmpty => None
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

  (* option is for Success/Failure *)
  Fixpoint mem_tree_remove(t: mem_tree)(path: list bool): option mem_tree :=
    match t with
    | NEmpty => None
    | NLeaf m =>
        match path with
        | nil => Some NEmpty
        | cons _ _ => None
        end
    | NDisjointUnion t1 t2 =>
        match path with
        | nil => None (* can only remove leaves *)
        | cons b rest =>
            if b then
              match mem_tree_remove t2 rest with
              | Some NEmpty => Some t1
              | Some t2' => Some (NDisjointUnion t1 t2')
              | None => None
              end
            else
              match mem_tree_remove t1 rest with
              | Some NEmpty => Some t2
              | Some t1' => Some (NDisjointUnion t1' t2)
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

  Lemma canceling_done_nil: forall hs {Rest: Prop},
      mem_tree_is_empty hs = true ->
      Rest ->
      canceling nil (interp_mem_tree hs) Rest.
  Proof.
    unfold canceling. intros. split. 2: assumption. simpl.
    eapply mem_tree_is_empty_sound in H. rewrite H.
    unfold emp. intros. fwd. auto.
  Qed.

  Lemma canceling_done_anymem: forall {om} {Rest: Prop},
      Rest -> canceling [fun _ => True] om Rest.
  Proof.
    unfold canceling. simpl. intros. auto.
  Qed.

  Definition calleePostImpliesCallerPost1(calleePost callerPost F: mem -> Prop): Prop :=
    impl1 (sep calleePost F) callerPost.

  (* The frame evar of a call can always be instantiated with this *)
  Definition genericFrame1(calleePost callerPost: mem -> Prop): mem -> Prop :=
    fun mFrame => calleePostImpliesCallerPost1 calleePost callerPost (eq mFrame).

  Lemma canceling_done_frame_generic1: forall om eeP erP,
      (* No `P (fun mFrame : mem => P (eq mFrame))` hyp that needs to be solved by
         brittle eauto script, but requires specific calleePostImpliesCallerPost1
         shape that isnt' compatible with forall over trace and retvals *)
      (forall mFrame, om = mmap.Def mFrame -> genericFrame1 eeP erP mFrame) ->
      canceling [genericFrame1 eeP erP] om
        (enable_frame_trick (calleePostImpliesCallerPost1 eeP erP (genericFrame1 eeP erP))).
  Proof.
    intros. split. 1: assumption.
    unfold enable_frame_trick, genericFrame1, calleePostImpliesCallerPost1 in *.
    clear.
    unfold impl1, sep.
    intros m Hm. fwd.
    eapply Hmp2.
    do 2 eexists. ssplit.
    2: eassumption.
    1: eassumption.
    reflexivity.
  Qed.

  Definition calleePostImpliesCallerPost2[OtherState: Type]
    (calleePost callerPost: OtherState -> mem -> Prop)(F: mem -> Prop): Prop :=
    forall o m, sep (calleePost o) F m -> callerPost o m.

  (* The frame evar of a call can always be instantiated with this *)
  Definition genericFrame2[OtherState: Type](eeP erP: OtherState -> mem -> Prop) :=
    fun mFrame => calleePostImpliesCallerPost2 eeP erP (eq mFrame).

  Lemma canceling_done_frame_generic2[OtherState: Type]:
    forall om (eeP erP: OtherState -> mem -> Prop),
      (* No `P (fun mFrame : mem => P (eq mFrame))` hyp that needs to be solved by
         brittle eauto script, but requires specific calleePostImpliesCallerPost2
         shape that doesn't usually match: It's required to be
         `sep (calleePost otherstate) F` but usually is `(PureStuff /\ sep (... * F)` *)
      (forall mFrame, om = mmap.Def mFrame -> genericFrame2 eeP erP mFrame) ->
      canceling (cons (genericFrame2 eeP erP) nil) om
        (enable_frame_trick (calleePostImpliesCallerPost2 eeP erP (genericFrame2 eeP erP))).
  Proof.
    intros. split. 1: assumption.
    unfold enable_frame_trick, genericFrame2, calleePostImpliesCallerPost2 in *.
    clear.
    unfold impl1, sep.
    intros o m Hm. fwd.
    eapply Hmp2.
    do 2 eexists. ssplit.
    2: eassumption.
    1: eassumption.
    reflexivity.
  Qed.

  Lemma canceling_done_frame_generic: forall om (P: (mem -> Prop) -> Prop),
      (* This hypothesis holds for all (P F) of the form
         "forall m', (calleePost * F) m' -> callerPost m'"
         even if it has some additional foralls and existentials that can't
         be abstracted easily, so we'll prove this hyp with a generic Ltac *)
      P (fun mFrame : mem => P (eq mFrame)) ->
      (* This hypothesis verifies the rest of the program: *)
      (forall mFrame, om = mmap.Def mFrame -> P (eq mFrame)) ->
      canceling [fun mFrame => P (eq mFrame)] om
        (enable_frame_trick (P (fun mFrame => P (eq mFrame)))).
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

Set Printing Coercions.

  Lemma invert_du_empty: forall (m1 m2: mmap mem),
      mmap.du m1 m2 = mmap.Def map.empty ->
      m1 = map.empty /\ m2 = map.empty.
  Proof.
    unfold mmap.du, mmap.of_option. intros. destruct_one_match_hyp; fwd. 2: discriminate.
    unfold map.du in *. destruct_one_match_hyp. 2: discriminate.
    eapply map.disjointb_spec in E0. fwd. auto.
  Qed.

  Lemma invert_equal_union_empty: forall (m1 m2: mmap mem),
      mmap.equal_union value_eqb m1 m2 = mmap.Def map.empty ->
      m1 = map.empty /\ m2 = map.empty.
  Proof.
    unfold mmap.equal_union, mmap.of_option.
    intros. destruct_one_match_hyp; fwd. 2: discriminate.
    auto.
  Qed.

  Lemma consume_mem_tree: forall {hs hs' path m mFull},
      mem_tree_lookup hs path = Some m ->
      mem_tree_remove hs path = Some hs' ->
      interp_mem_tree hs' = mmap.Def map.empty ->
      interp_mem_tree hs = mmap.Def mFull ->
      m = mFull.
  Proof.
    induction hs; simpl; intros; fwd.
    - discriminate.
    - reflexivity.
    - destruct b; fwd; simpl in *.
      + destruct_one_match_hyp; fwd.
        * rewrite ?H1 in *. rewrite mmap.du_empty_l in *.
          eapply IHhs2; try eassumption. reflexivity.
        * simpl in *. eapply invert_du_empty in H1. fwd.
          eapply IHhs2; try eassumption; try reflexivity.
          rewrite H1p0 in H2. rewrite mmap.du_empty_l in *. assumption.
        * simpl in *. eapply invert_du_empty in H1. fwd.
          eapply invert_du_empty in H1p1. fwd.
          rewrite H1p0 in H2. rewrite mmap.du_empty_l in *.
          eapply IHhs2; try eassumption; try reflexivity.
          simpl. rewrite H1p1p0, H1p1p1. apply mmap.du_empty_l.
        * simpl in *. eapply invert_du_empty in H1. fwd.
          rewrite H1p0 in H2. rewrite mmap.du_empty_l in *.
          eapply invert_equal_union_empty in H1p1. fwd.
          eapply IHhs2; try eassumption; try reflexivity.
          simpl. rewrite H1p1p0, H1p1p1.
          unfold mmap.equal_union. destruct_one_match; congruence.
      + destruct_one_match_hyp; fwd.
        * rewrite ?H1 in *. rewrite mmap.du_empty_r in *.
          eapply IHhs1; try eassumption. reflexivity.
        * set (l := NLeaf m0) in *. cbn -[l] in *.
          eapply invert_du_empty in H1. fwd. subst l.
          simpl in *. fwd.
          eapply IHhs1; try eassumption; try reflexivity.
          rewrite H1p1 in H2. rewrite mmap.du_empty_r in *. assumption.
        * simpl in *. eapply invert_du_empty in H1. fwd.
          eapply invert_du_empty in H1p0. fwd.
          rewrite H1p1 in H2. rewrite mmap.du_empty_r in *.
          eapply IHhs1; try eassumption; try reflexivity.
          simpl. rewrite H1p0p0, H1p0p1. apply mmap.du_empty_l.
        * simpl in *. eapply invert_du_empty in H1. fwd.
          rewrite H1p1 in H2. rewrite mmap.du_empty_r in *.
          eapply invert_equal_union_empty in H1p0. fwd.
          eapply IHhs1; try eassumption; try reflexivity.
          simpl. rewrite H1p0p0, H1p0p1.
          unfold mmap.equal_union. destruct_one_match; congruence.
    - eapply invert_Some_eq_equal_union in H2. fwd.
      destruct b; fwd; eauto.
  Qed.

  Lemma split_mem_tree: forall {hs hs' path m mFull},
      mem_tree_lookup hs path = Some m ->
      mem_tree_remove hs path = Some hs' ->
      interp_mem_tree hs = mmap.Def mFull ->
      mmap.du (interp_mem_tree hs') (mmap.Def m) = mmap.Def mFull.
  Proof.
    induction hs; simpl; intros; fwd.
    - discriminate.
    - simpl. rewrite map.du_empty_l. reflexivity.
    - pose proof H1 as A.
      unfold mmap.du in A. fwd.
      specialize IHhs1 with (3 := eq_refl).
      specialize IHhs2 with (3 := eq_refl).
      destruct b; fwd; destruct_one_match_hyp; fwd; simpl;
      repeat match goal with
      | IH: _, H: mem_tree_lookup _ _ = Some _ |- _ => specialize IH with (1 := H)
      end;
      repeat match goal with
      | IH: _, H: mem_tree_remove _ _ = Some _ |- _ => specialize IH with (1 := H)
      end;
      simpl (interp_mem_tree _) in *;
      rewrite ?mmap.du_empty_l in *;
      fwd;
      rewrite ?E, ?E0.
      1: assumption.
      1-3: try (rewrite <- IHhs2 in H1; rewrite mmap.du_assoc; assumption).
      1: rewrite mmap.du_comm; assumption.
      all: progress rewrite <- IHhs1 in *.
      1: change (mmap.of_option (map.du m2 m1)) with (mmap.du m2 m1).
      all: rewrite mmap.du_assoc.
      all: lazymatch goal with
           | |- mmap.du _ (mmap.du ?a ?b) = _ => rewrite (mmap.du_comm a b)
           end.
      all: rewrite <- mmap.du_assoc.
      all: assumption.
    - eapply invert_Some_eq_equal_union in H1. fwd.
      destruct b; fwd; eauto.
  Qed.

  Lemma cancel_head: forall hs path {P P': mem -> Prop} {Ps hs' m Rest},
      with_mem m P' ->
      impl1 P' P ->
      mem_tree_lookup hs path = Some m ->
      mem_tree_remove hs path = Some hs' ->
      canceling Ps (interp_mem_tree hs') Rest ->
      canceling (P :: Ps) (interp_mem_tree hs) Rest.
  Proof.
    unfold with_mem, canceling. intros. destruct H3 as [H3 HR]. split; [intros |exact HR].
    eapply H0 in H.
    eapply seps_cons.
    pose proof (split_mem_tree H1 H2 H4) as A.
    unfold mmap.du in A. fwd.
    specialize (H3 _ eq_refl).
    eapply split_du in A.
    eapply sep_comm.
    exists m1, m. auto.
  Qed.

  Lemma cancel_pure_head: forall {P: Prop} {Ps om Rest},
      P ->
      canceling Ps om Rest ->
      canceling (emp P :: Ps) om Rest.
  Proof.
    unfold canceling. intros. destruct H0 as [H2 HR]. split; [intros | exact HR].
    eapply seps_cons. eapply sep_emp_l. eauto.
  Qed.

  Lemma cancel_ex1_head: forall {T: Type} {P: T -> mem -> Prop} {Ps om Rest},
      (exists x, canceling (cons (P x) Ps) om Rest) ->
      canceling (cons (ex1 P) Ps) om Rest.
  Proof.
    unfold canceling. intros. destruct H as (x & H & HR). split; [intros | exact HR].
    eapply seps_cons. eapply sep_ex1_l. unfold ex1. subst.
    exists x. eapply seps_cons. eapply H. reflexivity.
  Qed.

  Lemma cancel_sep_head: forall {P Q: mem -> Prop} {Ps om Rest},
      canceling (cons P (cons Q Ps)) om Rest ->
      canceling (cons (sep P Q) Ps) om Rest.
  Proof.
    unfold canceling. intros. destruct H as [H HR]. split; [intros | exact HR].
    simpl in *. subst om. destruct Ps as [ | R Rs]. 1: eauto.
    eapply sep_assoc. eauto.
  Qed.

  Lemma cancel_rew_head: forall {P Q: mem -> Prop} {Ps om Rest},
      impl1 P Q ->
      canceling (cons P Ps) om Rest ->
      canceling (cons Q Ps) om Rest.
  Proof.
    unfold canceling. intros. destruct H0 as [H0 HR]. split; [intros | exact HR].
    specialize (H0 _ H1). eapply seps'_iff1_seps. eapply seps'_iff1_seps in H0.
    simpl in *. revert H0. clear H1. revert m.
    lazymatch goal with
    | |- forall _, ?A _ -> ?B _ => change (impl1 A B)
    end.
    rewrite H. reflexivity.
  Qed.

  Lemma cancel_frame_evar_filling_step: forall hs path {P hs' m F Rest},
      with_mem m P ->
      mem_tree_lookup hs path = Some m ->
      mem_tree_remove hs path = Some hs' ->
      canceling (cons F nil) (interp_mem_tree hs') Rest ->
      canceling (cons (sep P F) nil) (interp_mem_tree hs) Rest.
  Proof.
    intros. eapply cancel_sep_head. eapply cancel_head; try eassumption. reflexivity.
  Qed.

  Lemma canceling_last_step: forall hs path {P P' hs' m} {Rest: Prop},
      with_mem m P' ->
      impl1 P' P ->
      mem_tree_lookup hs path = Some m ->
      mem_tree_remove hs path = Some hs' ->
      mem_tree_is_empty hs' = true ->
      Rest ->
      canceling [P] (interp_mem_tree hs) Rest.
  Proof.
    unfold canceling. simpl. intros. split. 2: assumption.
    intros.
    eapply mem_tree_is_empty_sound in H3.
    pose proof (consume_mem_tree H1 H2 H3 H5) as A. subst. apply H0. assumption.
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

  Definition collecting_heaplets(mAll: mem)(omAvailable: mmap mem)(Ps: list (mem -> Prop)) :=
    exists mUsed, mmap.du omAvailable (mmap.Def mUsed) = mmap.Def mAll /\ seps Ps mUsed.

  Lemma start_collecting_heaplets: forall mAll om,
      om = mmap.Def mAll ->
      collecting_heaplets mAll om nil.
  Proof.
    unfold collecting_heaplets. intros. subst. exists map.empty. split.
    - apply mmap.du_empty_r.
    - unfold seps, emp. auto.
  Qed.

  Lemma done_collecting_heaplets: forall mAll Ps,
      collecting_heaplets mAll (mmap.Def map.empty) Ps ->
      seps Ps mAll.
  Proof.
    unfold collecting_heaplets. intros. subst. fwd.
    unfold mmap.du, mmap.of_option, map.du in *. fwd. subst.
    rewrite map.putmany_empty_l. assumption.
  Qed.

  Lemma step_collecting_heaplets: forall mAll P Ps hs hs' path m,
      with_mem m P ->
      mem_tree_lookup hs path = Some m ->
      mem_tree_remove hs path = Some hs' ->
      collecting_heaplets mAll (interp_mem_tree hs) Ps ->
      collecting_heaplets mAll (interp_mem_tree hs') (cons P Ps).
  Proof.
    unfold with_mem, collecting_heaplets.
    intros. destruct H2 as (mUsed & H2 & HmUsed).
    unfold mmap.du, mmap.of_option, map.du in H2. fwd. subst.
    pose proof (split_mem_tree H0 H1 E) as A.
    unfold mmap.du, mmap.of_option, map.du in A. fwd. subst.
    eapply map.disjointb_spec in E1.
    eexists. split.
    2: {
      apply seps'_iff1_seps. simpl. unfold sep, map.split. do 2 eexists.
      ssplit.
      4: apply seps'_iff1_seps; eassumption.
      3: eassumption.
      1: reflexivity.
      eapply map.disjoint_putmany_l. eassumption.
    }
    unfold mmap.du, mmap.of_option, map.du.
    rewrite (proj2 (map.disjointb_spec _ _)).
    { f_equal. eapply map.putmany_assoc. }
    eapply map.disjoint_putmany_r. split.
    + eapply map.disjointb_spec. eassumption.
    + eapply map.disjoint_putmany_l. rewrite map.putmany_comm.
      1: eassumption. apply map.disjoint_comm. eapply map.disjointb_spec. assumption.
  Qed.

  Definition canceling_in_hyp(mAll: mem)(omAvailable: mmap mem)
    (Ps: list (mem -> Prop))(Q: mem -> Prop) :=
    exists mUsed, mmap.du omAvailable (mmap.Def mUsed) = mmap.Def mAll /\
                  forall mp mq, mmap.du (mmap.Def mp) (mmap.Def mUsed) = mmap.Def mq ->
                                seps Ps mp -> Q mq.

  Lemma start_canceling_in_hyp: forall Ps (Q: mem -> Prop) omAll mAll,
      omAll = mmap.Def mAll ->
      (forall m, SeparationLogic.Tree.to_sep Ps m -> Q m) ->
      canceling_in_hyp mAll omAll (SeparationLogic.Tree.flatten Ps) Q.
  Proof.
    unfold canceling_in_hyp. intros. exists map.empty. split.
    - rewrite mmap.du_empty_r. exact H.
    - intros. rewrite mmap.du_empty_r in H1. inversion H1. subst mp. clear H1.
      eapply H0. eapply SeparationLogic.Tree.flatten_iff1_to_sep. assumption.
  Qed.

  Lemma canceling_sep_step_in_hyp: forall mAll om P1 P2 Ps Q,
      canceling_in_hyp mAll om (cons (sep P1 P2) Ps) Q ->
      canceling_in_hyp mAll om (cons P1 (cons P2 Ps)) Q.
  Proof.
    unfold canceling_in_hyp. intros. fwd. eexists. split. 1: eassumption.
    intros * D H. eapply Hp1. 1: eassumption.
    eapply seps'_iff1_seps. simpl.
    eapply seps'_iff1_seps in H. simpl in H.
    eapply sep_assoc. exact H.
  Qed.

  Lemma canceling_step_in_hyp: forall (P: mem -> Prop) Ps Q mAll m path hs1 hs2,
      with_mem m P ->
      mem_tree_lookup hs1 path = Some m ->
      mem_tree_remove hs1 path = Some hs2 ->
      canceling_in_hyp mAll (interp_mem_tree hs1) (cons P Ps) Q ->
      canceling_in_hyp mAll (interp_mem_tree hs2) Ps Q.
  Proof.
    unfold canceling_in_hyp. intros. fwd.
    unfold mmap.du, mmap.of_option in H2p0. fwd.
    epose proof (split_mem_tree H0 H1 E) as A.
    exists (map.putmany m mUsed).
    unfold map.du in E0. fwd.
    unfold mmap.du, mmap.of_option in A. fwd.
    eapply map.disjointb_spec in E1.
    assert (map.disjoint m mUsed) as D. {
      unfold map.du in E2. fwd. eapply map.disjointb_spec in E3.
      unfold map.disjoint in *. intros. eapply E1. 2: eassumption.
      rewrite map.get_putmany_dec. rewrite H2. reflexivity.
    }
    split.
    - unfold map.du in E2. fwd.
      unfold mmap.du, mmap.of_option, map.du.
      eapply map.disjoint_putmany_l in E1. fwd.
      replace (map.disjointb m1 (map.putmany m mUsed)) with true.
      1: rewrite map.putmany_assoc; reflexivity.
      symmetry. eapply map.disjointb_spec. eapply map.disjoint_putmany_r.
      eapply map.disjointb_spec in E3. auto.
    - intros.
      unfold mmap.du, mmap.of_option, map.du in H2. fwd.
      eapply map.disjointb_spec in E4. eapply map.disjoint_putmany_r in E4. fwd.
      eapply H2p1.
      2: {
        eapply SeparationLogic.seps_cons. eapply sep_from_disjointb. 2,3: eassumption.
        eapply map.disjointb_spec. apply map.disjoint_comm. assumption.
      }
      unfold mmap.du, mmap.of_option, map.du.
      replace (map.disjointb (map.putmany m mp) mUsed) with true.
      + rewrite map.putmany_assoc. f_equal. f_equal. eapply map.putmany_comm.
        eapply map.disjoint_comm. assumption.
      + symmetry. eapply map.disjointb_spec. eapply map.disjoint_putmany_l. auto.
  Qed.

  Lemma canceling_emp_in_hyp: forall (P: Prop) (Ps: list (mem -> Prop)) Q mAll om,
      P ->
      canceling_in_hyp mAll om (cons (emp P) Ps) Q ->
      canceling_in_hyp mAll om Ps Q.
  Proof.
    unfold canceling_in_hyp. intros. fwd. eexists. split. 1: eassumption.
    intros. eapply H0p1. 1: eassumption. eapply seps_cons. eapply sep_emp_l.
    split; assumption.
  Qed.

  Lemma canceling_done_in_hyp: forall Q mAll omAvailable,
      canceling_in_hyp mAll omAvailable nil Q ->
      exists m, mmap.du omAvailable (mmap.Def m) = mAll /\ with_mem m Q.
  Proof.
    unfold canceling_in_hyp. intros. fwd. exists mUsed. split. 1: assumption.
    eapply Hp1. 1: eapply mmap.du_empty_l. unfold seps, emp. auto.
  Qed.
End HeapletwiseHyps.

Ltac reify_mem_tree e :=
  lazymatch e with
  | mmap.du ?e1 ?e2 =>
      let t1 := reify_mem_tree e1 in
      let t2 := reify_mem_tree e2 in
      constr:(NDisjointUnion t1 t2)
  | mmap.equal_union _ ?e1 ?e2 =>
      let t1 := reify_mem_tree e1 in
      let t2 := reify_mem_tree e2 in
      constr:(NEqualUnion t1 t2)
  | mmap.Def ?m =>
      lazymatch m with
      | @map.empty ?k ?v ?mem => constr:(@NEmpty k v mem)
      | _ => constr:(NLeaf m)
      end
  end.

Ltac should_unpack P :=
 lazymatch P with
 | sep _ _ => constr:(true)
 | (fun m => Some m = _) => constr:(true)
 | _ => constr:(false)
 end.

Ltac clear_if_dup_or_trivial H :=
  let t := type of H in
  lazymatch t with
  | True => clear H
  | ?x = ?x => clear H
  | _ => match goal with
         | H': t |- _ => tryif constr_eq H H' then fail else clear H
         | |- _ => idtac
         end
  end.

Ltac is_var_b x :=
  match constr:(Set) with
  | _ => let __ := match constr:(Set) with
                   | _ => is_var x
                   end in
         constr:(true)
  | _ => constr:(false)
  end.

Inductive nothing_to_purify: Prop := mk_nothing_to_purify.

(* Returns a proof of the purified (h: pred m) or mk_nothing_to_purify.
   As a side effect, it might pose a warning, so it should not be called inside a try. *)
Ltac purified_hyp_of_pred h pred m :=
  lazymatch is_var_b pred with
  | true => constr:(mk_nothing_to_purify) (* it's probably a frame *)
  | false =>
      let pf := match constr:(Set) with
                (* typeclasses eauto is "more modern" and has unlimited search depth *)
                | _ => constr:(ltac:(typeclasses eauto with purify) : purify pred _)
                | _ => let __ :=
                         match constr:(Set) with
                         | _ => pose_warning (mk_cannot_purify pred)
                         end in
                       constr:(mk_nothing_to_purify)
                end in
      lazymatch type of pf with
      | nothing_to_purify => pf
      | purify pred True => constr:(mk_nothing_to_purify)
      | purify pred ?p => constr:(pf m h)
      end
  end.

(* Returns a proof of the purified (h: t) or mk_nothing_to_purify.
   As a side effect, it might pose a warning, so it should not be called inside a try. *)
Ltac purified_hyp h t :=
  lazymatch t with
  | with_mem ?m ?pred => purified_hyp_of_pred h pred m
  | ?pred ?m =>
      lazymatch type of m with
      | @map.rep (@Interface.word.rep _ _) Byte.byte _ => purified_hyp_of_pred h pred m
      | _ => constr:(mk_nothing_to_purify)
      end
  | _ => constr:(mk_nothing_to_purify)
  end.

Ltac heapletwise_hyp_pre_clear_default h :=
  let t := type of h in
  lazymatch purified_hyp h t with
  | mk_nothing_to_purify => idtac
  | ?pf => let hp := fresh "old_" h "_pure" in pose proof pf as hp;
           clear_if_dup_or_trivial hp
  end.

Ltac heapletwise_hyp_pre_clear_hook H := heapletwise_hyp_pre_clear_default H.

Ltac clear_heapletwise_hyp H :=
  let tH := type of H in
  let m := lazymatch tH with
           | with_mem ?m _ => m
           | _ ?m => m
           | _ => fail 1000 H "has unexpected shape" tH
           end in
  heapletwise_hyp_pre_clear_hook H;
  clear H m.

Ltac clear_heapletwise_hyps :=
  repeat match goal with
         | _: tactic_error _ |- _ => fail 1 (* pose at most one error *)
         | H: with_mem _ _ |- _ => clear_heapletwise_hyp H
         end.

(* can be overridden using ::= *)
Ltac get_pred_of_sep_clause P :=
  lazymatch P with
  | anyval ?pred ?addr => pred
  | ?pred ?val ?addr => pred
  end.

(* can be overridden using ::= *)
Ltac get_addr_of_sep_clause P :=
  lazymatch P with
  | ?pred ?val ?addr => addr
  end.

Ltac same_pred_and_addr P Q :=
  let addr1 := get_addr_of_sep_clause P in
  let addr2 := get_addr_of_sep_clause Q in
  constr_eq addr1 addr2;
  let pred1 := get_pred_of_sep_clause P in
  let pred2 := get_pred_of_sep_clause Q in
  constr_eq pred1 pred2.

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
  match reverse goal with
  | HOld: with_mem ?mOld ?Pold |- _ =>
      tryif constr_eq HOld H then fail (*bad choice of HOld: don't replace H by itself*)
      else same_pred_and_addr Pnew Pold;
      move H before HOld;
      clear_heapletwise_hyp HOld;
      rename H into HOld
  end.

(* Called whenever a new heapletwise hyp is created whose type will get destructed further *)
Ltac new_heapletwise_hyp_hook h t := idtac.

Ltac will_merge_back_later :=
  lazymatch goal with
  | |- canceling ?Ps ?oms True => fail
  | |- canceling ?Ps ?oms _ => idtac
  | |- _ => fail
  end.

(* For hints registered with `Hint Unfold`, used by autounfold *)
Create HintDb heapletwise_always_unfold.

Ltac prove_emp_in h p :=
  eapply (use_is_emp p) in h; [ | solve [ auto with is_emp ] ].

Ltac new_mem_hyp h :=
  let t := type of h in
  let p := lazymatch t with
           | with_mem ?m ?p => p
           | ?p ?m => p
           end in
  lazymatch p with
  | sep _ _ => idtac
  | emp _ => idtac
  | ex1 _ => idtac
  | _ => (tryif will_merge_back_later
          then idtac (* don't simplify empty arrays away because merge step happening later
                        will need it even if empty *)
          else prove_emp_in h p)
         || new_heapletwise_hyp_hook h t
  end.

Ltac split_sep_step_in H :=
    let D := fresh "D" in
    let m1 := fresh "m0" in
    let m2 := fresh "m0" in
    let H1 := fresh "H0" in
    let H2 := fresh "H0" in
    lazymatch type of H with
    | @sep _ _ ?mem ?P ?Q ?parent_m =>
      let unpackP := should_unpack P in
      let unpackQ := should_unpack Q in
      lazymatch constr:((unpackP, unpackQ)) with
      | (true, true) => eapply sep_to_unpacked_and_unpacked in H
      | (false, true) => eapply sep_to_with_mem_and_unpacked in H
      | (true, false) => eapply sep_to_unpacked_and_with_mem in H
      | (false, false) => eapply sep_to_with_mem_and_with_mem in H
      end;
      destruct H as (m1 & m2 & H1 & H2 & D);
      new_mem_hyp H1;
      new_mem_hyp H2;
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

Ltac split_sep_step :=
  lazymatch goal with
  | H: with_mem ?m1 (eq ?m2) |- _ =>
      match goal with
      | H': with_mem m2 _ |- _ => move H' after H
      | |- _ => idtac
      end;
      unfold with_mem in H; subst m1
  | H: sep _ _ _ |- _ =>
      autounfold with heapletwise_always_unfold in H;
      split_sep_step_in H
  | H: with_mem ?m (sep ?P ?Q) |- _ =>
      change (sep P Q m) in H;
      autounfold with heapletwise_always_unfold in H;
      split_sep_step_in H
  end.

Ltac destruct_ex1_as H name :=
  let x := fresh name in destruct H as [x H];
  lazymatch type of H with
  | ?P ?m => lazymatch should_unpack P with
             | true => idtac
             | false => change (with_mem m P) in H
             end
  end.

Ltac destruct_ex1_step :=
  lazymatch goal with
  | H: with_mem ?m (ex1 (fun name => _)) |- _ => destruct_ex1_as H name
  | H: ex1 (fun name => _) ?m            |- _ => destruct_ex1_as H name
  end.

Ltac destruct_emp_step0 H m P :=
  lazymatch goal with
  | D: _ = mmap.Def _ |- _ =>
      destruct H as [? H];
      subst m;
      rewrite ?mmap.du_empty_l, ?mmap.du_empty_r in D;
      lazymatch P with
      | True => clear H
      | _ => idtac
      end
  end.

Ltac destruct_emp_step :=
  lazymatch goal with
  | H: with_mem ?m (emp ?P) |- _ => destruct_emp_step0 H m P
  | H: emp ?P ?m            |- _ => destruct_emp_step0 H m P
  end.

(* usually already done by split_sep_step, but when introducing hyps from the
   frame after a call, separate merging might still be needed: *)
Ltac merge_du_step :=
  match reverse goal with
  | E1: ?om1 = mmap.Def ?m, E2: ?om2 = mmap.Def ?m |- _ =>
      let D := fresh "D" in
      pose proof (merge_two_split_equations E1 E2) as D;
      clear E1 E2
  | E1: ?om1 = @mmap.Def _ _ ?Mem ?m, E2: ?om2 = mmap.Def ?m' |- _ =>
      lazymatch om1 with
      | mmap.du _ _ => idtac
      | mmap.equal_union _ _ _ => idtac
      end;
      lazymatch om2 with
      | mmap.du _ _ => idtac
      | mmap.equal_union _ _ _ => idtac
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

Ltac is_last_canceling_step mempath sepclauses :=
  lazymatch mempath with
  | nil => lazymatch sepclauses with
           | nil => constr:(true)
           | cons _ _ => constr:(false)
           end
  | cons _ _ => constr:(false)
  end.

Ltac cancel_head_with_hyp H :=
  lazymatch goal with
  | |- canceling (cons _ ?Ps) ?om _ =>
      let m := lazymatch type of H with with_mem ?m _ => m end in
      let hs := reify_mem_tree om in
      let p := path_in_mem_tree hs m in
      let lem := lazymatch is_last_canceling_step p Ps with
                 | true => open_constr:(canceling_last_step hs p H)
                 | false => open_constr:(cancel_head hs p H)
                 end in
      eapply lem;
      [ lazymatch goal with
        | |- impl1 ?P ?P => reflexivity (* fast, common path *)
        | |- _ => idtac (* leave implication open for other tactics to pick up *)
        end
      | reflexivity ..
      | cbn [interp_mem_tree] ]
  end.

Ltac decomposing_intro :=
  match goal with
  | |- _ -> ?P =>
      let H := fresh in intro H;
      try (progress (decompose [ex and or] H); clear H)
  | |- forall _, _ => intro
  end.

(* An evar/frame trick inspired by unfolding the definition of magic wand.
   Advantages:
   - Works even if the predicates about the remaining memory contain variables
     that are not in the evar ?R's evar scope
   - Picks the strongest fact that can be said about the frame (what heaplet it equals),
     so if there are multiple assertions (or splits) about the same heaplet, all of
     them are retained
   - Sep clauses that are not used by the callee are not introduced again after the
     call, but stay. This can be important because if they are introduced again
     (by splitting a big sep formula corresponding to the frame), they might undergo
     additional simplification such as detection of emp predicates (eg array of nil),
     which might break a merge_step
   Disadvantage:
   - If ?R occurs somewhere far away, not in ?P, ?R gets instantiated only to P,
     which will be too weak for the other occurrence of ?R far away.
   Because of the disadvantage, this trick should only be used when canceling
   function calls, but not in cases where the disadvantage might matter, such as
   tailrec loop pre and postconditions.
   So we use enable_frame_trick as an opt-in marker. *)
Ltac instantiate_frame_evar_with_remaining_obligation :=
  lazymatch goal with
  | |- canceling (cons ?R nil) ?om (enable_frame_trick ?P) =>
      let P := lazymatch eval pattern R in P with ?f _ => f end in
      eapply (canceling_done_frame_generic om P);
      [ solve [clear; unfold sep, ex1; repeat decomposing_intro; eauto 40] | ]
  end.

(* both x and y may contain evars, but only evars in y will be instantiated *)
Ltac syntactic_unify_only_inst_r x y :=
  first
    [ is_evar y; unify x y
    | lazymatch x with
      | ?f ?a => lazymatch y with
                 | ?g ?b => syntactic_unify_only_inst_r f g;
                            syntactic_unify_only_inst_r a b
                 end
      | _ => constr_eq x y
      end ].

(* can be overridden with ::=, and can accept clause pairs that need a proof
   produced by tactics outside this file (canceling will just leave a goal open) *)
Ltac hyp_clause_matches_goal_clause hypClause goalClause :=
  syntactic_unify_only_inst_r hypClause goalClause.

Ltac canceling_step :=
  lazymatch goal with
  | |- canceling [fun _ => True] _ _ => eapply canceling_done_anymem
  | |- canceling (cons ?R ?Ps) ?om _ =>
      tryif is_evar R then
        lazymatch Ps with
        | nil =>
            match goal with
            | |- _ => instantiate_frame_evar_with_remaining_obligation
            | H: with_mem ?m ?PH |- _ =>
                let hs := reify_mem_tree om in
                let p := path_in_mem_tree hs m in
                let lem := lazymatch p with
                           | nil => open_constr:(canceling_last_step hs p H impl1_refl)
                           | cons _ _ => open_constr:(cancel_frame_evar_filling_step hs p H)
                           end in
                eapply lem;
                [ reflexivity ..
                | cbn [interp_mem_tree] ]
            end
        | cons _ _ => fail 1000 "frame evar must be last in list"
        end
      else
        lazymatch R with
        | emp _ => eapply cancel_pure_head
        | ex1 _ => eapply cancel_ex1_head
        | sep _ _ => eapply cancel_sep_head
        | _ => match R with
               | _ =>
                   match goal with
                   | H: with_mem _ ?P' |- _ =>
                       hyp_clause_matches_goal_clause P' R; cancel_head_with_hyp H
                   end
               | anyval ?p ?a =>
                   (* to make sure we don't create an evar too early, we only do
                      this step if we can also find a matching hypothesis *)
                   eapply cancel_ex1_head;
                   eexists;
                   match goal with
                   | H: with_mem _ ?P' |- canceling (cons ?R ?Ps) ?om ?P =>
                       hyp_clause_matches_goal_clause P' R; cancel_head_with_hyp H
                   end
               end
        end
  | |- canceling nil ?om _ =>
      let hs := reify_mem_tree om in
      eapply (canceling_done_nil hs eq_refl)
  | |- True => constructor
  end.

Ltac intro_step :=
  lazymatch goal with
  | m: ?mem, H: @with_mem ?mem _ _ |- forall (_: ?mem), _ =>
      let m' := fresh "m0" in intro m'; move m' before m
  | HOld: _ = mmap.Def ?mOld |- _ = mmap.Def _ -> _ =>
      let tmp := fresh "tmp" in
      intro tmp; move tmp before HOld; clear mOld HOld; rename tmp into HOld;
      rewrite ?mmap.du_empty_l, ?mmap.du_empty_r in HOld
  | H: with_mem _ _ |- sep _ _ _ -> _ =>
      let H' := fresh "H0" in
      intro H'; move H' before H
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

Ltac collecting_heaplets_step D :=
  lazymatch type of D with
  | collecting_heaplets ?mAll ?om ?Ps =>
      let hs := reify_mem_tree om in
      lazymatch goal with
      | H: with_mem ?m ?P |- _ =>
          let p := match constr:(Set) with
                   | _ => path_in_mem_tree hs m
                   | _ => constr:(tt)
                   end in
          lazymatch p with
          | tt => idtac
          | _ => eapply (step_collecting_heaplets mAll P Ps hs _ p m H) in D;
                 [ | reflexivity | reflexivity ];
                 cbn [interp_mem_tree] in D
          end;
          clear m H
      end
  end.

Ltac collect_heaplets_into_one_sepclause :=
  lazymatch goal with
  | D: _ = mmap.Def _ |- _ =>
      eapply start_collecting_heaplets in D;
      repeat collecting_heaplets_step D;
      eapply done_collecting_heaplets in D
  end.

Ltac start_canceling_in_hyp H :=
  repeat lazymatch type of H with
    | forall m, ?A m -> ?B m => fail (* done *)
    | forall (_: ?A), _ => let x := lazymatch open_constr:(_: A) with ?x => x end in
                           specialize (H x)
    end;
  lazymatch type of H with
  | forall m, ?A m -> ?B m =>
      let clausetree := SeparationLogic.reify A in
      change (forall m, SeparationLogic.Tree.to_sep clausetree m -> B m) in H;
      lazymatch goal with
      | D: _ = @mmap.Def ?key ?value ?mem _ |- _ =>
          let mok := constr:(_: map.ok mem) in
          let spec := constr:(_: forall (x y: key), BoolSpec (x = y) (x <> y) (_ x y)) in
          eapply (start_canceling_in_hyp (mem_ok := mok) (key_eqb_spec := spec)
                    clausetree _ _ _ D) in H;
          clear D;
          cbn [SeparationLogic.Tree.flatten
               SeparationLogic.Tree.interp
               bedrock2.Map.SeparationLogic.app] in H
      end
  end.

Ltac canceling_step_in_hyp C :=
  lazymatch type of C with
  | canceling_in_hyp ?mAll ?om (cons (emp ?P) ?Ps) ?Q =>
      eapply canceling_emp_in_hyp in C;
      [ | lazymatch goal with
          | H: P |- P => exact H
          | |- True => constructor
          | _ => clear C (* leave open for manual proving *)
          end ]
  | canceling_in_hyp ?mAll ?om (cons (sep ?P1 ?P2) ?Ps) ?Q =>
      eapply canceling_sep_step_in_hyp in C
  | canceling_in_hyp ?mAll ?om (cons ?P ?Ps) ?Q =>
      let H := match goal with
               | H: with_mem _ ?P' |- _ =>
                   let __ := match constr:(Set) with
                             |  _ => syntactic_unify_only_inst_r P' P
                             end in H
               end in
      let m := lazymatch type of H with with_mem ?m _ => m end in
      let hs := reify_mem_tree om in
      let p := path_in_mem_tree hs m in
      eapply (canceling_step_in_hyp P Ps Q mAll m p hs _ H) in C;
      [ | reflexivity | reflexivity];
      cbn [interp_mem_tree] in C;
      clear H; try clear m
  end.

Ltac cancel_in_hyp H :=
  start_canceling_in_hyp H;
  repeat canceling_step_in_hyp H;
  eapply canceling_done_in_hyp in H;
  destruct H as (?m & ?D & ?H).

Section HeapletwiseHypsTests.
  Context {key value: Type} {mem: map.map key value} {mem_ok: map.ok mem}
          {key_eqb: key -> key -> bool} {key_eqb_spec: EqDecider key_eqb}
          {value_eqb: value -> value -> bool} {value_eq_dec: EqDecider value_eqb}.

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
      (calleePre /\ enable_frame_trick
         (forall t' m' l' rets,
             calleePost t' m' rets -> update_locals l rets l' -> callerPost t' m' l')) ->
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
        progress (replace v with v' in H by Lia.lia)
    | |- _ => progress fwd
    | |- wp (cmd_call frobnicate _) _ _ _ _ => eapply wp_call; [eapply frobnicate_ok | ]
    | H: ?P |- ?P => exact H
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
    (* just for testing, join them back together: *)
    collect_heaplets_into_one_sepclause. cbn [seps] in D.
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
    step.
    step.
  Succeed Qed. Abort.

  Goal forall m v1 v2 v3 v4 (Rest: mem -> Prop),
      (sep (scalar v1 1) (sep (sep (scalar v2 2) (scalar v3 3)) (sep (scalar v4 4) Rest))) m ->
      exists R a4, sep (ex1 (fun a3 => sep (scalar a4 4) (scalar a3 3))) R m.
  Proof.
    clear frobnicate frobnicate_ok wp_call update_locals wp call cmd_call.
    step. step. step. step. step. step. step. step. step. step. step. step. step.
    (* now we start canceling, but still with an ex1 inside the list: *)
    step.
    step. (* ex1 *)
    eexists.
    step. (* sep *)
    step. step. step. step. step. step.
  Succeed Qed. Abort.

  Goal forall v1 a1 v2 a2 (P: Prop),
      P ->
      impl1 (sep (scalar v2 a2) (scalar v1 a1))
            (sep (scalar v1 a1) (sep (scalar v2 a2) (emp P))).
  Proof.
    unfold impl1. intros. repeat step.
  Qed.

  Goal forall (P R1 R2: mem -> Prop),
      P = emp True ->
      impl1 (sep (sep P P) (sep R1 R2)) (sep R2 R1).
  Proof.
    intros *. intros ? m ?.
    step. step. step. step. step.
    subst P.
    step. step. step.
    (* after removing m2 from ((map.empty \*/ map.empty) \*/ m2), the memory is
       not literally empty, but it's (map.empty \*/ map.empty) *)
    step. step.
  Succeed Qed. Abort.

  (* sample caller: *)
  Goal forall (p1 p2 p3 x y: nat) t (m: mem) l (R: mem -> Prop),
      sep (scalar x p1) (sep (scalar y p2) (sep (scalar x p3) R)) m ->
      wp (cmd_call frobnicate [p1; p3]) t m l (fun t m l =>
        wp (cmd_call frobnicate [p3; p1]) t m l (fun t m l =>
           exists res,
           sep (scalar 0 p1) (sep (scalar y p2) (sep (scalar res p3) R)) m)).
  Proof.
    repeat step.
  Succeed Qed. Abort.

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
    lazymatch goal with
    | |- canceling _ _ _ => fail "should not be canceling any more"
    | |- forall _, _ => idtac
    end.
    step. step. step. step. step. step. step. step. step. step. step. step. step.

    repeat step.
  Succeed Qed. Abort.

  Goal let nonzeroscalar := fun v a => sep (scalar v a) (emp (0 < a)%nat) in
       forall v a m R, sep (nonzeroscalar v a) R m -> sep (scalar v a) R m.
  Proof.
    intros.
    repeat step.
    unfold nonzeroscalar, with_mem in H0.
    step. step. (* now we have a map.empty in the heaplets passed to canceling! *)
    step. (* map.empty gets deleted *)
    step. step.
  Succeed Qed. Abort.

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
  Succeed Qed. Abort.
End HeapletwiseHypsTests.
