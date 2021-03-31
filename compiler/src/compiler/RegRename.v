Require Import Coq.ZArith.ZArith.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.simpl_rewrite.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Z.Lia.
Require Import coqutil.Macros.unique.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Solver.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.TestLemmas.
Require Import bedrock2.Syntax.
Require Import coqutil.Datatypes.ListSet.
Require Import coqutil.Tactics.Simp.
Require Import coqutil.Tactics.ParamRecords.
Require Import compiler.Simulation.

Open Scope Z_scope.

Notation "'bind_opt' x <- a ; f" :=
  (match a with
   | Some x => f
   | None => None
   end)
  (right associativity, at level 70, x pattern).

Section RegAlloc.

  Context {src2imp: map.map String.string Z}.
  Context {src2impOk: map.ok src2imp}.

  Local Notation srcvar := String.string (only parsing).
  Local Notation impvar := Z (only parsing).
  Local Notation stmt  := (@FlatImp.stmt srcvar). (* input type *)
  Local Notation stmt' := (@FlatImp.stmt impvar). (* output type *)

  Definition rename_assignment_lhs(m: src2imp)(x: srcvar)(a: impvar):
    option (src2imp * impvar * impvar) :=
    match map.get m x with
    | Some y => Some (m, y, a)
    | None   => Some (map.put m x a, a, a + 1)
    end.

  Definition rename_assignment_rhs(m: src2imp)(s: stmt)(y: impvar): option stmt' :=
    match s with
    | SLoad sz x a ofs => bind_opt a' <- map.get m a; Some (SLoad sz y a' ofs)
    | SInlinetable sz x t i => bind_opt i' <- map.get m i; Some (SInlinetable sz y t i')
    | SLit x v => Some (SLit y v)
    | SOp x op a b => bind_opt a' <- map.get m a; bind_opt b' <- map.get m b;
                      Some (SOp y op a' b')
    | SSet x a => bind_opt a' <- map.get m a; Some (SSet y a')
    | _ => None
    end.

  Fixpoint rename_binds(m: src2imp)(binds: list srcvar)(a: impvar):
    option (src2imp * list impvar * impvar) :=
    match binds with
    | nil => Some (m, nil, a)
    | x :: binds =>
      bind_opt (m, y, a) <- rename_assignment_lhs m x a;
      bind_opt (m, res, a) <- rename_binds m binds a;
      Some (m, y :: res, a)
    end.

  Definition rename_cond(m: src2imp)(cond: @bcond srcvar): option (@bcond impvar) :=
    match cond with
    | CondBinary op x y => bind_opt x' <- map.get m x;
                           bind_opt y' <- map.get m y;
                           Some (CondBinary op x' y')
    | CondNez x => bind_opt x' <- map.get m x; Some (CondNez x')
    end.

  (* The simplest dumbest possible "register allocator": Just renames, according to
     a global mapping m being constructed as we go.
     Returns None if not enough registers. *)
  Fixpoint rename
           (m: src2imp)              (* current mapping, growing *)
           (s: stmt)                 (* current sub-statement *)
           (a: impvar)               (* smallest available register, increasing *)
           {struct s}
    : option (src2imp * stmt' * impvar) :=
    match s with
    | SLoad _ x _ _ | SInlinetable _ x _ _ | SLit x _ | SOp x _ _ _ | SSet x _ =>
      bind_opt (m', y, a) <- rename_assignment_lhs m x a;
      bind_opt s' <- rename_assignment_rhs m s y;
      Some (m', s', a)
    | SStore sz x y ofs =>
      bind_opt x' <- map.get m x;
      bind_opt y' <- map.get m y;
      Some (m, SStore sz x' y' ofs, a)
    | SStackalloc x n body =>
      bind_opt (m', y, a') <- rename_assignment_lhs m x a;
      bind_opt (m'', body', a'') <- rename m' body a';
      Some (m'', SStackalloc y n body', a'')
    | SIf cond s1 s2 =>
      bind_opt (m', s1', a') <- rename m s1 a;
      bind_opt (m'', s2', a'') <- rename m' s2 a';
      bind_opt cond' <- rename_cond m cond;
      Some (m'', SIf cond' s1' s2', a'')
    | SSeq s1 s2 =>
      bind_opt (m', s1', a') <- rename m s1 a;
      bind_opt (m'', s2', a'') <- rename m' s2 a';
      Some (m'', SSeq s1' s2', a'')
    | SLoop s1 cond s2 =>
      bind_opt (m', s1', a') <- rename m s1 a;
      bind_opt cond' <- rename_cond m' cond;
      bind_opt (m'', s2', a'') <- rename m' s2 a';
      Some (m'', SLoop s1' cond' s2', a'')
    | SCall binds f args =>
      bind_opt args' <- map.getmany_of_list m args;
      bind_opt (m, binds', a) <- rename_binds m binds a;
      Some (m, SCall binds' f args', a)
    | SInteract binds f args =>
      bind_opt args' <- map.getmany_of_list m args;
      bind_opt (m, binds', a) <- rename_binds m binds a;
      Some (m, SInteract binds' f args', a)
    | SSkip => Some (m, SSkip, a)
    end.

  Definition rename_stmt(m: src2imp)(s: stmt)(av: impvar): option stmt' :=
    bind_opt (_, s', _) <- rename m s av; Some s'.

  (* 0 is the constant 0, 1 is the return address register, 2 is the stack pointer, 3 onward is available *)
  Definition lowest_available_impvar := 3.
  Definition lowest_nonregister := 32.

  Definition rename_fun(F: list srcvar * list srcvar * stmt):
    option (list impvar * list impvar * stmt') :=
    let '(argnames, retnames, body) := F in
    bind_opt (m, argnames', av) <- rename_binds map.empty argnames lowest_available_impvar;
    bind_opt (m, retnames', av) <- rename_binds m retnames av;
    bind_opt (_, body', av) <- rename m body av;
    if Z.leb av lowest_nonregister then Some (argnames', retnames', body') else None.

  Context {W: Utility.Words} {mem: map.map word byte}.
  Context {srcLocals: map.map srcvar word}.
  Context {impLocals: map.map impvar word}.
  Context {srcLocalsOk: map.ok srcLocals}.
  Context {impLocalsOk: map.ok impLocals}.
  Context {srcEnv: map.map String.string (list srcvar * list srcvar * stmt)}.
  Context {impEnv: map.map String.string (list impvar * list impvar * stmt')}.
  Context (ext_spec:  list (mem * String.string * list word * (mem * list word)) ->
                      mem -> String.string -> list word -> (mem -> list word -> Prop) -> Prop).

  Instance srcSemanticsParams: FlatImp.parameters srcvar. refine ({|
    FlatImp.varname_eqb := String.eqb;
    FlatImp.locals := srcLocals;
    FlatImp.ext_spec := ext_spec;
  |}).
  Defined.

  Instance impSemanticsParams: FlatImp.parameters impvar. refine ({|
    FlatImp.varname_eqb := Z.eqb;
    FlatImp.locals := impLocals;
    FlatImp.ext_spec := ext_spec;
  |}).
  Defined.

  Definition rename_functions: srcEnv -> option impEnv :=
    map.map_all_values rename_fun.

  (* Should lH and m have the same domain?
     - lH could have fewer vars in domain because we didn't pass through one branch of the if
     - lH cannot have more vars in its domain because that would mean we don't know where to store
       the value in the target program
     So, (dom lH) subsetOf (dom m) *)
  Definition states_compat(lH: srcLocals)(m: src2imp)(lL: impLocals) :=
    forall (x: srcvar) (v: word),
      map.get lH x = Some v ->
      exists y, map.get m x = Some y /\ map.get lL y = Some v.

  Definition states_compat'(lH: srcLocals)(m: src2imp)(lL: impLocals) :=
    forall (x: srcvar) (y: impvar),
      map.get m x = Some y ->
      map.get lH x = map.get lL y.

  (* slightly stronger: *)
  Definition states_compat''(lH: srcLocals)(m: src2imp)(lL: impLocals) :=
    (forall (x: srcvar) (v: word),
        map.get lH x = Some v ->
        exists y, map.get m x = Some y) /\
    (forall (x: srcvar) (y: impvar),
        map.get m x = Some y ->
        map.get lH x = map.get lL y).

  Lemma states_compat_put_raw: forall lH lL r x y v,
      map.injective r ->
      map.get r x = Some y ->
      states_compat lH r lL ->
      states_compat (map.put lH x v) r (map.put lL y v).
  Proof.
    unfold states_compat. intros.
    rewrite map.get_put_dec in H2.
    destruct_one_match_hyp.
    - subst x0. simp. exists y. rewrite map.get_put_same. auto.
    - unfold map.injective in *.
      specialize H1 with (1 := H2). simp.
      eexists. split; [eassumption|].
      rewrite map.get_put_dec.
      destruct_one_match.
      + subst. specialize H with (1 := H1p0) (2 := H0). congruence.
      + assumption.
  Qed.

  Lemma getmany_of_list_states_compat: forall srcnames impnames r lH lL argvals,
      map.getmany_of_list lH srcnames = Some argvals ->
      map.getmany_of_list r srcnames = Some impnames ->
      states_compat lH r lL ->
      map.getmany_of_list lL impnames = Some argvals.
  Proof.
    induction srcnames; intros;
      destruct argvals as [|argval argvals];
      destruct impnames as [|impname impnames];
      try reflexivity;
      try discriminate;
      unfold map.getmany_of_list, List.option_all in *; simpl in *;
        repeat (destruct_one_match_hyp; try discriminate).
    simp.
    replace (map.get lL impname) with (Some argval); cycle 1. {
      rewrite <- E1.
      unfold states_compat in *. firstorder congruence.
    }
    erewrite IHsrcnames; eauto.
  Qed.

  Lemma putmany_of_list_states_compat: forall r: src2imp,
      map.injective r ->
      forall srcnames impnames lH lH' lL vals,
      map.putmany_of_list_zip srcnames vals lH = Some lH' ->
      map.getmany_of_list r srcnames = Some impnames ->
      states_compat lH r lL ->
      exists lL', map.putmany_of_list_zip impnames vals lL = Some lL' /\
                  states_compat lH' r lL'.
  Proof.
    intros r Inj.
    induction srcnames; intros; simpl in *; simp.
    - exists lL. unfold map.getmany_of_list in H0. simpl in H0. simp.
      simpl. auto.
    - unfold map.getmany_of_list in H0. simpl in H0. simp.
      edestruct IHsrcnames; eauto using states_compat_put_raw.
  Qed.

  Definition envs_related(e1: srcEnv)(e2: impEnv): Prop :=
    forall f impl1,
      map.get e1 f = Some impl1 ->
      exists impl2,
        rename_fun impl1 = Some impl2 /\
        map.get e2 f = Some impl2.

  Lemma rename_assignment_lhs_get{r x av r' i av'}:
    rename_assignment_lhs r x av = Some (r', i, av') ->
    map.get r' x = Some i.
  Proof.
    intros.
    unfold rename_assignment_lhs in *.
    destruct_one_match_hyp; try congruence.
    simp.
    apply map.get_put_same.
  Qed.

  (* domain of m is upper-bounded by bound *)
  Definition dom_bound(m: src2imp)(bound: impvar): Prop :=
    forall k v, map.get m k = Some v -> v < bound.

  Lemma dom_bound_empty: forall bound, dom_bound map.empty bound.
  Proof.
    unfold dom_bound. intros. rewrite map.get_empty in H. discriminate.
  Qed.

  Lemma states_compat_put: forall lH lL r x av r' y av' v,
      map.injective r ->
      dom_bound r av ->
      rename_assignment_lhs r x av = Some (r', y, av') ->
      states_compat lH r lL ->
      states_compat (map.put lH x v) r' (map.put lL y v).
  Proof.
    unfold rename_assignment_lhs, states_compat.
    intros.
    setoid_rewrite map.get_put_dec.
    destruct_one_match_hyp; simp.
    - rewrite map.get_put_dec in H3.
      destruct_one_match_hyp; subst; simp.
      + eexists. split; [eassumption|].
        destruct_one_match; congruence.
      + specialize H2 with (1 := H3). simp.
        eexists. split; [eassumption|].
        destruct_one_match; try congruence.
        subst.
        unfold map.injective in H.
        specialize H with (1 := E) (2 := H2p0). congruence.
    - rewrite map.get_put_dec in H3.
      setoid_rewrite map.get_put_dec.
      unfold dom_bound in *. simp.
      destruct_one_match; subst; simp.
      + eexists. split; [reflexivity|].
        destruct_one_match; subst; simp; congruence.
      + specialize H2 with (1 := H3). simp.
        eexists. split; [eassumption|].
        destruct_one_match; try congruence.
        specialize H0 with (1 := H2p0). exfalso. blia.
  Qed.

  Lemma states_compat_put': forall lH lL r x av r' y av' v,
      map.injective r ->
      dom_bound r av ->
      rename_assignment_lhs r x av = Some (r', y, av') ->
      states_compat' lH r lL ->
      states_compat' (map.put lH x v) r' (map.put lL y v).
  Proof.
    unfold rename_assignment_lhs, states_compat'. intros.
    do 2 rewrite map.get_put_dec.
    destruct_one_match_hyp; simp.
    - specialize H2 with (1 := H3).
      do 2 destruct_one_match; subst; try congruence.
      unfold map.injective in H.
      specialize H with (1 := E) (2 := H3). congruence.
    - rewrite map.get_put_dec in H3.
      unfold dom_bound in *. simp.
      do 2 destruct_one_match; subst; try congruence.
      + specialize H0 with (1 := H3). exfalso. blia.
      + eauto.
  Qed.

  Ltac srew_sidec := first [rewrite map.get_put_same; reflexivity | eauto].
  Ltac srew_h := simpl_rewrite_in_hyps ltac:(fun _ => srew_sidec).
  Ltac srew_g := simpl_rewrite_in_goal ltac:(fun _ => srew_sidec).

  Lemma eval_bcond_compat: forall (lH : srcLocals) r (lL: impLocals) condH condL b,
      rename_cond r condH = Some condL ->
      states_compat lH r lL ->
      @eval_bcond _ srcSemanticsParams lH condH = Some b ->
      @eval_bcond _ impSemanticsParams lL condL = Some b.
  Proof.
    intros.
    unfold rename_cond, eval_bcond in *.
    destruct_one_match_hyp; simp;
      repeat match goal with
             | C: states_compat _ _ _, D: _ |- _ => unique pose proof (C _ _ D)
             end;
      simp;
      simpl_param_projections;
      srew_h; simp; srew_g; reflexivity.
  Qed.

  Lemma eval_bcond_compat_None: forall (lH : srcLocals) r (lL: impLocals) condH condL,
      rename_cond r condH = Some condL ->
      states_compat lH r lL ->
      @eval_bcond _ srcSemanticsParams lH condH <> None ->
      @eval_bcond _ impSemanticsParams lL condL <> None.
  Proof.
    intros.
    match goal with
    | H: ?E1 <> None |- ?E2 <> None => destruct E1 eqn: A1; destruct E2 eqn: A2; try congruence
    end.
    eapply eval_bcond_compat in A1; try eassumption.
    congruence.
  Qed.

  Lemma eval_bcond_compat': forall (lH : srcLocals) r (lL: impLocals) condH condL b,
      rename_cond r condH = Some condL ->
      states_compat' lH r lL ->
      @eval_bcond _ srcSemanticsParams lH condH = Some b ->
      @eval_bcond _ impSemanticsParams lL condL = Some b.
  Proof.
    intros.
    unfold rename_cond, eval_bcond in *.
    destruct_one_match_hyp; simp;
      repeat match goal with
             | C: states_compat' _ _ _, D: _ |- _ => unique pose proof (C _ _ D)
             end;
      simpl_param_projections;
      srew_h; simp; srew_g; reflexivity.
  Qed.

  Lemma states_compat_extends: forall lL lH r1 r2,
      map.extends r2 r1 ->
      states_compat lH r1 lL ->
      states_compat lH r2 lL.
  Proof.
    unfold map.extends, states_compat. intros.
    specialize H0 with (1 := H1). simp.
    eauto.
  Qed.

  (* TODO is this really in no library? *)
  Lemma invert_Forall_app: forall {T: Type} (l1 l2: list T) (P: T -> Prop),
      Forall P (l1 ++ l2) ->
      Forall P l1 /\ Forall P l2.
  Proof.
    induction l1; intros; simpl in *; simp; eauto.
    specialize (IHl1 _ _ H3). simp.
    repeat constructor; eauto.
  Qed.

  Lemma invert_NoDup_app: forall {T: Type} (l1 l2: list T),
      NoDup (l1 ++ l2) ->
      NoDup l1 /\ NoDup l2 /\ forall x, In x l1 -> In x l2 -> False.
  Proof.
    induction l1; intros; simpl in *; simp.
    - repeat constructor; auto.
    - specialize IHl1 with (1 := H3). simp. repeat constructor; try assumption.
      + eauto using in_or_app.
      + intros. destruct H.
        * subst. apply H2. auto using in_or_app.
        * eauto using in_or_app.
  Qed.

  Lemma rename_assignment_lhs_props: forall {x r1 r2 y av1 av2},
      rename_assignment_lhs r1 x av1 = Some (r2, y, av2) ->
      map.injective r1 ->
      dom_bound r1 av1 ->
      map.injective r2 /\
      map.extends r2 r1 /\
      (forall r3 av3, map.extends r3 r2 -> rename_assignment_lhs r3 x av3 = Some (r3, y, av3)) /\
      av1 <= av2 /\
      dom_bound r2 av2 /\
      (forall x y, map.get r2 x = Some y -> av1 <= y < av2 \/ map.get r1 x = Some y) /\
      map.get r2 x = Some y.
  Proof.
    intros.
    unfold rename_assignment_lhs, map.extends, dom_bound in *; intros; simp.
    destruct_one_match_hyp; simp; ssplit; (intuition eauto); srew_g;
      try blia;
      rewrite ?map.get_put_diff by congruence;
      rewrite ?map.get_put_same by congruence;
      eauto;
      try (eapply map.injective_put; firstorder blia).
    - rewrite map.get_put_dec in H. destruct_one_match_hyp; simp; subst; firstorder blia.
    - rewrite map.get_put_dec in H. destruct_one_match_hyp; simp; subst; try blia; eauto.
  Qed.

  (* a list of useful properties of rename_binds, all proved in one induction *)
  Lemma rename_binds_props: forall {bH r1 r2 bL av1 av2},
      rename_binds r1 bH av1 = Some (r2, bL, av2) ->
      map.injective r1 ->
      dom_bound r1 av1 ->
      map.injective r2 /\
      map.extends r2 r1 /\
      (forall r3 av3, map.extends r3 r2 -> rename_binds r3 bH av3 = Some (r3, bL, av3)) /\
      av1 <= av2 /\
      dom_bound r2 av2 /\
      (forall x y, map.get r2 x = Some y -> av1 <= y < av2 \/ map.get r1 x = Some y) /\
      map.getmany_of_list r2 bH = Some bL.
  Proof.
    induction bH; intros; simpl in *; simp.
    - split; [assumption|].
      split; [apply extends_refl|].
      split; [intros; reflexivity|].
      split; [reflexivity|].
      split; [assumption|].
      split; [|reflexivity].
      eauto.
    - specialize IHbH with (1 := E0).
      destruct (rename_assignment_lhs_props E); try assumption. simp.
      apply_in_hyps @invert_NoDup_app. simp.
      edestruct IHbH; eauto. simp.
      split; [assumption|].
      unfold map.extends in *.
      ssplit.
      + intros. eapply extends_trans; eassumption.
      + intros. srew_g. reflexivity.
      + blia.
      + assumption.
      + intros x y A.
        match goal with
        | H: _ |- _ => specialize H with (1 := A); rename H into D
        end.
        destruct D as [D | D].
        * blia.
        * match goal with
          | H: forall _ _ _, _ \/ _ |- _ => specialize H with (1 := D); rename H into D'
          end.
          intuition blia.
      + unfold map.getmany_of_list in *. simpl. srew_g. reflexivity.
  Qed.

  Lemma rename_cond_props: forall {r1 cond cond'},
      rename_cond r1 cond = Some cond' ->
      (forall r3, map.extends r3 r1 -> rename_cond r3 cond = Some cond') /\
      ForallVars_bcond (fun y => exists x : srcvar, map.get r1 x = Some y) cond'.
  Proof.
    unfold rename_cond, ForallVars_bcond, map.extends. split.
    - intros. destruct_one_match; simp; repeat erewrite H0 by eassumption; reflexivity.
    - destruct_one_match_hyp; simp; eauto.
  Qed.

  (* a list of useful properties of rename, all proved in one induction *)
  Lemma rename_props: forall {sH r1 r2 sL av1 av2},
      rename r1 sH av1 = Some (r2, sL, av2) ->
      map.injective r1 ->
      dom_bound r1 av1 ->
      map.injective r2 /\
      map.extends r2 r1 /\
      (forall r3 av3, map.extends r3 r2 -> rename r3 sH av3 = Some (r3, sL, av3)) /\
      av1 <= av2 /\
      dom_bound r2 av2 /\
      (forall x y, map.get r2 x = Some y -> av1 <= y < av2 \/ map.get r1 x = Some y) /\
      ForallVars_stmt (fun y => exists x, map.get r2 x = Some y) sL.
  Proof.
    induction sH; simpl in *; intros; simp;
      apply_in_hyps @rename_assignment_lhs_props; simp;
        try (repeat match goal with
                    | |- _ /\ _ => split
                    end;
             simpl; eauto;
             solve [intros; unfold map.extends in *; srew_g; reflexivity]).
    - (* SStore remainder *)
      unfold map.extends;
            (split; [ (try eapply map.injective_put); eassumption
                    | split;
                      [ idtac
                      | split;
                        [ intros; rewrite ?map.get_put_diff by congruence
                        |  first [ refine (ex_intro _ nil (conj eq_refl _))
                                 | refine (ex_intro _ [_] (conj eq_refl _)) | idtac ]]];
                      eauto]).
      1: srew_g; reflexivity.
      simpl. ssplit; eauto 10.
      reflexivity.
    - (* SStackalloc *)
      specialize IHsH with (1 := E0).
      apply_in_hyps @invert_NoDup_app.
      apply_in_hyps @invert_Forall_app.
      simp.
      auto_specialize. simp.
      split; [assumption|].
      pose proof (rename_assignment_lhs_props E) as P. auto_specialize. simp.
      unfold map.extends in *.
      split; [eauto|].
      split; [intros; srew_g; reflexivity|].
      split; [blia|].
      split; [assumption|].
      split. 2: simpl; eauto.
      (*firstorder blia. too slow and fails, COQBUG https://github.com/coq/coq/issues/12687 *)
      intros x' y A.
      match goal with
      | H: _ |- _ => specialize H with (1 := A); rename H into D
      end.
      destruct D as [D | D].
      + intuition blia.
      + match goal with
        | H: forall _ _ _, _ \/ _ |- _ => specialize H with (1 := D); rename H into D'
        end.
        intuition blia.
    - (* SOp *)
      ssplit; simpl; eauto 10.
      intros; unfold map.extends in *; srew_g; reflexivity.
    - (* SIf *)
      specialize IHsH1 with (1 := E). auto_specialize. simp.
      apply_in_hyps @invert_NoDup_app.
      apply_in_hyps @invert_Forall_app.
      simp.
      specialize IHsH2 with (1 := E0). auto_specialize. simp.
      split; [assumption|].
      pose proof (rename_cond_props E1) as P. destruct P.
      unfold map.extends in *.
      split; [eauto|].
      split; [intros; srew_g; reflexivity|].
      split; [blia|].
      split; [assumption|].
      split. 2: {
        simpl. ssplit.
        + eapply ForallVars_bcond_impl. 2: eassumption.
          simpl. intros. simp. eauto.
        + eapply ForallVars_stmt_impl. 2: eassumption.
          simpl. intros. simp. eauto.
        + eauto.
      }
      intros x y A.
      match goal with
      | H: _ |- _ => specialize H with (1 := A); rename H into D
      end.
      destruct D as [D | D].
      + intuition blia.
      + match goal with
        | H: forall _ _ _, _ \/ _ |- _ => specialize H with (1 := D); rename H into D'
        end.
        intuition blia.
    - (* SLoop *)
      specialize IHsH1 with (1 := E). auto_specialize. simp.
      apply_in_hyps @invert_NoDup_app.
      apply_in_hyps @invert_Forall_app.
      simp.
      specialize IHsH2 with (1 := E1). auto_specialize. simp.
      split; [assumption|].
      unfold map.extends in *.
      split; [eauto|].
      pose proof (rename_cond_props E0) as P. destruct P.
      unfold map.extends in *.
      ssplit.
      + intros; srew_g; reflexivity.
      + blia.
      + assumption.
      + intros x y A.
        match goal with
        | H: _ |- _ => specialize H with (1 := A); rename H into D
        end.
        destruct D as [D | D].
        * intuition blia.
        * match goal with
          | H: forall _ _ _, _ \/ _ |- _ => specialize H with (1 := D); rename H into D'
          end.
          intuition blia.
      + simpl. ssplit.
        * eapply ForallVars_bcond_impl. 2: eassumption.
          simpl. intros. simp. eauto.
        * eapply ForallVars_stmt_impl. 2: eassumption.
          simpl. intros. simp. eauto.
        * eauto.
    - (* SSeq *)
      specialize IHsH1 with (1 := E). auto_specialize. simp.
      apply_in_hyps @invert_NoDup_app.
      apply_in_hyps @invert_Forall_app.
      simp.
      specialize IHsH2 with (1 := E0). auto_specialize. simp.
      split; [assumption|].
      unfold map.extends in *.
      split; [eauto|].
      split; [intros; srew_g; reflexivity|].
      ssplit.
      + blia.
      + assumption.
      + intros x y A.
        match goal with
        | H: _ |- _ => specialize H with (1 := A); rename H into D
        end.
        destruct D as [D | D].
        * intuition blia.
        * match goal with
          | H: forall _ _ _, _ \/ _ |- _ => specialize H with (1 := D); rename H into D'
          end.
          intuition blia.
      + simpl. split.
        * eapply ForallVars_stmt_impl. 2: eassumption.
          simpl. intros. simp. eauto.
        * eauto.
    - (* SSkip *)
      repeat split; unfold map.extends in *; eauto.
      simpl. reflexivity.
    - (* SCall *)
      apply_in_hyps @rename_binds_props. simp; ssplit; eauto.
      + intros. pose proof @map.getmany_of_list_extends. srew_g. reflexivity.
      + simpl. split.
        * eapply map.getmany_of_list_in_map. eassumption.
        * eapply map.getmany_of_list_in_map. eapply map.getmany_of_list_extends; eassumption.
    - (* SInteract *)
      apply_in_hyps @rename_binds_props. simp; ssplit; eauto.
      + intros. pose proof @map.getmany_of_list_extends. srew_g. reflexivity.
      + simpl. split.
        * eapply map.getmany_of_list_in_map. eassumption.
        * eapply map.getmany_of_list_in_map. eapply map.getmany_of_list_extends; eassumption.
  Qed.

  Lemma states_compat_putmany_of_list: forall srcvars lH lH' lL r impvars av r' av' values,
      map.injective r ->
      dom_bound r av ->
      rename_binds r srcvars av = Some (r', impvars, av') ->
      states_compat lH r lL ->
      map.putmany_of_list_zip srcvars values lH = Some lH' ->
      exists lL',
        map.putmany_of_list_zip impvars values lL = Some lL' /\
        states_compat lH' r' lL'.
  Proof.
    induction srcvars; intros; simpl in *.
    - simp. eexists. simpl. eauto.
    - simp.
      apply_in_hyps @rename_assignment_lhs_props. simp.
      apply_in_hyps @invert_NoDup_app. simp.
      edestruct IHsrcvars as [lL' ?].
      3: eassumption.
      4: eassumption.
      all: try eassumption.
      1: {
        eapply states_compat_put.
        3: eassumption.
        all: eassumption.
      }
      simp. simpl. eauto.
  Qed.

  Lemma rename_binds_preserves_length: forall vars vars' r r' av av',
      rename_binds r vars av = Some (r', vars', av') ->
      List.length vars' = List.length vars.
  Proof.
    induction vars; intros.
    - simpl in *. simp. reflexivity.
    - simpl in *. simp. simpl. f_equal. eauto.
  Qed.

  Lemma rename_preserves_stmt_size: forall sH r av r' sL av',
      rename r sH av = Some (r', sL, av') ->
      stmt_size sH = stmt_size sL.
  Proof.
    induction sH; intros; simpl in *; simp; simpl;
      erewrite ?IHsH1 by eassumption;
      erewrite ?IHsH2 by eassumption;
      erewrite ?IHsH by eassumption;
      try reflexivity.
    eapply rename_binds_preserves_length in E0.
    eapply map.getmany_of_list_length in E.
    congruence.
  Qed.

  Lemma rename_correct: forall eH eL,
      envs_related eH eL ->
      forall sH t m lH mc post,
      @exec _ srcSemanticsParams eH sH t m lH mc post ->
      forall lL r r' av av' sL,
      map.injective r ->
      dom_bound r av ->
      rename r sH av = Some (r', sL, av') ->
      states_compat lH r lL ->
      @exec _ impSemanticsParams eL sL t m lL mc (fun t' m' lL' mc' =>
        exists lH', states_compat lH' r' lL' /\
                    post t' m' lH' mc').
  Proof.
    induction 2; intros; simpl in *; simp;
      repeat match goal with
             | H: rename_assignment_lhs _ _ _ = _ |- _ =>
               unique pose proof (rename_assignment_lhs_get H)
             | C: states_compat _ _ _, D: _ |- _ => unique pose proof (C _ _ D)
             end;
      simp;
      try solve [
            econstructor; cycle -1; [solve [eauto using states_compat_put]|..];
            simpl_param_projections;
            eauto;
            congruence].

    - (* @exec.interact *)
      apply_in_hyps @rename_binds_props. simp.
      rename l into lH.
      eapply @exec.interact; try eassumption.
      + eapply getmany_of_list_states_compat; eassumption.
      + intros. specialize (H3 _ _ H6). simp.
        pose proof putmany_of_list_states_compat as P.
        specialize P with (1 := E0_uacp0).
        pose proof states_compat_extends as Q.
        specialize Q with (1 := E0_uacp1) (2 := H7).
        specialize P with (3 := Q); clear Q.
        specialize P with (1 := H3p0).
        specialize P with (1 := E0_uacp6).
        simp.
        eauto 10.
    - (* @exec.call *)
      rename l into lH.
      unfold envs_related in *.
      edestruct H as [p R]; [eassumption|].
      destruct p as [[params' rets'] body'].
      unfold rename_fun in R.
      simp.
      apply_in_hyps @rename_binds_props.
      pose proof E1 as E1'.
      apply @rename_binds_props in E1;
        [|eapply map.empty_injective|eapply dom_bound_empty].
      simp.
      pose proof E2 as E2'.
      apply @rename_binds_props in E2; [|assumption..].
      simp.
      apply_in_hyps @rename_props. simp.
      edestruct putmany_of_list_states_compat as [ lLF' [? ?] ].
      2: exact H2.
      1: exact E2p0.
      1: eapply map.getmany_of_list_extends; cycle 1; eassumption.
      { instantiate (1 := map.empty).
        unfold states_compat. intros *. intro A. rewrite map.get_empty in A. discriminate A.
      }
      eapply @exec.call.
      + eassumption.
      + eapply getmany_of_list_states_compat; eassumption.
      + eassumption.
      + eauto.
      + cbv beta. intros. simp.
        specialize H4 with (1 := H10p1). move H4 at bottom. simp.
        edestruct states_compat_putmany_of_list as [ lL' [? ?] ].
        4: exact H8.
        4: eassumption.
        1: assumption.
        2: exact E0.
        1: assumption.
        do 2 eexists. split; [|split].
        * eapply getmany_of_list_states_compat.
          3: eassumption.
          1: eassumption.
          eapply map.getmany_of_list_extends; eassumption.
        * eassumption.
        * eauto.
    - (* @exec.inlinetable *)
      econstructor; cycle -1.
      1: solve [eauto using states_compat_put].
      all: simpl_param_projections; eauto; try congruence.
      assert (z1 = y) by congruence. subst z1.
      destruct (rename_assignment_lhs_props E); try assumption. simp.
      intros C. subst z0.
      match goal with
      | H: _ <> _ |- _ => apply H; clear H
      end.
      match goal with
      | H: map.injective r' |- _ => eapply H; clear H
      end.
      1: eassumption.
      unfold map.extends in *.
      eauto.
    - (* @exec.stackalloc *)
      eapply @exec.stackalloc. 1: eassumption.
      rename H2 into IHexec.
      intros.
      eapply exec.weaken.
      + apply_in_hyps @rename_assignment_lhs_props. simp.
        apply_in_hyps @invert_NoDup_app. simp.
        specialize IHexec with (5 := E0). eapply IHexec; try eassumption.
        eauto using states_compat_put.
      + cbv beta. intros. simp. eauto 10.
    - (* @exec.if_true *)
      eapply @exec.if_true.
      + eauto using eval_bcond_compat.
      + eapply exec.weaken.
        * eapply IHexec; eauto.
        * cbv beta. intros. simp. eexists; split; eauto.
          destruct (rename_props E); try assumption. simp.
          apply_in_hyps @invert_NoDup_app. simp.
          destruct (rename_props E0); try assumption. simp.
          eapply states_compat_extends; cycle 1; eassumption.
    - (* @exec.if_false *)
      eapply @exec.if_false.
      + eauto using eval_bcond_compat.
      + destruct (rename_props E); try assumption. simp.
        apply_in_hyps @invert_NoDup_app. simp.
        destruct (rename_props E0); try assumption. simp.
        apply_in_hyps @invert_NoDup_app. simp.
        eapply IHexec. 3: eassumption. all: try eassumption.
        eapply states_compat_extends; cycle 1; try eassumption.
    - (* @exec.loop *)
      destruct (rename_props E); try assumption. simp.
      apply_in_hyps @invert_NoDup_app. simp.
      destruct (rename_props E1); try assumption. simp.
      apply_in_hyps @invert_NoDup_app. simp.
      rename IHexec into IH1.
      rename H4 into IH2.
      rename H6 into IH12.
      specialize IH1 with (3 := E).
      specialize IH2 with (5 := E1).
      move IH1 at bottom.
      specialize (IH1 lL). auto_specialize.
      assert (rename r' (SLoop body1 cond body2) av' = Some (r', (SLoop s b s0), av')) as R. {
        simpl.
        rewrite H11p1 by assumption.
        rewrite (proj1 (rename_cond_props E0)) by eassumption.
        rewrite H12p1 by apply extends_refl.
        reflexivity.
      }
      simpl in R.
      specialize IH12 with (4 := R). clear R.
      move IH1 at bottom.
      eapply @exec.loop.
      + eapply IH1.
      + cbv beta. intros. simp.
        eauto using eval_bcond_compat_None.
      + cbv beta. intros. simp.
        eexists. split.
        * eapply states_compat_extends; cycle 1; eassumption.
        * move H1 at bottom.
          specialize H1 with (1 := H4p1).
          match type of H1 with
          | ?E <> None => destruct E eqn: A; [|contradiction]
          end.
          clear H1.
          pose proof @eval_bcond_compat as P.
          specialize P with (1 := E0) (2 := H4p0) (3 := A).
          erewrite P in H6.
          simp. eapply H2; try eassumption.
      + cbv beta. intros. simp.
        eapply IH2; try eassumption.
        pose proof @eval_bcond_compat as P.
        specialize H1 with (1 := H4p1).
        match type of H1 with
        | ?E <> None => destruct E eqn: A; [|contradiction]
        end.
        clear H1.
        specialize P with (1 := E0) (2 := H4p0) (3 := A).
        erewrite P in H6.
        simp. reflexivity.
      + cbv beta. intros. simp.
        eapply IH12; try eassumption.
    - (* @exec.seq *)
      destruct (rename_props E); try assumption. simp.
      apply_in_hyps @invert_NoDup_app. simp.
      destruct (rename_props E0); try assumption. simp.
      rename IHexec into IH1, H2 into IH2.
      specialize IH1 with (3 := E).
      specialize IH2 with (4 := E0).
      eapply @exec.seq.
      + eapply IH1; eassumption.
      + cbv beta. intros. simp.
        eapply IH2; try eassumption.
  Qed.

  Definition related(done: bool):
    @FlatImp.SimState _ srcSemanticsParams -> @FlatImp.SimState _ impSemanticsParams -> Prop :=
    fun '(t1, m1, l1, mc1) '(t2, m2, l2, mc2) =>
      t1 = t2 /\
      m1 = m2 /\
      (done = false -> l1 = map.empty /\ l2 = map.empty /\ mc1 = mc2).
      (* TODO could/should also relate l1 and l2 *)

  Lemma renameSim
        (e1: srcEnv)(e2: impEnv)(c1: stmt)(c2: stmt'):
    forall av' r',
      envs_related e1 e2 ->
      rename map.empty c1 lowest_available_impvar = Some (r', c2, av') ->
      simulation (@FlatImp.SimExec _ srcSemanticsParams e1 c1)
                 (@FlatImp.SimExec _ impSemanticsParams e2 c2) related.
  Proof.
    unfold simulation.
    intros *. intros ER Ren.
    intros *. intros R Ex1.
    unfold FlatImp.SimExec, related in *.
    destruct s1 as (((t1 & m1) & l1) & mc1).
    destruct s2 as (((t2 & m2) & l2) & mc2).
    simp.
    pose proof Ren as A.
    apply @rename_props in A;
      [|eapply map.empty_injective|eapply dom_bound_empty].
    specialize (Rp1 eq_refl).
    simp.
    apply_in_hyps @invert_NoDup_app. simp.
    eapply exec.weaken.
    - eapply rename_correct.
      1: eassumption.
      1: eassumption.
      3: {
        eapply Ap2. eapply extends_refl.
      }
      1: eassumption.
      1: eassumption.
      unfold states_compat. intros *. intro B.
      erewrite map.get_empty in B. discriminate.
    - simpl. intros. simp.
      eexists; split; [|eassumption].
      simpl.
      repeat split; try discriminate; eauto.
  Qed.

End RegAlloc.

(* Print Assumptions renameSim. *)
