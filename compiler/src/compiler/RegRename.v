Require Import Coq.ZArith.ZArith.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.simpl_rewrite.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Macros.unique.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Solver.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.TestLemmas.
Require Import bedrock2.Syntax.
Require Import coqutil.Datatypes.ListSet.
Require Import compiler.Simp.
Require Import compiler.Simulation.


Notation "'bind_opt' x <- a ; f" :=
  (match a with
   | Some x => f
   | None => None
   end)
  (right associativity, at level 70, x pattern).

Module map.
  Definition injective{K V: Type}{M: map.map K V}(m: M): Prop :=
    forall k1 k2 v,
      map.get m k1 = Some v -> map.get m k2 = Some v -> k1 = k2.

  (* Alternative:
  Definition injective{K V: Type}{M: map.map K V}(m: M): Prop :=
    forall k1 k2 v1 v2,
      k1 <> k2 -> map.get m k1 = Some v1 -> map.get m k2 = Some v2 -> v1 <> v2.
  *)

  Lemma injective_put{K V: Type}{M: map.map K V}{ok: map.ok M}
        {key_eqb: K -> K -> bool}{key_eq_dec: EqDecider key_eqb}:
    forall (m: M) k v,
      (forall k, map.get m k <> Some v) ->
      map.injective m ->
      map.injective (map.put m k v).
  Proof.
    unfold map.injective.
    intros.
    rewrite map.get_put_dec in H1.
    rewrite map.get_put_dec in H2.
    do 2 destruct_one_match_hyp; try congruence.
    eauto.
  Qed.

  Definition not_in_range{K V: Type}{M: map.map K V}(m: M)(l: list V): Prop :=
    List.Forall (fun v => forall k, map.get m k <> Some v) l.

  Lemma empty_injective{K V: Type}{M: map.map K V}{ok: map.ok M}:
      map.injective map.empty.
  Proof. unfold injective. intros. rewrite map.get_empty in H. discriminate. Qed.

  Lemma not_in_range_empty{K V: Type}{M: map.map K V}{ok: map.ok M}: forall (l: list V),
      map.not_in_range map.empty l.
  Proof.
    unfold not_in_range. induction l; intros; constructor; intros;
    rewrite ?map.get_empty; [congruence|auto].
  Qed.

  Lemma not_in_range_put{K V: Type}{M: map.map K V}{ok: map.ok M}
        {key_eqb: K -> K -> bool}{key_eq_dec: EqDecider key_eqb}:
    forall (m: M)(l: list V)(x: K)(y: V),
      ~ In y l ->
      not_in_range m l ->
      not_in_range (map.put m x y) l.
  Proof.
    intros. unfold not_in_range in *. apply Forall_forall. intros.
    eapply Forall_forall in H0. 2: eassumption.
    rewrite map.get_put_dec.
    destruct_one_match.
    - subst. intro C. simp. contradiction.
    - eapply H0.
  Qed.

  Definition map_all_values_V0{K V1 V2: Type}{M1: map.map K V1}{M2: map.map K V2}
             (f: V1 -> option V2)(m1: M1)(keys: list K): option M2 :=
    bind_opt values2 <- List.option_all
                           (List.map (fun k => bind_opt v1 <- map.get m1 k; f v1) keys);
    map.of_list_zip keys values2.

  Definition map_all_values{K V1 V2: Type}{M1: map.map K V1}{M2: map.map K V2}
             (f: V1 -> option V2)(m1: M1): list K -> option M2 :=
    fix rec keys :=
      match keys with
      | nil => Some map.empty
      | k :: ks =>
        match map.get m1 k with
        | Some v1 => match f v1 with
                     | Some v2 => match rec ks with
                                  | Some res => Some (map.put res k v2)
                                  | None => None
                                  end
                     | None => None
                     end
        | None => None
        end
      end.

  Lemma get_map_all_values{K V1 V2: Type}{M1: map.map K V1}{M2: map.map K V2}
        (keqb: K -> K -> bool) {keqb_spec: EqDecider keqb}
        {OK1: map.ok M1} {OK2: map.ok M2} (f: V1 -> option V2):
    forall (keys: list K) (m1: M1) (m2: M2) (k: K) (v1: V1),
      map_all_values f m1 keys = Some m2 ->
      In k keys ->
      map.get m1 k = Some v1 ->
      exists v2, f v1 = Some v2 /\ map.get m2 k = Some v2.
  Proof.
    induction keys; intros.
    - simpl in *. contradiction.
    - simpl in *.
      destruct H0.
      + subst. rewrite H1 in H. simp.
        rewrite map.get_put_same. eauto.
      + simp.
        rewrite map.get_put_dec.
        * destr (keqb a k).
          { (* Automation? clear keqb keqb_spec OK1 OK2 IHkeys. firstorder congruence. (* <- fails *) *)
            subst. eexists. split; [|reflexivity]. congruence. }
          { eauto. }
  Qed.

End map.

Section RegAlloc.

  Context {srcvar: Type}.
  Context (srcvar_eqb: srcvar -> srcvar -> bool).
  Context {impvar: Type}.
  Context (impvar_eqb: impvar -> impvar -> bool).
  Context {func: Type}.
  Context (func_eqb: func -> func -> bool).
  Context {act: Type}.
  Context (act_eqb: act -> act -> bool).

  Context {srcvar_eq_dec : EqDecider srcvar_eqb}.
  Context {impvar_eq_dec : EqDecider impvar_eqb}.

  Context {src2imp: map.map srcvar impvar}.
  Context {src2impOk: map.ok src2imp}.

  Instance srcparams: Syntax.parameters := {|
    Syntax.varname := srcvar;
    Syntax.funname := func;
    Syntax.actname := act;
  |}.

  Instance impparams: Syntax.parameters := {|
    Syntax.varname := impvar;
    Syntax.funname := func;
    Syntax.actname := act;
  |}.

  Local Notation stmt  := (@FlatImp.stmt srcparams). (* input type *)
  Local Notation stmt' := (@FlatImp.stmt impparams). (* output type *)

  Variable available_impvars: list impvar.

  Definition rename_assignment_lhs(m: src2imp)(x: srcvar)(a: list impvar):
    option (src2imp * impvar * list impvar) :=
    match map.get m x with
    | Some y => Some (m, y, a)
    | None   => match a with
                | y :: rest => Some (map.put m x y, y, rest)
                | nil => None
                end
    end.

  Definition rename_assignment_rhs(m: src2imp)(s: stmt)(y: impvar): option stmt' :=
    match s with
    | SLoad sz x a => bind_opt a' <- map.get m a; Some (SLoad sz y a')
    | SLit x v => Some (SLit y v)
    | SOp x op a b => bind_opt a' <- map.get m a; bind_opt b' <- map.get m b;
                      Some (SOp y op a' b')
    | SSet x a => bind_opt a' <- map.get m a; Some (SSet y a')
    | _ => None
    end.

  Fixpoint rename_binds(m: src2imp)(binds: list srcvar)(a: list impvar):
    option (src2imp * list impvar * list impvar) :=
    match binds with
    | nil => Some (m, nil, a)
    | x :: binds =>
      bind_opt (m, y, a) <- rename_assignment_lhs m x a;
      bind_opt (m, res, a) <- rename_binds m binds a;
      Some (m, y :: res, a)
    end.

  Definition rename_cond(m: src2imp)(cond: @bcond srcparams): option (@bcond impparams) :=
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
           (a: list impvar)          (* available registers, shrinking *)
           {struct s}
    : option (src2imp * stmt' * list impvar) :=
    match s with
    | SLoad _ x _ | SLit x _ | SOp x _ _ _ | SSet x _ =>
      bind_opt (m', y, a) <- rename_assignment_lhs m x a;
      bind_opt s' <- rename_assignment_rhs m s y;
      Some (m', s', a)
    | SStore sz x y =>
      bind_opt x' <- map.get m x;
      bind_opt y' <- map.get m y;
      Some (m, SStore sz x' y', a)
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

  Definition rename_stmt(m: src2imp)(s: stmt)(av: list impvar): option stmt' :=
    bind_opt (_, s', _) <- rename m s av; Some s'.

  Definition rename_fun(F: list srcvar * list srcvar * stmt):
    option (list impvar * list impvar * stmt') :=
    let '(argnames, retnames, body) := F in
    bind_opt (m, argnames', av) <- rename_binds map.empty argnames available_impvars;
    bind_opt (m, retnames', av) <- rename_binds m retnames av;
    bind_opt (_, body', _) <- rename m body av;
    Some (argnames', retnames', body').

  Context {W: Utility.Words} {mem: map.map word byte}.
  Context {srcLocals: map.map srcvar word}.
  Context {impLocals: map.map impvar word}.
  Context {srcLocalsOk: map.ok srcLocals}.
  Context {impLocalsOk: map.ok impLocals}.
  Context {funname_env: forall T: Type, map.map func T}.
  Context (ext_spec:  list (mem * actname * list word * (mem * list word)) ->
                      mem -> actname -> list word -> (mem -> list word -> Prop) -> Prop).

  Instance srcSemanticsParams: Semantics.parameters. refine ({|
    Semantics.syntax := srcparams;
    Semantics.varname_eqb := srcvar_eqb;
    Semantics.funname_eqb := func_eqb;
    Semantics.actname_eqb := act_eqb;
    Semantics.locals := srcLocals;
    Semantics.ext_spec := ext_spec;
  |}).
  Defined.

  Instance impSemanticsParams: Semantics.parameters. refine ({|
    Semantics.syntax := impparams;
    Semantics.varname_eqb := impvar_eqb;
    Semantics.funname_eqb := func_eqb;
    Semantics.actname_eqb := act_eqb;
    Semantics.locals := impLocals;
    Semantics.ext_spec := ext_spec;
  |}).
  Defined.

  Definition rename_functions(e: @FlatImp.env srcSemanticsParams)(funs: list funname):
    option (@FlatImp.env impSemanticsParams) := map.map_all_values rename_fun e funs.

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
      + subst. specialize H with (1 := H1l) (2 := H0). congruence.
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
      specialize IHsrcnames with (1 := H) (2 := E0) (lL := (map.put lL i r0)).
      edestruct IHsrcnames; eauto using states_compat_put_raw.
  Qed.

  Definition envs_related(e1: @env srcSemanticsParams)
                         (e2: @env impSemanticsParams): Prop :=
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
    destruct_one_match_hyp; try congruence.
    simp.
    apply map.get_put_same.
  Qed.

  Lemma states_compat_put: forall lH lL r x av r' y av' v,
      map.injective r ->
      map.not_in_range r av ->
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
        specialize H with (1 := E) (2 := H2l). congruence.
    - rewrite map.get_put_dec in H3.
      setoid_rewrite map.get_put_dec.
      unfold map.not_in_range in *. simp.
      destruct_one_match; subst; simp.
      + eexists. split; [reflexivity|].
        destruct_one_match; subst; simp; congruence.
      + specialize H2 with (1 := H3). simp.
        eexists. split; [eassumption|].
        destruct_one_match; try congruence.
  Qed.

  Lemma states_compat_put': forall lH lL r x av r' y av' v,
      map.injective r ->
      map.not_in_range r av ->
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
      unfold map.not_in_range in *. simp.
      do 2 destruct_one_match; subst; try congruence. eauto.
  Qed.

  Ltac srew_sidec := first [rewrite map.get_put_same; reflexivity | eauto].
  Ltac srew_h := simpl_rewrite_in_hyps ltac:(fun _ => srew_sidec).
  Ltac srew_g := simpl_rewrite_in_goal ltac:(fun _ => srew_sidec).

  Lemma eval_bcond_compat: forall (lH : srcLocals) r (lL: impLocals) condH condL b,
      rename_cond r condH = Some condL ->
      states_compat lH r lL ->
      @eval_bcond srcSemanticsParams lH condH = Some b ->
      @eval_bcond impSemanticsParams lL condL = Some b.
  Proof.
    intros.
    unfold rename_cond, eval_bcond in *.
    destruct_one_match_hyp; simp;
      repeat match goal with
             | C: states_compat _ _ _, D: _ |- _ => unique pose proof (C _ _ D)
             end;
      simp;
      simpl in *; (* PARAMRECORDS *)
      srew_h; simp; srew_g; reflexivity.
  Qed.

  Lemma eval_bcond_compat_None: forall (lH : srcLocals) r (lL: impLocals) condH condL,
      rename_cond r condH = Some condL ->
      states_compat lH r lL ->
      @eval_bcond srcSemanticsParams lH condH <> None ->
      @eval_bcond impSemanticsParams lL condL <> None.
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
      @eval_bcond srcSemanticsParams lH condH = Some b ->
      @eval_bcond impSemanticsParams lL condL = Some b.
  Proof.
    intros.
    unfold rename_cond, eval_bcond in *.
    destruct_one_match_hyp; simp;
      repeat match goal with
             | C: states_compat' _ _ _, D: _ |- _ => unique pose proof (C _ _ D)
             end;
      simpl in *; (* PARAMRECORDS *)
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
      map.not_in_range r1 av1 ->
      NoDup av1 ->
      map.injective r2 /\
      map.extends r2 r1 /\
      (forall r3 av3, map.extends r3 r2 -> rename_assignment_lhs r3 x av3 = Some (r3, y, av3)) /\
      (exists used, av1 = used ++ av2 /\ map.not_in_range r2 av2) /\
      map.get r2 x = Some y.
  Proof.
    pose proof (map.not_in_range_put (ok := src2impOk)).
    intros.
    unfold rename_assignment_lhs, map.extends, map.not_in_range in *; intros; simp.
    destruct_one_match_hyp; simp;
      (split; [ (try eapply map.injective_put); eassumption
              | split;
                [ intros; rewrite ?map.get_put_diff by congruence
                | split; [ intros; rewrite ?map.get_put_same; srew_g
                         | split; [ first [ refine (ex_intro _ nil (conj eq_refl _))
                                          | refine (ex_intro _ [_] (conj eq_refl _)) ]
                                  | rewrite ?map.get_put_same; eauto ]]];
                eauto ]).
  Qed.

  (* a list of useful properties of rename_binds, all proved in one induction *)
  Lemma rename_binds_props: forall {bH r1 r2 bL av1 av2},
      rename_binds r1 bH av1 = Some (r2, bL, av2) ->
      map.injective r1 ->
      map.not_in_range r1 av1 ->
      NoDup av1 ->
      map.injective r2 /\
      map.extends r2 r1 /\
      (forall r3 av3, map.extends r3 r2 -> rename_binds r3 bH av3 = Some (r3, bL, av3)) /\
      (exists used, av1 = used ++ av2 /\ map.not_in_range r2 av2) /\
      map.getmany_of_list r2 bH = Some bL.
  Proof.
    induction bH; intros; simpl in *; simp.
    - split; [assumption|].
      split; [apply extends_refl|].
      split; [intros; reflexivity|].
      split; [|reflexivity].
      exists nil.
      split; [reflexivity|].
      assumption.
    - specialize IHbH with (1 := E0).
      destruct (rename_assignment_lhs_props E); try assumption. simp.
      apply_in_hyps @invert_NoDup_app. simp.
      edestruct IHbH; eauto. simp.
      split; [assumption|].
      unfold map.extends in *.
      split; [|split;[|split]].
      + intros. eapply extends_trans; eassumption.
      + intros. srew_g. reflexivity.
      + refine (ex_intro _ (_ ++ _) (conj _ _)).
        2: eassumption. rewrite <- List.app_assoc. reflexivity.
      + unfold map.getmany_of_list in *. simpl. srew_g. reflexivity.
  Qed.

  Lemma rename_cond_props: forall {r1 cond cond'},
      rename_cond r1 cond = Some cond' ->
      (forall r3, map.extends r3 r1 -> rename_cond r3 cond = Some cond').
  Proof.
    unfold rename_cond, map.extends. intros.
    destruct_one_match; simp; repeat erewrite H0 by eassumption; reflexivity.
  Qed.

  (* a list of useful properties of rename, all proved in one induction *)
  Lemma rename_props: forall {sH r1 r2 sL av1 av2},
      rename r1 sH av1 = Some (r2, sL, av2) ->
      map.injective r1 ->
      map.not_in_range r1 av1 ->
      NoDup av1 ->
      map.injective r2 /\
      map.extends r2 r1 /\
      (forall r3 av3, map.extends r3 r2 -> rename r3 sH av3 = Some (r3, sL, av3)) /\
      (exists used, av1 = used ++ av2 /\ map.not_in_range r2 av2).
  Proof.
    induction sH; simpl in *; intros; simp;
      apply_in_hyps @rename_assignment_lhs_props; simp;
        try (repeat match goal with
                    | |- _ /\ _ => split
                    end;
             eauto;
             []);
        try solve [intros; unfold map.extends in *; srew_g; reflexivity].

    - (* SStore remainder *)
      unfold map.extends;
            (split; [ (try eapply map.injective_put); eassumption
                    | split;
                      [ idtac
                      | split;
                        [ intros; rewrite ?map.get_put_diff by congruence
                        |  first [ refine (ex_intro _ nil (conj eq_refl _))
                                 | refine (ex_intro _ [_] (conj eq_refl _)) ]]];
                      eauto]).
      srew_g. reflexivity.
    - (* SIf *)
      specialize IHsH1 with (1 := E). auto_specialize. simp.
      apply_in_hyps @invert_NoDup_app.
      apply_in_hyps @invert_Forall_app.
      simp.
      specialize IHsH2 with (1 := E0). auto_specialize. simp.
      split; [assumption|].
      pose proof (rename_cond_props E1).
      unfold map.extends in *.
      split; [eauto|].
      split; [intros; srew_g; reflexivity|].
      refine (ex_intro _ (_ ++ _) (conj _ _)). 2: assumption.
      rewrite <- List.app_assoc. reflexivity.
    - (* SLoop *)
      specialize IHsH1 with (1 := E). auto_specialize. simp.
      apply_in_hyps @invert_NoDup_app.
      apply_in_hyps @invert_Forall_app.
      simp.
      specialize IHsH2 with (1 := E1). auto_specialize. simp.
      split; [assumption|].
      unfold map.extends in *.
      split; [eauto|].
      pose proof (rename_cond_props E0).
      unfold map.extends in *.
      split; [intros; srew_g; reflexivity|].
      refine (ex_intro _ (_ ++ _) (conj _ _)). 2: assumption.
      rewrite <- List.app_assoc. reflexivity.
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
      refine (ex_intro _ (_ ++ _) (conj _ _)). 2: assumption.
      rewrite <- List.app_assoc. reflexivity.
    - (* SSkip *)
      repeat split; unfold map.extends in *; eauto.
      exists nil. simpl. auto.
    - (* SCall *)
      apply_in_hyps @rename_binds_props. simp; repeat split; eauto.
      intros. pose proof @map.getmany_of_list_extends. srew_g. reflexivity.
    - (* SInteract *)
      apply_in_hyps @rename_binds_props. simp; repeat split; eauto.
      intros. pose proof @map.getmany_of_list_extends. srew_g. reflexivity.
  Qed.

  Lemma states_compat_putmany_of_list: forall srcvars lH lH' lL r impvars av r' av' values,
      map.injective r ->
      map.not_in_range r av ->
      NoDup av ->
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
      4: eassumption.
      5: eassumption.
      all: try eassumption.
      1: {
        eapply states_compat_put.
        3: eassumption.
        all: eassumption.
      }
      simp. simpl. eauto.
  Qed.

  Lemma rename_correct(available_impvars_NoDup: NoDup available_impvars): forall eH eL,
      envs_related eH eL ->
      forall sH t m lH mc post,
      @exec srcSemanticsParams eH sH t m lH mc post ->
      forall lL r r' av av' sL,
      map.injective r ->
      map.not_in_range r av ->
      NoDup av ->
      rename r sH av = Some (r', sL, av') ->
      states_compat lH r lL ->
      @exec impSemanticsParams eL sL t m lL mc (fun t' m' lL' mc' =>
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
            simpl in *; (* PARAMRECORDS *)
            eauto;
            congruence].

    - (* @exec.interact *)
      apply_in_hyps @rename_binds_props. simp.
      rename l into lH.
      eapply @exec.interact; try eassumption.
      + eapply getmany_of_list_states_compat; eassumption.
      + intros. specialize (H3 _ _ H7). simp.
        pose proof putmany_of_list_states_compat as P.
        specialize P with (1 := E0_uacl).
        pose proof states_compat_extends as Q.
        specialize Q with (1 := E0_uacrl) (2 := H8).
        specialize P with (3 := Q); clear Q.
        specialize P with (1 := H3l).
        specialize P with (1 := E0_uacrrrr).
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
        [|eapply map.empty_injective|eapply map.not_in_range_empty|eapply available_impvars_NoDup].
      simp.
      apply_in_hyps @invert_NoDup_app. simp.
      pose proof E2 as E2'.
      apply @rename_binds_props in E2; [|assumption..].
      simp.
      apply_in_hyps @invert_NoDup_app. simp.
      apply_in_hyps @rename_props. simp.
      edestruct putmany_of_list_states_compat as [ lLF' [? ?] ].
      2: exact H2.
      1: exact E2l.
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
        specialize H4 with (1 := H11r). move H4 at bottom. simp.
        edestruct states_compat_putmany_of_list as [ lL' [? ?] ].
        5: exact H9.
        5: eassumption.
        1: assumption.
        3: exact E0.
        1: assumption.
        1: assumption.
        do 2 eexists. split; [|split].
        * eapply getmany_of_list_states_compat.
          3: eassumption.
          1: eassumption.
          eapply map.getmany_of_list_extends; eassumption.
        * eassumption.
        * eauto.
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
        eapply IHexec. 4: eassumption. all: try eassumption.
        eapply states_compat_extends; cycle 1; try eassumption.
    - (* @exec.loop *)
      destruct (rename_props E); try assumption. simp.
      apply_in_hyps @invert_NoDup_app. simp.
      destruct (rename_props E1); try assumption. simp.
      apply_in_hyps @invert_NoDup_app. simp.
      rename IHexec into IH1.
      rename H4 into IH2.
      rename H6 into IH12.
      specialize IH1 with (4 := E).
      specialize IH2 with (6 := E1).
      move IH1 at bottom.
      specialize (IH1 lL). auto_specialize.
      assert (rename r' (SLoop body1 cond body2) av' = Some (r', (SLoop s b s0), av')) as R. {
        simpl.
        rewrite H12rl by assumption.
        rewrite (rename_cond_props E0) by eassumption.
        rewrite H13rl by apply extends_refl.
        reflexivity.
      }
      simpl in R.
      specialize IH12 with (5 := R). clear R.
      move IH1 at bottom.
      eapply @exec.loop.
      + eapply IH1.
      + cbv beta. intros. simp.
        eauto using eval_bcond_compat_None.
      + cbv beta. intros. simp.
        eexists. split.
        * eapply states_compat_extends; cycle 1; eassumption.
        * move H1 at bottom.
          specialize H1 with (1 := H4r).
          match type of H1 with
          | ?E <> None => destruct E eqn: A; [|contradiction]
          end.
          clear H1.
          pose proof @eval_bcond_compat as P.
          specialize P with (1 := E0) (2 := H4l) (3 := A).
          erewrite P in H6.
          simp. eapply H2; try eassumption.
      + cbv beta. intros. simp.
        eapply IH2; try eassumption.
        pose proof @eval_bcond_compat as P.
        specialize H1 with (1 := H4r).
        match type of H1 with
        | ?E <> None => destruct E eqn: A; [|contradiction]
        end.
        clear H1.
        specialize P with (1 := E0) (2 := H4l) (3 := A).
        erewrite P in H6.
        simp. reflexivity.
      + cbv beta. intros. simp.
        eapply IH12; try eassumption.
    - (* @exec.seq *)
      destruct (rename_props E); try assumption. simp.
      apply_in_hyps @invert_NoDup_app. simp.
      destruct (rename_props E0); try assumption. simp.
      rename IHexec into IH1, H2 into IH2.
      specialize IH1 with (4 := E).
      specialize IH2 with (5 := E0).
      eapply @exec.seq.
      + eapply IH1; eassumption.
      + cbv beta. intros. simp.
        eapply IH2; try eassumption.
  Qed.

  Definition related(done: bool): @FlatImp.SimState srcSemanticsParams ->
                                  @FlatImp.SimState impSemanticsParams -> Prop :=
    fun '(e1, c1, t1, m1, l1, mc1) '(e2, c2, t2, m2, l2, mc2) =>
      envs_related e1 e2 /\
      t1 = t2 /\
      m1 = m2 /\
      (done = false -> l1 = map.empty /\ l2 = map.empty /\ mc1 = mc2) /\
      exists av' r', rename map.empty c1 available_impvars = Some (r', c2, av').
      (* TODO could/should also relate l1 and l2 *)

  Lemma renameSim(available_impvars_NoDup: NoDup available_impvars):
    simulation (@FlatImp.SimExec srcSemanticsParams)
               (@FlatImp.SimExec impSemanticsParams) related.
  Proof.
    unfold simulation.
    intros *. intros R Ex1.
    unfold FlatImp.SimExec, related in *.
    destruct s1 as (((((e1 & c1) & t1) & m1) & l1) & mc1).
    destruct s2 as (((((e2 & c2) & t2) & m2) & l2) & mc2).
    simp.
    pose proof Rrrrr as A.
    apply @rename_props in A;
      [|eapply map.empty_injective|eapply map.not_in_range_empty|eapply available_impvars_NoDup].
    specialize (Rrrrl eq_refl).
    simp.
    apply_in_hyps @invert_NoDup_app. simp.
    eapply exec.weaken.
    - eapply rename_correct.
      1: subst; eassumption.
      1: eassumption.
      1: eassumption.
      4: {
        eapply Arrl. eapply extends_refl.
      }
      1: eassumption.
      1: eassumption.
      1: eassumption.
      unfold states_compat. intros *. intro A.
      erewrite map.get_empty in A. discriminate.
    - simpl. intros. simp.
      eexists; split; [|eassumption].
      simpl.
      repeat split; try discriminate; eauto.
  Qed.

End RegAlloc.

(* Print Assumptions renameSim. *)
