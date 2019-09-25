Require Import Coq.ZArith.ZArith.
Require Import compiler.FlatImp.
Require Import coqutil.Decidable.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Utility.Utility.
Require Import coqutil.Macros.unique.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Properties.
Require Import coqutil.Map.Solver.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.TestLemmas.
Require Import bedrock2.Syntax.
Require Import compiler.util.ListLib.
Require Import compiler.Simp.
Require Import compiler.Simulation.


Local Notation "'bind_opt' x <- a ; f" :=
  (match a with
   | Some x => f
   | None => None
   end)
  (right associativity, at level 70, x pattern).

Axiom TODO_sam: False.

Module map.
  Definition putmany_of_pairs{K V: Type}{M: map.map K V}(m: M): list (K * V) -> M :=
    fix rec l :=
    match l with
    | nil => m
    | (k, v) :: rest => map.put (rec rest) k v
    end.

  Definition injective{K V: Type}{M: map.map K V}(m: M): Prop :=
    forall k1 k2 v,
      map.get m k1 = v -> map.get m k2 = v -> k1 = k2.

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

  Lemma putmany_of_pairs_extends{K V: Type}{M: map.map K V}{ok: map.ok M}
        {key_eqb: K -> K -> bool}{key_eq_dec: EqDecider key_eqb}:
    forall (pairs: list (K * V)) (m1 m2: M),
    map.extends m1 m2 ->
    map.extends (putmany_of_pairs m1 pairs) (putmany_of_pairs m2 pairs).
  Proof.
    induction pairs; intros.
    - simpl. assumption.
    - simpl. destruct a as [k v]. apply map.put_extends. eapply IHpairs. assumption.
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
    option (src2imp * list (srcvar * impvar) * list impvar) :=
    match binds with
    | nil => Some (m, nil, a)
    | x :: binds =>
      bind_opt (m, y, a) <- rename_assignment_lhs m x a;
      bind_opt (m, res, a) <- rename_binds m binds a;
      Some (m, (x, y) :: res, a)
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
      bind_opt (m, tuples, a) <- rename_binds m binds a;
      bind_opt args' <- map.getmany_of_list m args;
      Some (map.putmany_of_pairs m tuples, SCall (List.map snd tuples) f args', a)
    | SInteract binds f args =>
      bind_opt (m, tuples, a) <- rename_binds m binds a;
      bind_opt args' <- map.getmany_of_list m args;
      Some (map.putmany_of_pairs m tuples, SInteract (List.map snd tuples) f args', a)
    | SSkip => Some (m, SSkip, a)
    end.

  Definition rename_stmt(m: src2imp)(s: stmt)(av: list impvar): stmt' :=
    match rename m s av with
    | Some (_, s', _) => s'
    | None => SSkip
    end.

  Definition rename_fun(F: list srcvar * list srcvar * stmt):
    option (list impvar * list impvar * stmt') :=
    let '(argnames, retnames, body) := F in
    bind_opt (m, argtuples, av) <- rename_binds map.empty argnames available_impvars;
    bind_opt (m, rettuples, av) <- rename_binds m retnames av;
    bind_opt (_, body', _) <- rename m body av;
    Some (List.map snd argtuples, List.map snd rettuples, body').

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

  Definition rename_function(e: @FlatImp.env srcSemanticsParams)(f: funname):
    (list impvar * list impvar * stmt') :=
    match map.get e f with
    | Some F => match rename_fun F with
                | Some res => res
                | None => (nil, nil, FlatImp.SSkip)
                end
    | None => (nil, nil, FlatImp.SSkip)
    end.

  Definition rename_functions(e: @FlatImp.env srcSemanticsParams):
    list funname -> @FlatImp.env impSemanticsParams :=
    fix rec funs :=
      match funs with
      | f :: rest => map.put (rec rest) f (rename_function e f)
      | nil => map.empty
      end.

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

  Ltac head e :=
    match e with
    | ?a _ => head a
    | _ => e
    end.

  Definition envs_related(e1: @env srcSemanticsParams)
                         (e2: @env impSemanticsParams): Prop :=
    forall f impl1,
      map.get e1 f = Some impl1 ->
      exists impl2,
        rename_fun impl1 = Some impl2.

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
      simpl in *. (* PARAMRECORDS *)
    - (* TODO such simplification patterns should be automated *)
      rewrite E2 in Hl. rewrite E1 in H1l. simp.
      rewrite H1r. rewrite Hr.
      reflexivity.
    - rewrite E0 in Hl. simp.
      rewrite Hr.
      reflexivity.
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
      simpl in *. (* PARAMRECORDS *)
    - rewrite <- H1. rewrite E. (* <-- TODO such simplification patterns should be automated *)
      rewrite <- H. rewrite E0.
      reflexivity.
    - rewrite <- H. rewrite E.
      reflexivity.
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

  Ltac auto_specialize :=
    repeat match goal with
           | H: ?P -> _, H': _ |- _ => match type of P with
                                       | Prop => specialize (H H')
                                       end
           end.

  Ltac apply_in_hyps t :=
    repeat match goal with
           | H: _ |- _ => apply t in H
           end.

  (* a list of useful properties of rename, all proved in one induction *)
  Lemma rename_props: forall sH r1 r2 sL av1 av2,
      map.injective r1 ->
      map.not_in_range r1 av1 ->
      NoDup av1 ->
      rename r1 sH av1 = Some (r2, sL, av2) ->
      map.injective r2 /\
      map.extends r2 r1 /\
      exists used, av1 = used ++ av2 /\ map.not_in_range r2 av2.
  Proof.
    pose proof (map.not_in_range_put (ok := src2impOk)).
    induction sH; simpl in *;
      unfold rename_assignment_lhs, map.extends, map.not_in_range in *; intros; simp;
        try solve [
              try (destruct_one_match_hyp; simp);
              (split; [ (try eapply map.injective_put); eassumption
                      | split;
                        [ intros; rewrite ?map.get_put_diff by congruence
                        |  first [ refine (ex_intro _ nil (conj eq_refl _))
                                 | refine (ex_intro _ [_] (conj eq_refl _)) ]];
                        eauto ])].

    - (* SIf *)
      specialize IHsH1 with (4 := E). auto_specialize. simp.
      apply_in_hyps @invert_NoDup_app.
      apply_in_hyps @invert_Forall_app.
      simp.
      specialize IHsH2 with (4 := E0). auto_specialize. simp.
      split; [assumption|].
      split; [eauto|].
      refine (ex_intro _ (_ ++ _) (conj _ _)). 2: assumption.
      rewrite <- List.app_assoc. reflexivity.
    - (* SLoop *)
      case TODO_sam.
    - (* SSeq *)
      case TODO_sam.
    - (* SCall *)
      case TODO_sam.
    - (* SInteract *)
      case TODO_sam.
  Qed.

  Lemma rename_extends_and_shrinks: forall sH r1 r2 sL av1 av2,
      map.not_in_range r1 av1 ->
      NoDup av1 ->
      rename r1 sH av1 = Some (r2, sL, av2) ->
      map.extends r2 r1 /\ exists used, av1 = used ++ av2 /\ map.not_in_range r2 av2.
  Proof.
    pose proof (map.not_in_range_put (ok := src2impOk)).
    induction sH; simpl in *;
      unfold rename_assignment_lhs, map.extends, map.not_in_range in *; intros; simp;
        try solve [
              try (destruct_one_match_hyp; simp);
              (split;
               [ intros; rewrite ?map.get_put_diff by congruence
               |  first [ refine (ex_intro _ nil (conj eq_refl _))
                        | refine (ex_intro _ [_] (conj eq_refl _)) ]];
               eauto)].

    - (* SIf *)
      specialize IHsH1 with (3 := E). specialize IHsH1 with (1 := H0) (2 := H1). simp.
      apply invert_NoDup_app in H1.
      apply invert_Forall_app in H0. simp.
      specialize IHsH2 with (3 := E0).
      destruct IHsH2; simp; try assumption.
      split; eauto.
      refine (ex_intro _ (_ ++ _) (conj _ _)). 2: assumption.
      rewrite <- List.app_assoc. reflexivity.
    - (* SLoop *)
      case TODO_sam.
    - (* SSeq *)
      case TODO_sam.
    - (* SCall *)
      case TODO_sam.
    - (* SInteract *)
      case TODO_sam.
  Qed.

  Lemma checker_correct: forall eH eL,
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
    (*
    intros.
    destruct H0 eqn: E;
    match type of E with
    | _ = ?r => let h := head r in idtac "- (*" h "*)"
    end.
    *)
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
      case TODO_sam.
    - (* @exec.call *)
      case TODO_sam.
    - (* @exec.if_true *)
      eapply @exec.if_true.
      + eauto using eval_bcond_compat.
      + eapply exec.weaken.
        * eapply IHexec; eauto.
        * cbv beta. intros. simp. eexists; split; eauto.
          edestruct rename_extends_and_shrinks. 3: exact E. all: try assumption. simp.
          apply invert_NoDup_app in H4. simp.
          edestruct rename_extends_and_shrinks. 3: exact E0. all: try assumption. simp.
          eapply states_compat_extends; cycle 1; eassumption.
    - (* @exec.if_false *)
      eapply @exec.if_false.
      + eauto using eval_bcond_compat.
      + edestruct rename_extends_and_shrinks. 3: exact E. all: try assumption. simp.
        apply invert_NoDup_app in H4. simp.
        edestruct rename_extends_and_shrinks. 3: exact E0. all: try assumption. simp.
        eapply IHexec. 4: eassumption. all: try eassumption.
        all: case TODO_sam.
    - (* @exec.loop *)
      case TODO_sam.
    - (* @exec.seq *)
      rename IHexec into IH1, H2 into IH2.
      econstructor.
      1: eapply IH1; eassumption.
      cbv beta.
      intros. simp.
      eapply IH2; try eassumption.
      all: case TODO_sam.
  all: fail.
  Admitted.

(*

  Lemma states_compat_put: forall lH lL v x y r,
      map.get r x = None ->
      states_compat lH r lL ->
      states_compat (map.put lH x v) (map.put r x y) (map.put lL y v).
  Proof.
    unfold states_compat.
    intros.
    rewrite (map.get_put_dec (key_eqb := impvar_eqb)).
    lazymatch goal with
    | H: map.get (map.put _ _ _) _ = _ |- _ => rewrite map.get_put_dec in H
    end.
    lazymatch goal with
    | H: gett (putt _ _ _) _ = _ |- _ => rewrite gett_putt_dec in H
    end.
    destruct_one_match_hyp.
    - subst x0. replace y0 with y by congruence. replace w with v by congruence.
      destruct_one_match; congruence.
    - specialize H0 with (1 := H1) (2 := H2).
*)

  Lemma putmany_of_list_states_compat: forall binds resvals lL lH lH' r,
      map.putmany_of_list (map fst binds) resvals lH = Some lH' ->
      states_compat lH r lL ->
      exists lL',
        map.putmany_of_list (map snd binds) resvals lL = Some lL' /\
        states_compat lH' (map.putmany_of_pairs r binds) lL'.
  Proof.
    induction binds; intros.
    - simpl in H. simp. simpl. eauto.
    - simpl in *. simp.
      specialize IHbinds with (1 := H).
      destruct a as [sv iv].
      apply map.putmany_of_list_sameLength in H.
      rewrite map_length in H. rewrite <- (map_length snd) in H.
      eapply map.sameLength_putmany_of_list in H.
      destruct H as (lL' & H).
      exists lL'. split; [exact H|].
  Abort.

End RegAlloc.
