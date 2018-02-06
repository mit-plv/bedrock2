Require Import lib.LibTacticsMin.
Require Import compiler.Common.
Require Import compiler.ResMonad.
Require compiler.ExprImp.
Require compiler.FlatImp.
Require Import compiler.StateCalculus.
Require Import compiler.NameGen.
Require Import bbv.DepEqNat.
Require Import riscv.NameWithEq.

Section FlattenExpr.

  Context {w: nat}. (* bit width *)

  Context {Name: NameWithEq}.
  Notation var := (@name Name).
  Existing Instance eq_name_dec.

  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.
  Context {vars: Type}.
  Context {varset: set vars var}.
  Context {NGstate: Type}.
  Context {NG: NameGen var vars NGstate}.

  Ltac state_calc := state_calc_generic (@name Name) (word w).
  Ltac set_solver := set_solver_generic (@name Name).

  (* returns and var into which result is saved, and new fresh name generator state
     TODO use state monad? *)
  Fixpoint flattenExpr(ngs: NGstate)(e: ExprImp.expr (w := w)):
    (FlatImp.stmt (w := w) * var * NGstate) :=
    match e with
    | ExprImp.ELit n =>
        let '(x, ngs') := genFresh ngs in
        (FlatImp.SLit x n, x, ngs')
    | ExprImp.EVar x =>
        (* (FlatImp.SSkip, x, ngs)  would be simpler but doesn't satisfy the invariant that
           the returned var is in modVars of the returned statement *)
        let '(y, ngs') := genFresh ngs in
        (FlatImp.SSet y x, y, ngs')
    | ExprImp.EOp op e1 e2 =>
        let '(s1, r1, ngs') := flattenExpr ngs e1 in
        let '(s2, r2, ngs'') := flattenExpr ngs' e2 in
        let '(x, ngs''') := genFresh ngs'' in
        (FlatImp.SSeq s1 (FlatImp.SSeq s2 (FlatImp.SOp x op r1 r2)), x, ngs''')
    end.

  (* returns statement and new fresh name generator state *)
  Fixpoint flattenStmt(ngs: NGstate)(s: ExprImp.stmt (w := w)): (FlatImp.stmt (w := w) * NGstate) :=
    match s with
    | ExprImp.SSet x e =>
        let '(e', r, ngs') := flattenExpr ngs e in
        (FlatImp.SSeq e' (FlatImp.SSet x r), ngs')
    | ExprImp.SIf cond sThen sElse =>
        let '(cond', r, ngs') := flattenExpr ngs cond in
        let '(sThen', ngs'') := flattenStmt ngs' sThen in
        let '(sElse', ngs''') := flattenStmt ngs'' sElse in
        (FlatImp.SSeq cond' (FlatImp.SIf r sThen' sElse'), ngs''')
    | ExprImp.SWhile cond body =>
        let '(cond', r, ngs') := flattenExpr ngs cond in
        let '(body', ngs'') := flattenStmt ngs' body in
        (FlatImp.SLoop cond' r body', ngs'')
    | ExprImp.SSeq s1 s2 =>
        let '(s1', ngs') := flattenStmt ngs s1 in
        let '(s2', ngs'') := flattenStmt ngs' s2 in
        (FlatImp.SSeq s1' s2', ngs'')
    | ExprImp.SSkip => (FlatImp.SSkip, ngs)
    end.

  Lemma flattenExpr_size: forall e s resVar ngs ngs',
    flattenExpr ngs e = (s, resVar, ngs') ->
    FlatImp.stmt_size s <= 4 * ExprImp.expr_size e.
  Proof.
    induction e; intros; simpl in *; repeat destruct_one_match_hyp; inversionss; simpl; try omega.
    specializes IHe1; [eassumption|].
    specializes IHe2; [eassumption|].
    omega.
  Qed.

  Lemma flattenStmt_size: forall s s' ngs ngs',
    flattenStmt ngs s = (s', ngs') ->
    FlatImp.stmt_size s' <= 4 * ExprImp.stmt_size s.
  Proof.
    induction s; intros; simpl in *; repeat destruct_one_match_hyp; inversionss; simpl;
    repeat match goal with
    | IH: _, A: _ |- _ => specialize IH with (1 := A)
    end;
    repeat match goal with
    | H: _ |- _ => apply flattenExpr_size in H
    end;
    try omega.
  Qed.

  Lemma flattenExpr_freshVarUsage: forall e ngs ngs' s v,
    flattenExpr ngs e = (s, v, ngs') ->
    subset (allFreshVars ngs') (allFreshVars ngs).
  Proof.
    induction e; intros; repeat (inversionss; try destruct_one_match_hyp);
    repeat match goal with
    | H: _ |- _ => apply genFresh_spec in H
    end;
    try (
      specializes IHe1; [ eassumption | ];
      specializes IHe2; [ eassumption | ]
    );
    set_solver.
  Qed.

  Lemma flattenExpr_modifies_resVar: forall e s ngs ngs' resVar,
    flattenExpr ngs e = (s, resVar, ngs') ->
    resVar \in (FlatImp.modVars s).
  Proof.
    intros.
    destruct e; repeat (inversionss; try destruct_one_match_hyp); simpl in *; set_solver.
  Qed.

  Lemma flattenExpr_resVar: forall e s ngs ngs' resVar,
    flattenExpr ngs e = (s, resVar, ngs') ->
    ~ resVar \in (allFreshVars ngs').
  Proof.
    intros. destruct e; repeat (inversionss; try destruct_one_match_hyp); simpl in *;
    repeat match goal with
    | H: _ |- _ => apply genFresh_spec in H
    end;
    set_solver.
  Qed.

  Lemma flattenExpr_modVars_spec: forall e s ngs ngs' resVar,
    flattenExpr ngs e = (s, resVar, ngs') ->
    subset (FlatImp.modVars s) (diff (allFreshVars ngs) (allFreshVars ngs')).
  Proof.
    (* Note: here it can happen that inversionss substitutes w (if we have an equality
       wlit + wdiff = w, and then flattenExpr_freshVarUsage, which depends on w, cannot be
       applied any more. *)
    induction e; intros; repeat (inversionss; try destruct_one_match_hyp);
    simpl;
    try (
      specializes IHe1; [ eassumption | ];
      specializes IHe2; [ eassumption | ]
    );
    repeat match goal with
    | H: _ |- _ => apply genFresh_spec in H
    | H: _ |- _ => apply flattenExpr_freshVarUsage in H
    end;
    set_solver.
  Qed.

  Lemma flattenStmt_freshVarUsage: forall s s' ngs1 ngs2,
    flattenStmt ngs1 s = (s', ngs2) ->
    subset (allFreshVars ngs2) (allFreshVars ngs1).
  Proof.
    induction s; intros; repeat (inversionss; try destruct_one_match_hyp);
    repeat match goal with
    | H: _ |- _ => apply genFresh_spec in H
    | H: _ |- _ => apply flattenExpr_freshVarUsage in H
    end;
    repeat match goal with
    | IH: forall _ _ _, _ = _ -> _ |- _ => specializes IH; [ eassumption | ]
    end;
    set_solver.
  Qed.

  Ltac pose_flatten_var_ineqs :=
    repeat match goal with
    | H: _ |- _ => unique apply flattenExpr_freshVarUsage in copy of H
    | H: _ |- _ => unique apply FlatImp.modVarsSound in copy of H
    | H: _ |- _ => unique apply flattenExpr_modifies_resVar in copy of H
    | H: _ |- _ => unique apply flattenExpr_modVars_spec in copy of H
    | H: _ |- _ => unique apply flattenStmt_freshVarUsage in copy of H
    end.

  Tactic Notation "nofail" tactic3(t) := first [ t | fail 1000 "should not have failed"].

  Ltac fuel_increasing_rewrite :=
    match goal with
    | Ev: FlatImp.eval_stmt ?Fuel1 ?initial ?s = ?final
      |- context [FlatImp.eval_stmt ?Fuel2 ?initial ?s]
      => let IE := fresh in assert (Fuel1 <= Fuel2) as IE by omega;
         apply (FlatImp.increase_fuel_still_Success _ _ _ _ _ IE) in Ev;
         clear IE;
         rewrite Ev
    end.

  (* Note: If you want to get in the conclusion
     "only_differ initialL (vars_range firstFree (S resVar)) finalL"
     this needn't be part of this lemma, because it follows from
     flattenExpr_modVars_spec and FlatImp.modVarsSound *)
  Lemma flattenExpr_correct_aux: forall e ngs1 ngs2 resVar s
    initialH initialL res,
    flattenExpr ngs1 e = (s, resVar, ngs2) ->
    extends initialL initialH ->
    undef initialH (allFreshVars ngs1) ->
    ExprImp.eval_expr initialH e = Some res ->
    exists fuel finalL,
      FlatImp.eval_stmt fuel initialL s = Success finalL /\
      get finalL resVar = Some res.
  Proof.
    induction e; introv F Ex U Ev.
    - repeat (inversionss; try destruct_one_match_hyp).
      match goal with
      | |- context [get _ resVar = Some ?res] =>
         exists 1%nat (put initialL resVar res)
      end.
      split; state_calc.
    - repeat (inversionss; try destruct_one_match_hyp).
      exists 1%nat (put initialL resVar res). repeat split.
      + simpl. unfold extends in Ex. apply Ex in H0. rewrite H0. simpl. reflexivity.
      + state_calc.
    - repeat (inversionss; try destruct_one_match_hyp).
      pose_flatten_var_ineqs.
      specialize (IHe1 _ _ _ _ _ _ w0 E Ex).
      specializes IHe1. {
        clear IHe2.
        state_calc.
      }
      { assumption. }
      destruct IHe1 as [fuel1 [midL [Ev1 G1]]].
      progress pose_flatten_var_ineqs.
      specialize (IHe2 _ _ _ _ initialH midL w1 E0).
      specializes IHe2.
      { state_calc. }
      { state_calc. }
      { assumption. }
      destruct IHe2 as [fuel2 [preFinalL [Ev2 G2]]].
      remember (Datatypes.S (Datatypes.S (fuel1 + fuel2))) as f0.
      remember (Datatypes.S (fuel1 + fuel2)) as f.
      exists (Datatypes.S f0) (put preFinalL resVar (Op.eval_binop op w0 w1)).
      pose_flatten_var_ineqs.
      split; [|apply get_put_same].
      simpl. fuel_increasing_rewrite.
      subst f0. simpl. fuel_increasing_rewrite.
      subst f. simpl.
      rename n0 into v.
      assert (get preFinalL v = Some w0) as G1'. {
        state_calc.
      }
      rewrite G1'. simpl. rewrite G2. simpl. reflexivity.
  Qed.

  Lemma flattenStmt_correct_aux:
    forall fuelH sH sL ngs ngs' initialH finalH initialL,
    flattenStmt ngs sH = (sL, ngs') ->
    extends initialL initialH ->
    undef initialH (allFreshVars ngs) ->
    disjoint (ExprImp.modVars sH) (allFreshVars ngs) ->
    ExprImp.eval_stmt fuelH initialH sH = Some finalH ->
    exists fuelL finalL,
      FlatImp.eval_stmt fuelL initialL sL = Success finalL /\
      extends finalL finalH.
  Proof.
    induction fuelH; introv F Ex U Di Ev; [solve [inversionss] |].
    destruct sH.
    - apply ExprImp.invert_eval_SSet in Ev.
      destruct Ev as [v [Ev Eq]].
      repeat (inversionss; try destruct_one_match_hyp).
      pose proof (flattenExpr_correct_aux _ _ _ _ _ _ _ _ E Ex U Ev) as P.
      destruct P as [fuelL [prefinalL [Evs G]]].
      remember (Datatypes.S fuelL) as SfuelL.
      exists (Datatypes.S SfuelL). eexists. repeat split.
      + simpl.
        assert (FlatImp.eval_stmt SfuelL initialL s = Success prefinalL) as Evs'. {
          eapply FlatImp.increase_fuel_still_Success; [|eassumption]. omega.
        }
        rewrite Evs'. subst SfuelL. simpl. rewrite G. simpl. reflexivity.
      + clear IHfuelH.
        pose_flatten_var_ineqs.
        state_calc.
    - inversions F. repeat destruct_one_match_hyp. destruct_pair_eqs. subst.
      apply ExprImp.invert_eval_SIf in Ev.
      destruct Ev as [cv [Evc Ev]].
      pose_flatten_var_ineqs.
      rename cond into condH, s into condL, s0 into sL1, s1 into sL2.
      pose proof (flattenExpr_correct_aux _ _ _ _ _ _ _ cv E Ex) as P.
      specializes P; [eassumption|eassumption|].
      destruct P as [fuelLcond [initial2L [Evcond G]]].
      destruct Ev as [[Ne EvThen] | [Eq EvElse]]; pose_flatten_var_ineqs.
      + specialize IHfuelH with (initialL := initial2L) (1 := E0) (5 := EvThen).
        destruct IHfuelH as [fuelL [finalL [Evbranch Ex2]]].
        * state_calc.
        * state_calc.
        * simpl in Di.
          set_solver.
        * exists (S (S (fuelLcond + fuelL))). eexists.
          refine (conj _ Ex2).
          remember (S (fuelLcond + fuelL)) as tempFuel.
          simpl.
          fuel_increasing_rewrite.
          subst tempFuel.
          simpl. rewrite G. simpl. destruct_one_match; [contradiction|].
          fuel_increasing_rewrite.
          reflexivity.
      + specialize (IHfuelH sH2 sL2 _ _ initialH finalH initial2L E1).
        specializes IHfuelH.
        * state_calc.
        * state_calc.
        * simpl in Di.
          set_solver.
        * exact EvElse.
        * destruct IHfuelH as [fuelL [finalL [Evbranch Ex2]]].
          exists (S (S (fuelLcond + fuelL))). eexists.
          refine (conj _ Ex2).
          remember (S (fuelLcond + fuelL)) as tempFuel.
          simpl.
          fuel_increasing_rewrite.
          subst tempFuel.
          simpl. rewrite G. simpl. destruct_one_match; [|contradiction].
          fuel_increasing_rewrite.
          reflexivity.
    - apply ExprImp.invert_eval_SWhile in Ev.
      simpl in Di.
      pose proof F as F0.
      simpl in F. do 3 destruct_one_match_hyp. destruct_pair_eqs. subst.
      rename s into sCond, s0 into sBody.
      destruct Ev as [cv [EvcondH Ev]].
      pose proof (flattenExpr_correct_aux _ _ _ _ _ _ _ cv E Ex) as P.
      specializes P; [eassumption|eassumption|].
      destruct P as [fuelLcond [initial2L [EvcondL G]]].
      destruct Ev as [Ev | Ev]; pose_flatten_var_ineqs.
      + destruct Ev as [Ne [middleH [Ev1H Ev2H]]].
        specialize IHfuelH with (1 := E0) (5 := Ev1H) as IH.
        specialize (IH initial2L).
        specializes IH.
        { state_calc. }
        { state_calc. }
        { set_solver. }
        destruct IH as [fuelL1 [middleL [EvL1 Ex1]]].
        pose_flatten_var_ineqs.
        specialize IHfuelH with (initialL := middleL) (1 := F0) (5 := Ev2H).
        specializes IHfuelH.
        { state_calc. }
        { pose proof (ExprImp.modVarsSound _ _ _ _ Ev1H) as D1.
          state_calc. }
        { set_solver. }
        destruct IHfuelH as [fuelL2 [finalL [EvL2 Ex2]]].
        exists (S (fuelL1 + fuelL2 + fuelLcond)) finalL.
        refine (conj _ Ex2).
        simpl.
        fuel_increasing_rewrite.
        rewrite G. simpl. destruct_one_match; [contradiction|].
        fuel_increasing_rewrite.
        fuel_increasing_rewrite.
        reflexivity.
      + destruct Ev as [? ?]. subst.
        exists (S fuelLcond) initial2L.
        split; [|state_calc].
        simpl.
        fuel_increasing_rewrite.
        rewrite G. simpl. destruct_one_match; [|contradiction]. reflexivity.
    - apply ExprImp.invert_eval_SSeq in Ev.
      destruct Ev as [middleH [Ev1 Ev2]].
      simpl in F. do 2 destruct_one_match_hyp. inversions F.
      pose proof IHfuelH as IHfuelH2.
      specializes IHfuelH.
      1: exact E. 1: exact Ex. 3: exact Ev1.
      { clear IHfuelH2. state_calc. }
      { simpl in Di. set_solver. }
      destruct IHfuelH as [fuelL1 [middleL [EvL1 Ex1]]].
      rename IHfuelH2 into IHfuelH.
      rename s into sL1, s0 into sL2.
      pose_flatten_var_ineqs.
      simpl in Di.
      pose proof (ExprImp.modVarsSound _ _ _ _ Ev1) as D1.
      specialize (IHfuelH sH2 sL2 _ _ middleH finalH middleL E0).
      specializes IHfuelH.
      1: exact Ex1. 3: exact Ev2.
      { state_calc. }
      { state_calc. }
      destruct IHfuelH as [fuelL2 [finalL [EvL2 Ex2]]].
      exists (S (fuelL1 + fuelL2)) finalL.
      refine (conj _ Ex2).
      simpl.
      fuel_increasing_rewrite. fuel_increasing_rewrite. reflexivity.
    - apply ExprImp.invert_eval_SSkip in Ev. subst finalH.
      simpl in F. inversions F.
      exists 1%nat initialL. auto.
  Qed.

  Definition ExprImp2FlatImp(s: ExprImp.stmt): FlatImp.stmt :=
    fst (flattenStmt (freshNameGenState (ExprImp.allVars_stmt s)) s).

  Lemma flattenStmt_correct: forall fuelH sH sL finalH,
    ExprImp2FlatImp sH = sL ->
    ExprImp.eval_stmt fuelH empty sH = Some finalH ->
    exists fuelL finalL,
      FlatImp.eval_stmt fuelL empty sL = Success finalL /\
      forall resVar res, get finalH resVar = Some res -> get finalL resVar = Some res.
  Proof.
    introv C EvH.
    unfold ExprImp2FlatImp, fst in C. destruct_one_match_hyp. subst s.
    pose proof flattenStmt_correct_aux as P.
    specialize P with (1 := E).
    specialize P with (4 := EvH).
    specialize P with (initialL := (@empty _ _ _ stateMap)).
    destruct P as [fuelL [finalL [EvL ExtL]]].
    - unfold extends. auto.
    - unfold undef. intros. apply empty_is_empty.
    - unfold disjoint.
      intro x.
      pose proof (freshNameGenState_spec (ExprImp.allVars_stmt sH) x) as P.
      destruct (in_dec eq_name_dec x (ExprImp.allVars_stmt sH)) as [Iyes | Ino].
      + auto.
      + left. clear -Ino.
        intro. apply Ino. apply ExprImp.modVars_subset_allVars. assumption.
    - exists fuelL finalL. apply (conj EvL).
      intros. state_calc.
  Qed.

End FlattenExpr.
