Require Import lib.LibTacticsMin.
Require Import compiler.util.Common.
Require compiler.ExprImp.
Require compiler.FlatImp.
Require Import compiler.StateCalculus.
Require Import compiler.NameGen.
Require Import bbv.DepEqNat.
Require Import compiler.NameWithEq.
Require Import riscv.util.BitWidths.

Section FlattenExpr.

  Context {Bw: BitWidths}.

  Context {Name: NameWithEq}.
  Notation var := (@name Name).
  Notation func := (@name Name) (only parsing). (* TODO use separate names *)

  Existing Instance eq_name_dec.

  Context {state: Type}.
  Context {stateMap: Map state var (word wXLEN)}.
  Context {vars: Type}.
  Context {varset: set vars var}.
  Context {NGstate: Type}.
  Context {NG: NameGen var vars NGstate}.

  Ltac state_calc := state_calc_generic (@name Name) (word wXLEN).
  Ltac set_solver := set_solver_generic (@name Name).

  (* returns and var into which result is saved, and new fresh name generator state
     TODO use state monad? *)
  Fixpoint flattenExpr(ngs: NGstate)(e: ExprImp.expr):
    (FlatImp.stmt * var * NGstate) :=
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

  Definition flattenCall(ngs: NGstate)(binds: list var)(f: func)(args: list ExprImp.expr):
    FlatImp.stmt * NGstate :=
    let '(compute_args, argvars, ngs) :=
          List.fold_right
            (fun e '(c, vs, ngs) =>
               let (ce_ve, ngs) := flattenExpr ngs e in
               let c := FlatImp.SSeq (fst ce_ve) c in
               (c, snd ce_ve::vs, ngs)
            ) (FlatImp.SSkip, nil, ngs) args in
      (FlatImp.SSeq compute_args (FlatImp.SCall binds f argvars), ngs).

  (* returns statement and new fresh name generator state *)
  Fixpoint flattenStmt(ngs: NGstate)(s: ExprImp.stmt): (FlatImp.stmt * NGstate) :=
    match s with
    | ExprImp.SLoad x a =>
        let '(s, r, ngs') := flattenExpr ngs a in
        (FlatImp.SSeq s (FlatImp.SLoad x r), ngs')
    | ExprImp.SStore a v =>
        let '(sa, ra, ngs') := flattenExpr ngs a in
        let '(sv, rv, ngs'') := flattenExpr ngs' v in
        (FlatImp.SSeq sa (FlatImp.SSeq sv (FlatImp.SStore ra rv)), ngs'')
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
    | ExprImp.SCall binds f args => flattenCall ngs binds f args
    end.

  Lemma flattenExpr_size: forall e s resVar ngs ngs',
    flattenExpr ngs e = (s, resVar, ngs') ->
    FlatImp.stmt_size s <= 2 * ExprImp.expr_size e.
  Proof.
    induction e; intros; simpl in *; repeat destruct_one_match_hyp; inversionss; simpl; try omega.
    specializes IHe1; [eassumption|].
    specializes IHe2; [eassumption|].
    omega.
  Qed.

  Lemma fold_right_cons: forall (A B: Type) (f: B -> A -> A) (a0: A) (b: B) (bs: list B),
      fold_right f a0 (b :: bs) = f b (fold_right f a0 bs).
  Proof.
    intros. reflexivity.
  Qed.

  Lemma flattenCall_size: forall f args binds ngs ngs' s,
      flattenCall ngs binds f args = (s, ngs') ->
      FlatImp.stmt_size s <= 3 * ExprImp.stmt_size (ExprImp.SCall binds f args).
  Proof.
    intro f.
    induction args; intros.
    - unfold flattenCall in *. simpl in H. inversions H. simpl. omega.
    - unfold flattenCall in *. simpl in H.
      repeat destruct_one_match_hyp.
      inversions H.
      inversions E.
      specialize (IHargs binds ngs).
      rewrite E0 in IHargs.
      specialize IHargs with (1 := eq_refl).
      unfold FlatImp.stmt_size. fold FlatImp.stmt_size.
      unfold ExprImp.stmt_size.
      unfold FlatImp.stmt_size in IHargs; fold FlatImp.stmt_size in IHargs.
      unfold ExprImp.stmt_size in IHargs.
      rewrite map_cons. rewrite fold_right_cons.
      destruct p.
      apply flattenExpr_size in E1.
      simpl (length _).
      simpl (fst _).
      forget (FlatImp.stmt_size s) as sz0.
      forget (FlatImp.stmt_size s1) as sz1.
      forget (length binds) as lb.
      forget (length l0) as ll0.
      forget (ExprImp.expr_size a) as sza.
      forget (fold_right Nat.add 0 (map ExprImp.expr_size args)) as fr.
      omega.
  Qed.

  Lemma flattenStmt_size: forall s s' ngs ngs',
    flattenStmt ngs s = (s', ngs') ->
    FlatImp.stmt_size s' <= 3 * ExprImp.stmt_size s.
  Proof.
    induction s; intros; simpl in *; repeat destruct_one_match_hyp; inversionss; simpl;
    repeat match goal with
    | IH: _, A: _ |- _ => specialize IH with (1 := A)
    end;
    repeat match goal with
    | H: _ |- _ => apply flattenExpr_size in H
    end;
    try omega.
    eapply flattenCall_size. eassumption.
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

  Lemma flattenCall_freshVarUsage: forall f args binds ngs1 ngs2 s,
      flattenCall ngs1 binds f args = (s, ngs2) ->
      subset (allFreshVars ngs2) (allFreshVars ngs1).
  Proof.
    induction args; cbn; intros.
    { inversionss; subst; set_solver. }
    { unfold flattenCall in *. simpl in H.
      repeat destruct_one_match_hyp.
      inversions H.
      inversions E.
      specialize (IHargs binds ngs1).
      rewrite E0 in IHargs.
      specialize IHargs with (1 := eq_refl).
      destruct p.
      apply flattenExpr_freshVarUsage in E1.
      clear -IHargs E1.
      set_solver. }
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
    try solve [set_solver].
    eapply flattenCall_freshVarUsage. eassumption.
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
    lazymatch goal with
    | Ev: FlatImp.eval_stmt ?ENV ?Fuel1 ?initialSt ?initialM ?s = ?final
      |- context [FlatImp.eval_stmt ?ENV ?Fuel2 ?initialSt ?initialM ?s]
      => let IE := fresh in assert (Fuel1 <= Fuel2) as IE by omega;
         eapply FlatImp.increase_fuel_still_Success in Ev; [|apply IE];
         clear IE;
         rewrite Ev
    end.

  (* Note: If you want to get in the conclusion
     "only_differ initialL (vars_range firstFree (S resVar)) finalL"
     this needn't be part of this lemma, because it follows from
     flattenExpr_modVars_spec and FlatImp.modVarsSound *)
  Lemma flattenExpr_correct_aux env : forall e ngs1 ngs2 resVar s initialH initialL initialM res,
    flattenExpr ngs1 e = (s, resVar, ngs2) ->
    extends initialL initialH ->
    undef initialH (allFreshVars ngs1) ->
    ExprImp.eval_expr initialH e = Some res ->
    exists fuel finalL,
      FlatImp.eval_stmt env fuel initialL initialM s = Some (finalL, initialM) /\
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
      specialize IHe1 with (initialM := initialM) (1 := E) (2 := Ex).
      specializes IHe1. {
        clear IHe2.
        state_calc.
      }
      { eassumption. }
      destruct IHe1 as [fuel1 [midL [Ev1 G1]]].
      progress pose_flatten_var_ineqs.
      specialize IHe2 with (initialH := initialH) (initialL := midL) (initialM := initialM)
         (1 := E0).
      specializes IHe2.
      { state_calc. }
      { state_calc. }
      { eassumption. }
      destruct IHe2 as [fuel2 [preFinalL [Ev2 G2]]].
      remember (Datatypes.S (Datatypes.S (fuel1 + fuel2))) as f0.
      remember (Datatypes.S (fuel1 + fuel2)) as f.
      exists (Datatypes.S f0) (put preFinalL resVar (Op.eval_binop op w w0)).
      pose_flatten_var_ineqs.
      split; [|apply get_put_same].
      simpl. fuel_increasing_rewrite.
      subst f0. simpl. fuel_increasing_rewrite.
      subst f. simpl.
      rename n0 into v.
      assert (get preFinalL v = Some w) as G1'. {
        state_calc.
      }
      rewrite G1'. simpl. rewrite G2. simpl. reflexivity.
  Qed.

  Lemma flattenStmt_correct_aux:
    forall fuelH sH sL ngs ngs' initialH finalH initialL initialM finalM,
    flattenStmt ngs sH = (sL, ngs') ->
    extends initialL initialH ->
    undef initialH (allFreshVars ngs) ->
    disjoint (ExprImp.modVars sH) (allFreshVars ngs) ->
    ExprImp.eval_stmt empty fuelH initialH initialM sH = Some (finalH, finalM) ->
    exists fuelL finalL,
      FlatImp.eval_stmt empty fuelL initialL initialM sL = Some (finalL, finalM) /\
      extends finalL finalH.
  Proof.
    induction fuelH; introv F Ex U Di Ev; [solve [inversionss] |].
    ExprImp.invert_eval_stmt.
    - repeat (inversionss; try destruct_one_match_hyp).
      match goal with
      | Ev: ExprImp.eval_expr _ _ = Some _ |- _ =>
        let P := fresh "P" in
        pose proof (flattenExpr_correct_aux empty) as P;
        specialize P with (initialM := initialM) (4 := Ev);
        specializes P; [ eassumption .. | ];
        let fuelL := fresh "fuelL" in
        let prefinalL := fresh "prefinalL" in
        destruct P as [fuelL [prefinalL P]];
        deep_destruct P;
        exists (S (S fuelL)); eexists
      end.
      remember (S fuelL) as SfuelL.
      split.
      + simpl in *.
        fuel_increasing_rewrite.
        subst SfuelL. simpl.
        rewrite_match.
        reflexivity.
      + clear IHfuelH.
        pose_flatten_var_ineqs.
        state_calc.
    - repeat (inversionss; try destruct_one_match_hyp).
      match goal with
      | Ev: ExprImp.eval_expr _ _ = Some _ |- _ =>
        let P := fresh "P" in
        pose proof (flattenExpr_correct_aux empty) as P;
        specialize P with (initialM := initialM) (4 := Ev);
        specializes P; [ eassumption .. | ];
        let fuelL := fresh "fuelL" in
        let prefinalL := fresh "prefinalL" in
        destruct P as [fuelL [prefinalL P]];
        deep_destruct P
      end.
      match goal with
      | Ev: ExprImp.eval_expr _ _ = Some _ |- _ =>
        let P := fresh "P" in
        pose proof (flattenExpr_correct_aux empty) as P;
        specialize P with (initialL := prefinalL) (initialM := initialM) (4 := Ev)
      end.
      specializes P1.
      { eassumption. }
      { pose_flatten_var_ineqs. clear IHfuelH. state_calc. }
      { pose_flatten_var_ineqs. clear IHfuelH. state_calc. }
      destruct P1 as [fuelL2 P1]. deep_destruct P1.
      exists (S (S (S (fuelL + fuelL2)))). eexists.
      remember (S (S (fuelL + fuelL2))) as Sf.
      split.
      + simpl in *. fuel_increasing_rewrite. simpl. subst Sf.
        remember (S (fuelL + fuelL2)) as Sf. simpl. fuel_increasing_rewrite.
        subst Sf. simpl. rewrite_match.
        assert (get finalL n0 = Some av) as G. {
          clear IHfuelH. pose_flatten_var_ineqs. state_calc.
        }
        rewrite_match.
        reflexivity.
      + clear IHfuelH.
        pose_flatten_var_ineqs.
        state_calc. (* TODO this takes more than a minute, which is annoying *)
    - repeat (inversionss; try destruct_one_match_hyp).
      pose proof flattenExpr_correct_aux as P.
      specialize (P empty) with (initialM := initialM) (1 := E) (2 := Ex) (3 := U) (4 := Ev0).
      destruct P as [fuelL [prefinalL [Evs G]]].
      remember (Datatypes.S fuelL) as SfuelL.
      exists (Datatypes.S SfuelL). eexists. repeat split.
      + simpl.
        assert (FlatImp.eval_stmt empty SfuelL initialL initialM s = Some (prefinalL, initialM)) as Evs'. {
          eapply FlatImp.increase_fuel_still_Success; [|eassumption]. omega.
        }
        simpl in *.
        rewrite Evs'. subst SfuelL. simpl. rewrite G. simpl. reflexivity.
      + clear IHfuelH.
        pose_flatten_var_ineqs.
        state_calc.
    - inversions F. repeat destruct_one_match_hyp. destruct_pair_eqs. subst.
      pose_flatten_var_ineqs.
      rename cond into condH, s into condL, s0 into sL1, s1 into sL2.
      pose proof (flattenExpr_correct_aux empty) as P.
      specialize P with (initialM := initialM) (res := cv) (1 := E) (2 := Ex).
      specializes P; [eassumption|eassumption|].
      destruct P as [fuelLcond [initial2L [Evcond G]]].
      pose_flatten_var_ineqs.
      specialize IHfuelH with (initialL := initial2L) (1 := E0) (5 := Ev).
      destruct IHfuelH as [fuelL [finalL [Evbranch Ex2]]].
      * state_calc.
      * state_calc.
      * simpl in Di.
        set_solver.
      * exists (S (S (fuelLcond + fuelL))). eexists.
        refine (conj _ Ex2).
        remember (S (fuelLcond + fuelL)) as tempFuel.
        simpl in *.
        fuel_increasing_rewrite.
        subst tempFuel.
        simpl. rewrite G. simpl. simpl_if.
        fuel_increasing_rewrite.
        reflexivity.
    - inversions F. repeat destruct_one_match_hyp. destruct_pair_eqs. subst.
      pose_flatten_var_ineqs.
      rename cond into condH, s into condL, s0 into sL1, s1 into sL2.
      pose proof flattenExpr_correct_aux as P.
      specialize (P empty) with (initialM := initialM) (res := $0) (1 := E) (2 := Ex).
      specializes P; [eassumption|eassumption|].
      destruct P as [fuelLcond [initial2L [Evcond G]]].
      pose_flatten_var_ineqs.
      specialize IHfuelH with (initialL := initial2L) (1 := E1) (5 := Ev).
      destruct IHfuelH as [fuelL [finalL [Evbranch Ex2]]].
      * state_calc.
      * state_calc.
      * simpl in Di.
        set_solver.
      * exists (S (S (fuelLcond + fuelL))). eexists.
        refine (conj _ Ex2).
        remember (S (fuelLcond + fuelL)) as tempFuel.
        simpl in *.
        fuel_increasing_rewrite.
        subst tempFuel.
        simpl. rewrite G. simpl. simpl_if.
        fuel_increasing_rewrite.
        reflexivity.
    - simpl in Di.
      pose proof F as F0.
      simpl in F. do 3 destruct_one_match_hyp. destruct_pair_eqs. subst.
      rename s into sCond, s0 into sBody.
      pose proof flattenExpr_correct_aux as P.
      specialize (P empty) with (res := cv) (initialM := initialM) (1 := E) (2 := Ex).
      specializes P; [eassumption|eassumption|].
      destruct P as [fuelLcond [initial2L [EvcondL G]]].
      pose_flatten_var_ineqs.
      specialize IHfuelH with (1 := E0) (5 := Ev2) as IH.
      specialize (IH initial2L).
      specializes IH.
      { state_calc. }
      { state_calc. }
      { set_solver. }
      destruct IH as [fuelL1 [middleL [EvL1 Ex1]]].
      pose_flatten_var_ineqs.
      specialize IHfuelH with (initialL := middleL) (1 := F0) (5 := Ev).
      specializes IHfuelH.
      { state_calc. }
      { pose proof ExprImp.modVarsSound as D1.
        specialize D1 with (1 := Ev2).
        state_calc. }
      { set_solver. }
      destruct IHfuelH as [fuelL2 [finalL [EvL2 Ex2]]].
      exists (S (fuelL1 + fuelL2 + fuelLcond)) finalL.
      refine (conj _ Ex2).
      simpl in *.
      fuel_increasing_rewrite.
      rewrite G. simpl. simpl_if.
      fuel_increasing_rewrite.
      fuel_increasing_rewrite.
      reflexivity.
    - simpl in Di.
      pose proof F as F0.
      simpl in F. do 3 destruct_one_match_hyp. destruct_pair_eqs. subst.
      rename s into sCond, s0 into sBody.
      pose proof (flattenExpr_correct_aux empty) as P.
      specialize P with (res := $0) (initialM := initialM) (1 := E) (2 := Ex).
      specializes P; [eassumption|eassumption|].
      destruct P as [fuelLcond [initial2L [EvcondL G]]].
      exists (S fuelLcond) initial2L.
      pose_flatten_var_ineqs.
      split; [|state_calc].
      simpl in*.
      fuel_increasing_rewrite.
      rewrite G. simpl. simpl_if. reflexivity.
    - simpl in F. do 2 destruct_one_match_hyp. inversions F.
      pose proof IHfuelH as IHfuelH2.
      specializes IHfuelH.
      1: exact E. 1: exact Ex. 3: eassumption.
      { clear IHfuelH2. state_calc. }
      { simpl in Di. set_solver. }
      destruct IHfuelH as [fuelL1 [middleL [EvL1 Ex1]]].
      rename IHfuelH2 into IHfuelH.
      rename s into sL1, s0 into sL2.
      pose_flatten_var_ineqs.
      simpl in Di.
      pose proof ExprImp.modVarsSound as D1.
      specialize D1 with (1 := Ev0).
      specialize IHfuelH with (1 := E0) (2 := Ex1).
      specializes IHfuelH. 3: eassumption.
      { state_calc. }
      { state_calc. }
      destruct IHfuelH as [fuelL2 [finalL [EvL2 Ex2]]].
      exists (S (fuelL1 + fuelL2)) finalL.
      refine (conj _ Ex2).
      simpl in *.
      fuel_increasing_rewrite. fuel_increasing_rewrite. reflexivity.
    - simpl in F. inversions F. destruct_pair_eqs.
      exists 1%nat initialL. auto.
    - inversion Ev0.
  Qed.

  Definition ExprImp2FlatImp(s: ExprImp.stmt): FlatImp.stmt :=
    fst (flattenStmt (freshNameGenState (ExprImp.allVars_stmt s)) s).

  Lemma flattenStmt_correct: forall fuelH sH sL initialM finalH finalM,
    ExprImp2FlatImp sH = sL ->
    ExprImp.eval_stmt empty fuelH empty initialM sH = Some (finalH, finalM) ->
    exists fuelL finalL,
      FlatImp.eval_stmt empty fuelL empty initialM sL = Some (finalL, finalM) /\
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
