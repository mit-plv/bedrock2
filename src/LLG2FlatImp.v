Require Import lib.LibTacticsMin.
Require Import compiler.Common.
Require Import compiler.ResMonad.
Require Import compiler.LLG.
Require Import compiler.FlatImp.
Require Import compiler.StateCalculus.
Require Import compiler.NameGen.
Require Import compiler.member.
Require Import compiler.Op.

Section LLG2FlatImp.

  Context {w: nat}. (* bit width *)
  Context {var: Set}.
  Context {eq_var_dec: DecidableEq var}.
  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.
  Context {vars: Type}.
  Context {varset: set vars var}.
  Context {NGstate: Type}.
  Context {NG: NameGen var vars NGstate}.

  Definition TODO{T: Type}: T. Admitted.

  Ltac admit_if_TODO :=
    match goal with
    | _: context [ TODO ] |- _ => exact TODO
    | _ => idtac
    end.

  (* returns and var into which result is saved, and new fresh name generator state
     TODO use state monad? *)
  Fixpoint compile{l G t}(ngs: NGstate)(e: @expr w var l G t){struct e}:
    (@stmt w var * var * NGstate) :=
    match e with
    | ELit n => let '(x, ngs') := genFresh ngs in
                    (SLit x n, x, ngs')
    | EVar x =>
        (* (SSkip, x, ngs)  would be simpler but doesn't satisfy the invariant that
            the returned var is in modVars of the returned statement *)
        let '(y, ngs') := genFresh ngs in
        (SSet y (member_get x), y, ngs')
    | EOp e1 op e2 =>
        let '(s1, r1, ngs') := compile ngs e1 in
        let '(s2, r2, ngs'') := compile ngs' e2 in
        let '(x, ngs''') := genFresh ngs'' in
        (SSeq s1 (SSeq s2 (SOp x op r1 r2)), x, ngs''')
    | ELet x e1 e2 =>
        let '(s1, r1, ngs') := compile ngs e1 in
        let '(s2, r2, ngs'') := compile ngs' e2 in
        (SSeq s1 (SSeq (SSet x r1) s2), r2, ngs'')
    | ENewArray t es => TODO
    | EGet ea ei => TODO
    | EUpdate ea ei ev => TODO
    | EFor i eto upd ebody erest =>
        let '(to_stmt, to_res, ngs') := compile ngs eto in
        let '(c, ngs'') := genFresh ngs' in
        let '(body_stmt, body_res, ngs''') := compile ngs'' ebody in
        let '(rest_stmt, rest_res, ngs'''') := compile ngs''' erest in
        let '(one, ngs''''') := genFresh ngs'''' in
        (SSeq (SLit one $1)
        (SSeq to_stmt
        (SSeq (SLit i $0)
        (SSeq (SLoop (SOp c OLt i to_res)
                     c
                     (SSeq body_stmt
                     (SSeq (SSet (member_get upd) body_res)
                           (SOp i OPlus i one))))
         rest_stmt))),
         rest_res, ngs''''')
    end.

  Ltac state_calc_instantiation := state_calc var (word w).
  Ltac state_calc := state_calc_instantiation.

  Lemma compile_freshVarUsage: forall l G t (e: expr l G t) ngs ngs' s v,
    compile ngs e = (s, v, ngs') ->
    subset (allFreshVars ngs') (allFreshVars ngs).
  Proof.
    induction e; intros; repeat (inversionss; try destruct_one_match_hyp);
    admit_if_TODO;
    repeat match goal with
    | H: _ |- _ => apply genFresh_spec in H
    end;
    try (specializes IHe1; [ eassumption | ]);
    try (specializes IHe2; [ eassumption | ]);
    try (specializes IHe3; [ eassumption | ]);
    set_solver var.
  Qed.

  Lemma compile_modifies_resVar: forall l G t (e: expr l G t) s ngs ngs' resVar,
    compile ngs e = (s, resVar, ngs') ->
    resVar \in (modVars s).
  Proof.
    intros.
    destruct e; repeat (inversionss; try destruct_one_match_hyp); simpl in *; set_solver var.
  Admitted.

  Lemma compile_resVar: forall l G t (e: expr l G t) s ngs ngs' resVar,
    compile ngs e = (s, resVar, ngs') ->
    ~ resVar \in (allFreshVars ngs').
  Proof.
    intros. destruct e; repeat (inversionss; try destruct_one_match_hyp); simpl in *;
    repeat match goal with
    | H: _ |- _ => apply genFresh_spec in H
    end;
    set_solver var.
  Admitted.

  Lemma compile_modVars_spec: forall l G t (e: expr l G t) s ngs ngs' resVar,
    compile ngs e = (s, resVar, ngs') ->
    subset (modVars s) (diff (allFreshVars ngs) (allFreshVars ngs')).
  Proof.
  Admitted. (*
    induction e; intros; repeat (inversionss; try destruct_one_match_hyp);
    admit_if_TODO;
    simpl;
    try (specializes IHe1; [ eassumption | ]);
    try (specializes IHe2; [ eassumption | ]);
    try (specializes IHe3; [ eassumption | ]);
    repeat match goal with
    | H: _ |- _ => apply genFresh_spec in H
    | H: _ |- _ => apply compile_freshVarUsage in H
    end;
    set_solver var.
  *)


  Ltac pose_flatten_var_ineqs :=
    repeat match goal with
    | H: _ |- _ => unique apply compile_freshVarUsage in copy of H
    | H: _ |- _ => unique apply modVarsSound in copy of H
    | H: _ |- _ => unique apply compile_modifies_resVar in copy of H
    | H: _ |- _ => unique apply compile_modVars_spec in copy of H
    end.

  Tactic Notation "nofail" tactic3(t) := first [ t | fail 1000 "should not have failed"].

  Ltac fuel_increasing_rewrite :=
    match goal with
    | Ev: eval_stmt ?Fuel1 ?initial ?s = ?final
      |- context [eval_stmt ?Fuel2 ?initial ?s]
      => let IE := fresh in assert (Fuel1 <= Fuel2) as IE by omega;
         apply (increase_fuel_still_Success _ _ _ _ _ IE) in Ev;
         clear IE;
         rewrite Ev
    end.

(*
  (* Note: If you want to get in the conclusion
     "only_differ initialL (vars_range firstFree (S resVar)) finalL"
     this needn't be part of this lemma, because it follows from
     compile_modVars_spec and modVarsSound *)
  Lemma compile_correct_aux: forall e ngs1 ngs2 resVar s initialH initialL res,
    compile ngs1 e = (s, resVar, ngs2) ->
    extends initialL initialH ->
    undef initialH (allFreshVars ngs1) ->
    eval_expr initialH e = Some res ->
    exists fuel finalL,
      eval_stmt fuel initialL s = Success finalL /\
      get finalL resVar = Some res.
  Proof.
    induction e; introv F Ex U Ev.
    - repeat (inversionss; try destruct_one_match_hyp).
      exists 1%nat (put initialL resVar res).
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
    disjoint (modVars sH) (allFreshVars ngs) ->
    eval_stmt fuelH initialH sH = Some finalH ->
    exists fuelL finalL,
      eval_stmt fuelL initialL sL = Success finalL /\
      extends finalL finalH.
  Proof.
    induction fuelH; introv F Ex U Di Ev; [solve [inversionss] |].
    destruct sH.
    - apply invert_eval_SSet in Ev.
      destruct Ev as [v [Ev Eq]].
      repeat (inversionss; try destruct_one_match_hyp).
      pose proof (compile_correct_aux _ _ _ _ _ _ _ _ E Ex U Ev) as P.
      destruct P as [fuelL [prefinalL [Evs G]]].
      remember (Datatypes.S fuelL) as SfuelL.
      exists (Datatypes.S SfuelL). eexists. repeat split.
      + simpl.
        assert (eval_stmt SfuelL initialL s = Success prefinalL) as Evs'. {
          eapply increase_fuel_still_Success; [|eassumption]. omega.
        }
        rewrite Evs'. subst SfuelL. simpl. rewrite G. simpl. reflexivity.
      + clear IHfuelH.
        pose_flatten_var_ineqs.
        state_calc.
    - inversions F. repeat destruct_one_match_hyp. destruct_pair_eqs. subst.
      apply invert_eval_SIf in Ev.
      destruct Ev as [cv [Evc Ev]].
      pose_flatten_var_ineqs.
      rename cond into condH, s into condL, s0 into sL1, s1 into sL2.
      pose proof (compile_correct_aux _ _ _ _ _ _ _ cv E Ex) as P.
      specializes P; [eassumption|eassumption|].
      destruct P as [fuelLcond [initial2L [Evcond G]]].
      destruct Ev as [[Ne EvThen] | [Eq EvElse]]; pose_flatten_var_ineqs.
      + specialize (IHfuelH sH1 sL1 n n0 initialH finalH initial2L E0).
        specializes IHfuelH.
        * state_calc.
        * state_calc.
        * simpl in Di.
          set_solver var.
        * exact EvThen.
        * destruct IHfuelH as [fuelL [finalL [Evbranch Ex2]]].
          exists (S (S (fuelLcond + fuelL))). eexists.
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
          set_solver var.
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
    - apply invert_eval_SWhile in Ev.
      simpl in Di.
      pose proof F as F0.
      simpl in F. do 3 destruct_one_match_hyp. destruct_pair_eqs. subst.
      rename s into sCond, s0 into sBody.
      destruct Ev as [cv [EvcondH Ev]].
      pose proof (compile_correct_aux _ _ _ _ _ _ _ cv E Ex) as P.
      specializes P; [eassumption|eassumption|].
      destruct P as [fuelLcond [initial2L [EvcondL G]]].
      destruct Ev as [Ev | Ev]; pose_flatten_var_ineqs.
      + destruct Ev as [Ne [middleH [Ev1H Ev2H]]].
        specialize IHfuelH with (1 := E0) (5 := Ev1H) as IH.
        specialize (IH initial2L).
        specializes IH.
        { state_calc. }
        { state_calc. }
        { set_solver var. }
        destruct IH as [fuelL1 [middleL [EvL1 Ex1]]].
        pose_flatten_var_ineqs.
        specialize IHfuelH with (initialL := middleL) (1 := F0) (5 := Ev2H).
        specializes IHfuelH.
        { state_calc. }
        { pose proof (modVarsSound _ _ _ _ Ev1H) as D1.
          state_calc. }
        { set_solver var. }
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
    - apply invert_eval_SSeq in Ev.
      destruct Ev as [middleH [Ev1 Ev2]].
      simpl in F. do 2 destruct_one_match_hyp. inversions F.
      pose proof IHfuelH as IHfuelH2.
      specializes IHfuelH.
      1: exact E. 1: exact Ex. 3: exact Ev1.
      { clear IHfuelH2. state_calc. }
      { simpl in Di. set_solver var. }
      destruct IHfuelH as [fuelL1 [middleL [EvL1 Ex1]]].
      rename IHfuelH2 into IHfuelH.
      rename s into sL1, s0 into sL2.
      pose_flatten_var_ineqs.
      simpl in Di.
      pose proof (modVarsSound _ _ _ _ Ev1) as D1.
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
    - apply invert_eval_SSkip in Ev. subst finalH.
      simpl in F. inversions F.
      exists 1%nat initialL. auto.
  Qed.
*)
End LLG2FlatImp.
