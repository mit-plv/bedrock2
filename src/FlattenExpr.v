Require Import lib.LibTactics.
Require Import compiler.Common.
Require Import compiler.ResMonad.
Require compiler.ExprImp.
Require compiler.FlatImp.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import compiler.Axioms.
Require Import compiler.StateCalculus.
Require Import compiler.NameGen.

(* TODO automate such that we don't to Require this, and not always specify which lemma to use *)
Require compiler.StateCalculusTacticTest.

Open Scope Z.

Section FlattenExpr.

  Context {w: nat}. (* bit width *)
  Context {var: Set}.
  Context {eq_var_dec: DecidableEq var}.
  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.
  Context {vars: Type}.
  Context {varset: set vars var}.
  Context {NGstate: Type}.
  Context {NG: NameGen var vars NGstate}.

  (* returns and var into which result is saved, and new fresh name generator state
     TODO use state monad? *)
  Fixpoint flattenExpr(ngs: NGstate)(e: @ExprImp.expr w var):
    (@FlatImp.stmt w var * var * NGstate) :=
    match e with
    | ExprImp.ELit n =>
        let '(x, ngs') := genFresh ngs in
        (FlatImp.SLit x n, x, ngs')
    | ExprImp.EVar x =>
        (FlatImp.SSkip, x, ngs)
    | ExprImp.EOp op e1 e2 =>
        let '(s1, r1, ngs') := flattenExpr ngs e1 in
        let '(s2, r2, ngs'') := flattenExpr ngs' e2 in
        let '(x, ngs''') := genFresh ngs'' in
        (FlatImp.SSeq s1 (FlatImp.SSeq s2 (FlatImp.SOp x op r1 r2)), x, ngs''')
    end.

  (* returns statement and new fresh name generator state *)
  Fixpoint flattenStmt(ngs: NGstate)(s: @ExprImp.stmt w var):
    (@FlatImp.stmt w var * NGstate) :=
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

  Lemma set_extensionality: forall (T: Type) s1 s2,
    (forall (x: T), x \in s1 <-> x \in s2) -> s1 = s2.
  Proof.
    intros. extensionality x. apply prop_ext. apply H.
  Qed.

  Lemma flattenExpr_modVars_spec: forall e s firstFree resVar,
    flattenExpr firstFree e = (s, resVar) ->
    FlatImp.modVars s = vars_range firstFree (S resVar) /\ firstFree <= resVar.
  Proof.
    Opaque union.
    induction e; introv E; inversions E; try solve [split; [simpl; apply vars_one_range | omega]].
    destruct (flattenExpr firstFree e1) as [p1 r1] eqn: E1.
    destruct (flattenExpr (S r1) e2) as [p2 r2] eqn: E2.
    inversions H0.
    simpl.
    specialize (IHe1 _ _ _ E1). destruct IHe1 as [IH1a IH1b].
    specialize (IHe2 _ _ _ E2). destruct IHe2 as [IH2a IH2b].
    rewrite IH1a, IH2a.
    unfold var in *. unfold S in *.
    split; [|omega].
    rewrite range_union_inc_r by omega.
    apply range_union_adj. omega.
  Qed.

  Lemma flattenStmt_vars_range: forall s s' firstFree newFirstFree,
    flattenStmt firstFree s = (s', newFirstFree) ->
    firstFree <= newFirstFree.
  Proof.
    induction s; introv E; inversions E; unfold var in *; unfold S in *;
    try omega; repeat destruct_one_match_hyp; repeat destruct_pair_eqs;
    try match goal with
    | H: _ |- _ => apply flattenExpr_modVars_spec in H
    end;
    try rename IHs into IHs1;
    try match goal with
    | H: _ |- _ => apply IHs1 in H
    end;
    try match goal with
    | H: _ |- _ => apply IHs2 in H
    end;
    try omega.
  Qed.

  Ltac pose_flatten_var_ineqs :=
    repeat match goal with
    | H: flattenExpr _ _ = _ |- _ =>
         let H' := fresh H in pose proof H as H';
         apply flattenExpr_modVars_spec in H';
         ensure_new H'
    | H: flattenStmt _ _ = _ |- _ =>
         let H' := fresh H in pose proof H as H';
         apply flattenStmt_vars_range in H';
         ensure_new H'
    end.

  Lemma increase_fuel_still_Success: forall fuel1 fuel2 initial s final,
    (fuel1 <= fuel2)%nat ->
    FlatImp.eval_stmt fuel1 initial s = Success final ->
    FlatImp.eval_stmt fuel2 initial s = Success final.
  Proof.
    induction fuel1; introv L Ev.
    - inversions Ev.
    - destruct fuel2; [omega|]. destruct s.
      + exact Ev.
      + exact Ev.
      + exact Ev.
      + simpl in *. destruct_one_match; try discriminate.
        erewrite IHfuel1; [reflexivity | omega | exact Ev].
      + apply FlatImp.invert_eval_SLoop in Ev.
        destruct Ev as [Ev | Ev]. 
        * destruct Ev as [Ev C]. 
          simpl. erewrite IHfuel1; [|omega|eassumption].
          rewrite C. simpl. destruct_one_match; [reflexivity | contradiction].
        * destruct Ev as [mid2 [mid3 [cv [Ev1 [C1 [C2 [Ev2 Ev3]]]]]]].
          simpl.
          erewrite IHfuel1; [|omega|eassumption].
          erewrite IHfuel1; [|omega|eassumption].
          erewrite IHfuel1; [|omega|eassumption].
          rewrite C1. simpl.
          destruct_one_match; [ contradiction | reflexivity ].
     + apply FlatImp.invert_eval_SSeq in Ev.
       destruct Ev as [mid [Ev1 Ev2]].
       simpl.
       erewrite IHfuel1; [|omega|eassumption].
       erewrite IHfuel1; [|omega|eassumption].
       reflexivity.
     + simpl. inversionss. reflexivity.
  Qed.

  Definition vars_range_subset: forall lo1 hi1 lo2 hi2,
    lo1 >= lo2 ->
    hi1 <= hi2 ->
    subset (vars_range lo1 hi1) (vars_range lo2 hi2).
  Proof.
    unfold subset, vars_range, contains. simpl. unfold id. intros. omega.
  Qed.

  Tactic Notation "nofail" tactic3(t) := first [ t | fail 1000 "should not have failed"].

  Ltac myomega := unfold S, var in *; omega.

  (* Note: If you want to get in the conclusion
     "only_differ initialL (vars_range firstFree (S resVar)) finalL"
     this needn't be part of this lemma, because it follows from
     flattenExpr_modVars_spec and FlatImp.modVarsSound *)
  Lemma flattenExpr_correct_aux: forall e firstFree resVar s initialH initialL res,
    flattenExpr firstFree e = (s, resVar) ->
    extends initialL initialH ->
    undef initialH (vars_range firstFree (S resVar)) ->
    ExprImp.eval_expr initialH e = Some res ->
    exists fuel finalL,
      FlatImp.eval_stmt fuel initialL s = Success finalL /\
      get finalL resVar = Some res.
  Proof.
    induction e; introv F Ex U Ev.
    - inversionss.
      exists 1%nat (put initialL resVar res). rewrite <- vars_one_range in *.
      unfold FlatImp.vars_one in *.
      repeat split; state_calc.
    - inversionss.
      exists 1%nat (put initialL resVar res). repeat split.
      + simpl. unfold extends in Ex. apply Ex in H0. rewrite H0. reflexivity.
      + rewrite get_put_same. symmetry. assumption.
    - inversionss. repeat (destruct_one_match_hyp; try discriminate). inversionss.
      specialize (IHe1 _ _ _ _ _ w0 E Ex).
      specializes IHe1. {
        repeat match goal with
        | H : _  |- _ => apply flattenExpr_modVars_spec in H
        end.
        assert (subset (vars_range firstFree (S v)) (vars_range firstFree (S (S v0)))). {
          eapply vars_range_subset; myomega.
        }
        clear IHe2.
        state_calc.
      }
      assumption.
      destruct IHe1 as [fuel1 [midL [Ev1 G1]]].
      specialize (IHe2 _ _ _ initialH midL w1 E0).
      specializes IHe2.
      { apply flattenExpr_modVars_spec in E.
        apply flattenExpr_modVars_spec in E0.
        assert (subset (vars_range firstFree (S v)) (vars_range firstFree (S (S v0)))). {
          eapply vars_range_subset; myomega.
        }
        (* TODO make this work without this hint *)
        refine (compiler.StateCalculusTacticTest.extends_if_only_differ_in_undef
            _ _ _ (vars_range firstFree (S v)) Ex _ _); [ state_calc |].
        destruct E as [Ea Eb].
        pose proof (FlatImp.modVarsSound _ _ _ _ Ev1) as D1.
        rewrite Ea in D1.
        exact D1. }
      { apply flattenExpr_modVars_spec in E.
        apply flattenExpr_modVars_spec in E0.
        assert (subset (vars_range (S v) (S v0)) (vars_range firstFree (S (S v0)))). {
          eapply vars_range_subset; myomega.
        }
        state_calc.
        (* TODO make this work without the assert hint *) }
      { assumption. }
      destruct IHe2 as [fuel2 [preFinalL [Ev2 G2]]].
      remember (Datatypes.S (Datatypes.S (fuel1 + fuel2))) as f0.
      remember (Datatypes.S (fuel1 + fuel2)) as f.
      exists (Datatypes.S f0) (put preFinalL (S v0) (Op.eval_binop op w0 w1)).
      repeat split.
      + simpl. erewrite increase_fuel_still_Success; [| |eassumption]; [|omega].
        apply increase_fuel_still_Success with (fuel1 := f0); [omega|].
        subst f0. simpl.
        erewrite (increase_fuel_still_Success _ _ midL); [| |eassumption]; [|omega].
        subst f. simpl.
        assert (get preFinalL v = Some w0) as G1'. {
          (* TODO automate *)
          assert (only_differ midL (vars_range (S v) (S v0)) preFinalL) as D2. {
            pose_flatten_var_ineqs.
            destruct E3 as [E3a E3b].
            pose proof (FlatImp.modVarsSound _ _ _ _ Ev2) as D2.
            rewrite E3a in D2.
            exact D2.
          }
          eapply compiler.StateCalculusTacticTest.only_differ_get_unchanged; try eassumption.
          rewrite in_vars_range. myomega.
        }
        rewrite G1'. simpl. rewrite G2. simpl. reflexivity.
      + apply get_put_same.
  Qed.

  Lemma flattenStmt_correct_aux:
    forall fuelH sH sL firstFree newFirstFree initialH finalH initialL,
    flattenStmt firstFree sH = (sL, newFirstFree) ->
    extends initialL initialH ->
    undef initialH (vars_range firstFree newFirstFree) ->
    disjoint (ExprImp.modVars sH) (vars_range firstFree newFirstFree) ->
    ExprImp.eval_stmt fuelH initialH sH = Some finalH ->
    exists fuelL finalL,
      FlatImp.eval_stmt fuelL initialL sL = Success finalL /\
      extends finalL finalH.
  Proof.
    induction fuelH; introv F Ex U Di Ev; [solve [inversionss] |].
    destruct sH.
    - apply ExprImp.invert_eval_SSet in Ev.
      destruct Ev as [v [Ev Eq]].
      inversions F. destruct_one_match_hyp. destruct_pair_eqs. subst.
      pose proof (flattenExpr_correct_aux _ _ _ _ _ _ _ E Ex U Ev) as P.
      destruct P as [fuelL [prefinalL [Evs G]]].
      remember (Datatypes.S fuelL) as SfuelL.
      exists (Datatypes.S SfuelL). eexists. repeat split.
      + simpl.
        assert (FlatImp.eval_stmt SfuelL initialL s = Success prefinalL) as Evs'. {
          eapply increase_fuel_still_Success; [|eassumption]. omega.
        }
        rewrite Evs'. subst SfuelL. simpl. rewrite G. simpl. reflexivity.
      + clear IHfuelH. apply compiler.StateCalculusTacticTest.extends_put_same.
        eapply compiler.StateCalculusTacticTest.extends_if_only_differ_in_undef;
        [ eassumption | eassumption | ].
        pose_flatten_var_ineqs.
        apply proj1 in E0. rewrite <- E0.
        eapply FlatImp.modVarsSound. eassumption.
    - inversions F. repeat destruct_one_match_hyp. destruct_pair_eqs. subst.
      apply ExprImp.invert_eval_SIf in Ev.
      destruct Ev as [cv [Evc Ev]].
      pose_flatten_var_ineqs.
      rename cond into condH, s into condL, s0 into sL1, s1 into sL2.
      pose proof (flattenExpr_correct_aux _ _ _ _ _ _ cv E Ex) as P.
      specializes P; [|eassumption|]. {
        eapply compiler.StateCalculusTacticTest.undef_shrink; [eassumption|].
        apply vars_range_subset; omega.
      }
      destruct P as [fuelLcond [initial2L [Evcond G]]].
      destruct Ev as [[Ne EvThen] | [Eq EvElse]].
      + specialize (IHfuelH sH1 sL1 (S v) v0 initialH finalH initial2L E0).
        specializes IHfuelH.
        * assert (only_differ initialL (vars_range firstFree (S v)) initial2L) as D. {
            apply proj1 in E2. rewrite <- E2. eapply FlatImp.modVarsSound. eassumption.
          }
          (* TODO this should be state_calc *)
          clear - U D Ex E3 E4.
          eapply compiler.StateCalculusTacticTest.extends_if_only_differ_in_undef.
          3: exact D. 1: exact Ex.
          clear Ex D.
          unfold undef in *. intros. specialize (U x).
          rewrite? in_vars_range in *.
          apply U. myomega.
        * eapply compiler.StateCalculusTacticTest.undef_shrink; [eassumption|].
          apply vars_range_subset; myomega.
        * simpl in Di.
          destruct E2 as [_ E2].
          clear - E2 E3 E4 Di U.
          unfold disjoint.
          intros. specialize (Di x).
          Fail rewrite union_spec in *. (* why?? *)
          rewrite union_spec in Di. (* while this one works!! *)
          rewrite in_vars_range in *.
          intuition myomega.
        * exact EvThen.
        * destruct IHfuelH as [fuelL [finalL [Evbranch Ex2]]].
          exists (Datatypes.S (fuelLcond + (Datatypes.S fuelL))). eexists.
          refine (conj _ Ex2).
          simpl.
          pose proof increase_fuel_still_Success as P.
          assert (fuelLcond <= fuelLcond + (Datatypes.S fuelL))%nat as IE by omega.
          specializes P. { eapply IE. } { eapply Evcond. }
          rewrite P. clear IE P.
          pose proof increase_fuel_still_Success as P.
          assert (Datatypes.S fuelL <= fuelLcond + (Datatypes.S fuelL))%nat as IE by omega.
          eapply (P _ _ _ _ _ IE). clear IE P.
          simpl. rewrite G. simpl. destruct_one_match; [contradiction|].
          exact Evbranch.
      + specialize (IHfuelH sH2 sL2 v0 newFirstFree initialH finalH initial2L E1).
        specializes IHfuelH.
        * assert (only_differ initialL (vars_range firstFree (S v)) initial2L) as D. {
            apply proj1 in E2. rewrite <- E2. eapply FlatImp.modVarsSound. eassumption.
          } (* TODO this should be state_calc *)
          clear - U D Ex E3 E4.
          eapply compiler.StateCalculusTacticTest.extends_if_only_differ_in_undef.
          3: exact D. 1: exact Ex.
          clear Ex D.
          unfold undef in *. intros. specialize (U x).
          rewrite? in_vars_range in *.
          apply U. myomega.
        * eapply compiler.StateCalculusTacticTest.undef_shrink; [eassumption|].
          apply vars_range_subset; myomega.
        * simpl in Di.
          destruct E2 as [_ E2].
          clear - E2 E3 E4 Di U.
          unfold disjoint.
          intros. specialize (Di x).
          Fail rewrite union_spec in *. (* why?? *)
          rewrite union_spec in Di. (* while this one works!! *)
          rewrite in_vars_range in *.
          intuition myomega.
        * exact EvElse.
        * destruct IHfuelH as [fuelL [finalL [Evbranch Ex2]]].
          exists (Datatypes.S (fuelLcond + (Datatypes.S fuelL)))%nat. eexists.
          refine (conj _ Ex2).
          simpl.
          pose proof increase_fuel_still_Success as P.
          assert (fuelLcond <= fuelLcond + (Datatypes.S fuelL))%nat as IE by omega.
          specializes P. { eapply IE. } { eapply Evcond. }
          rewrite P. clear IE P.
          pose proof increase_fuel_still_Success as P.
          assert (Datatypes.S fuelL <= fuelLcond + (Datatypes.S fuelL))%nat as IE by omega.
          eapply (P _ _ _ _ _ IE). clear IE P.
          simpl. rewrite G. simpl. destruct_one_match; [|contradiction].
          exact Evbranch.
    - admit. (* TODO while *)
    - apply ExprImp.invert_eval_SSeq in Ev.
      destruct Ev as [middleH [Ev1 Ev2]].
      simpl in F. do 2 destruct_one_match_hyp. inversions F.
      pose proof IHfuelH as IHfuelH2.
      specializes IHfuelH.
      1: exact E. 1: exact Ex. 3: exact Ev1.
      { eapply StateCalculusTacticTest.undef_shrink; [eassumption|].
        unfold subset. intro.
        rewrite? in_vars_range. pose_flatten_var_ineqs. intros. myomega. }
      { simpl in Di. admit. (* TODO *)
      
      }
      destruct IHfuelH as [fuelL1 [middleL [EvL1 Ex1]]].
      rename IHfuelH2 into IHfuelH.
      rename s into sL1, s0 into sL2.
      specialize (IHfuelH sH2 sL2 v newFirstFree middleH finalH middleL).
      specializes IHfuelH.
      1: exact E0. 1: exact Ex1. 3: exact Ev2.
      { admit. (* TODO *) }
      { pose proof (ExprImp.modVarsSound _ _ _ _ Ev1) as D1.
        pose_flatten_var_ineqs.
        clear -D1 Di U. (* tricky, need to relate modVars range to "fresh" range *)
        admit. }
      
      admit. (* TODO seq *)

    - apply ExprImp.invert_eval_SSkip in Ev. subst finalH.
      simpl in F. inversions F.
      exists 1%nat initialL. auto.
  Qed.

End FlattenExpr.
