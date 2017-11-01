Require Import lib.LibTactics.
Require Import compiler.Common.
Require Import compiler.ResMonad.
Require compiler.ExprImp.
Require compiler.FlatImp.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import compiler.Axioms.
Require Import compiler.StateCalculus.

Section FlattenExpr.

  Context {w: nat}. (* bit width *)
  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.

  (* returns statement and var into which result is saved, and that's the highest used var *)
  Fixpoint flattenExpr(firstFree: var)(e: @ExprImp.expr w): (@FlatImp.stmt w * var) :=
    match e with
    | ExprImp.ELit n => (FlatImp.SLit firstFree n, firstFree)
    | ExprImp.EVar x => (FlatImp.SSet firstFree x, firstFree)
       (* returning "(FlatImp.SSkip, x)" would be simpler but that doesn't respect the invariant
          that the returned var is >= firstFree *)
    | ExprImp.EOp op e1 e2 =>
        let (p1, r1) := flattenExpr firstFree e1 in
        let (p2, r2) := flattenExpr (S r1) e2 in
        (FlatImp.SSeq p1 (FlatImp.SSeq p2 (FlatImp.SOp (S r2) op r1 r2)), S r2)
    end.

  (* returns statement and new first free var *)
  Fixpoint flattenStmt(firstFree: var)(s: @ExprImp.stmt w): (@FlatImp.stmt w * var) :=
    match s with
    | ExprImp.SSet x e =>
        let (e', r) := flattenExpr firstFree e in
        (FlatImp.SSeq e' (FlatImp.SSet x r), S r)
    | ExprImp.SIf cond sThen sElse =>
        let (cond', r1) := flattenExpr firstFree cond in
        let (sThen', f2) := flattenStmt (S r1) sThen in
        let (sElse', f3) := flattenStmt f2 sElse in
        (FlatImp.SSeq cond' (FlatImp.SIf r1 sThen' sElse'), f3)
    | ExprImp.SWhile cond body =>
        let (cond', r1) := flattenExpr firstFree cond in
        let (body', f2) := flattenStmt (S r1) body in
        (FlatImp.SLoop cond' r1 body', f2)
    | ExprImp.SSeq s1 s2 =>
        let (s1', f1) := flattenStmt firstFree s1 in
        let (s2', f2) := flattenStmt f1 s2 in
        (FlatImp.SSeq s1' s2', f2)
    | ExprImp.SSkip => (FlatImp.SSkip, firstFree)
    end.

  (* Alternative:

  (* returns statement, var into which result is saved, and new first free var *)
  Fixpoint flattenExpr(firstFree: var)(e: @ExprImp.expr w): (@FlatImp.stmt w * var * var) :=
    match e with
    | ExprImp.ELit n => (FlatImp.SLit firstFree n, firstFree, S firstFree)
    | ExprImp.EVar x => (FlatImp.SSkip, x, firstFree)
    | ExprImp.EOp op e1 e2 =>
        let '(p1, r1, f1) := flattenExpr firstFree e1 in
        let '(p2, r2, f2) := flattenExpr f1 e2 in
        (FlatImp.SSeq p1 (FlatImp.SSeq p2 (FlatImp.SOp (S f2) op r1 r2)), S f2, S (S f2))
    end.
  *)

  (* Alternative (violates "extends finalL initialL"):

  (* returns statement and new first free var *)
  Fixpoint flattenExpr(firstFree res: var)(e: @ExprImp.expr w): (@FlatImp.stmt w * var) :=
    match e with
    | ExprImp.ELit n => (FlatImp.SLit res n, firstFree)
    | ExprImp.EVar x => (FlatImp.SSet res x, firstFree)
    | ExprImp.EOp op e1 e2 =>
        let (p1, f1) := flattenExpr (S firstFree) firstFree e1 in
        let (p2, f2) := flattenExpr (S f1) f1 e2 in
        (FlatImp.SSeq p1 (FlatImp.SSeq p2 (FlatImp.SOp res op firstFree f1)), f2)
    end.

  (* returns statement and new first free var *)
  Fixpoint flattenStmt(firstFree: var)(s: @ExprImp.stmt w): (@FlatImp.stmt w * var) :=
    match s with
    | ExprImp.SSet x e => flattenExpr firstFree x e
    | ExprImp.SIf cond sThen sElse =>
        let (cond', f1) := flattenExpr (S firstFree) firstFree cond in
        let (sThen', f2) := flattenStmt f1 sThen in
        let (sElse', f3) := flattenStmt f2 sElse in
        (FlatImp.SSeq cond' (FlatImp.SIf firstFree sThen' sElse'), f3)
    | ExprImp.SWhile cond body =>
        let (cond', f1) := flattenExpr (S firstFree) firstFree cond in
        let (body', f2) := flattenStmt f1 body in
        (FlatImp.SLoop cond' firstFree body', f2)
    | ExprImp.SSeq s1 s2 =>
        let (s1', f1) := flattenStmt firstFree s1 in
        let (s2', f2) := flattenStmt f1 s2 in
        (FlatImp.SSeq s1' s2', f2)
    | ExprImp.SSkip => (FlatImp.SSkip, firstFree)
    end.
  *)

  Definition vars_one(x: var): vars := singleton_set x.

  (* returns the set of modified vars *)
  Fixpoint modVars(s: @FlatImp.stmt w): vars :=
    match s with
    | FlatImp.SLit x v => vars_one x
    | FlatImp.SOp x op y z => vars_one x
    | FlatImp.SSet x y => vars_one x
    | FlatImp.SIf cond bThen bElse =>
        union (modVars bThen) (modVars bElse)
    | FlatImp.SLoop body1 cond body2 =>
        union (modVars body1) (modVars body2)
    | FlatImp.SSeq s1 s2 =>
        union (modVars s1) (modVars s2)
    | FlatImp.SSkip => empty_set
    end.

  Lemma invert_eval_SLoop: forall fuel st1 body1 cond body2 st4,
    FlatImp.eval_stmt (S fuel) st1 (FlatImp.SLoop body1 cond body2) = Success st4 ->
    FlatImp.eval_stmt fuel st1 body1 = Success st4 /\ get st4 cond = Some $0 \/
    exists st2 st3 cv, FlatImp.eval_stmt fuel st1 body1 = Success st2 /\
                       get st2 cond = Some cv /\ cv <> $0 /\
                       FlatImp.eval_stmt fuel st2 body2 = Success st3 /\
                       FlatImp.eval_stmt fuel st3 (FlatImp.SLoop body1 cond body2) = Success st4.
  Proof.
    introv Ev. simpl in Ev. unfold option2res in *.
    repeat (destruct_one_match_hyp; try discriminate); inversionss; eauto 10.
  Qed.

  Lemma invert_eval_SSeq: forall fuel initial s1 s2 final,
    FlatImp.eval_stmt (S fuel) initial (FlatImp.SSeq s1 s2) = Success final ->
    exists mid, FlatImp.eval_stmt fuel initial s1 = Success mid /\
                FlatImp.eval_stmt fuel mid s2 = Success final.
  Proof.
    introv Ev. simpl in Ev. destruct_one_match_hyp; try discriminate. eauto.
  Qed.

  Lemma modVarsSound: forall fuel s initial final,
    FlatImp.eval_stmt fuel initial s = Success final ->
    only_differ initial (modVars s) final.
  Proof.
    induction fuel; introv Ev.
    - discriminate.
    - destruct s.
      + simpl in *. inversionss. apply only_differ_one.
      + simpl in Ev. unfold option2res in *.
        repeat (destruct_one_match_hyp_of_type (option (word w)); try discriminate).
        inversionss. apply only_differ_one.
      + simpl in Ev. unfold option2res in *.
        repeat (destruct_one_match_hyp_of_type (option (word w)); try discriminate).
        inversionss. apply only_differ_one.
      + Opaque union. simpl in *. unfold option2res in *.
        repeat (destruct_one_match_hyp_of_type (option (word w)); try discriminate).
        destruct fuel; [ inversion Ev | ].
        destruct_one_match_hyp.
        * apply only_differ_union_r. eapply IHfuel. eassumption.
        * apply only_differ_union_l. eapply IHfuel. eassumption.
      + apply invert_eval_SLoop in Ev. destruct Ev as [Ev | Ev]. 
        * destruct Ev as [Ev C]. 
          simpl.
          apply only_differ_union_l. apply IHfuel. assumption.
        * destruct Ev as [mid2 [mid3 [cv [Ev1 [C1 [C2 [Ev2 Ev3]]]]]]].
          eapply only_differ_trans.
          { simpl. apply only_differ_union_l.
            apply IHfuel. eassumption. }
          { eapply only_differ_trans.
            { simpl. apply only_differ_union_r.
              apply IHfuel. eassumption. }
            { apply IHfuel. assumption. } }
      + apply invert_eval_SSeq in Ev.
        destruct Ev as [mid [Ev1 Ev2]]. simpl.
        eapply only_differ_trans.
        * apply only_differ_union_l. eapply IHfuel. eassumption.
        * apply only_differ_union_r. eapply IHfuel. eassumption.
      + simpl. inversionss. apply only_differ_refl.
  Qed.

  Definition vars_range(x1 x2: var): vars := fun x => x1 <= x < x2.

(*
  Lemma range_union_one_r: forall x1 x2 x3,
    x1 <= x2 < x3 ->
    range_union (x1, x3) (range_one x2) = (x1, x3).
  Proof.
    intros. unfold range_union, range_one.
    repeat match goal with
    | [ |- context[if ?e then _ else _] ] => let E := fresh "E" in destruct e eqn: E
    end; f_equal; try omega.
    - pose proof (Min.min_spec x1 x2). omega.
    - pose proof (Max.max_spec x3 (S x2)). omega.
  Qed.
*)

  Transparent union.

  Lemma range_union_inc_r: forall x1 x2,
    x1 <= x2 ->
    union (vars_range x1 x2) (vars_one x2) = vars_range x1 (S x2).
  Proof.
    intros. unfold union, vars_one, vars_range.
    extensionality x. apply prop_ext; change var with nat in *; simpl; omega.
  Qed.

  Lemma range_union_adj: forall x1 x2 x3,
    x1 <= x2 <= x3 ->
    union (vars_range x1 x2) (vars_range x2 x3) = (vars_range x1 x3).
  Proof.
    unfold union, vars_range. intros.
    extensionality x. apply prop_ext; change var with nat in *; simpl; omega.
  Qed.

  Lemma vars_one_range: forall x,
    vars_one x = vars_range x (S x).
  Proof.
    intros. cbv. extensionality y. apply prop_ext. omega.
  Qed.

  Lemma flattenExpr_modVars_spec: forall e s firstFree resVar,
    flattenExpr firstFree e = (s, resVar) ->
    modVars s = vars_range firstFree (S resVar) /\ firstFree <= resVar.
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
    split; [|omega].
    rewrite range_union_inc_r by omega.
    apply range_union_adj. omega.
  Qed.

  Lemma flattenStmt_vars_range: forall s s' firstFree newFirstFree,
    flattenStmt firstFree s = (s', newFirstFree) ->
    firstFree <= newFirstFree.
  Proof.
    induction s; introv E; inversions E;
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
    fuel1 <= fuel2 ->
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
      + apply invert_eval_SLoop in Ev.
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
     + apply invert_eval_SSeq in Ev.
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

  Lemma flattenExpr_correct_aux: forall e firstFree resVar s initialH initialL res,
    flattenExpr firstFree e = (s, resVar) ->
    extends initialL initialH ->
    undef initialH (vars_range firstFree (S resVar)) ->
    ExprImp.eval_expr initialH e = Some res ->
    exists fuel finalL,
      FlatImp.eval_stmt fuel initialL s = Success finalL /\
      get finalL resVar = Some res /\
      only_differ initialL (vars_range firstFree (S resVar)) finalL.
  Proof.
    induction e; introv F Ex U Ev.
    - inversionss.
      exists 1 (put initialL resVar res). repeat split.
      + apply get_put_same.
      + rewrite <- vars_one_range. apply only_differ_one.
    - inversionss.
      exists 1 (put initialL resVar res). repeat split.
      + simpl. unfold extends in Ex. apply Ex in H0. rewrite H0. reflexivity.
      + rewrite get_put_same. symmetry. assumption.
      + rewrite <- vars_one_range. apply only_differ_one.
    - inversionss. repeat (destruct_one_match_hyp; try discriminate). inversionss.
      specialize (IHe1 _ _ _ _ _ w0 E Ex).
      specializes IHe1. {
        eapply undef_shrink; [eassumption|].
        repeat match goal with
        | H : _  |- _ => apply flattenExpr_modVars_spec in H
        end.
        eapply vars_range_subset; omega.
      }
      assumption.
      destruct IHe1 as [fuel1 [midL [Ev1 [G1 D1]]]].
      specialize (IHe2 _ _ _ initialH midL w1 E0).
      specializes IHe2.
      { refine (extends_if_only_differ_in_undef _ _ _ _ Ex _ D1).
        eapply undef_shrink; try eassumption.
        apply flattenExpr_modVars_spec in E.
        apply flattenExpr_modVars_spec in E0.
        apply vars_range_subset; omega. }
      { eapply undef_shrink; [eassumption|].
        apply flattenExpr_modVars_spec in E.
        apply flattenExpr_modVars_spec in E0.
        apply vars_range_subset; omega. }
      { assumption. }
      destruct IHe2 as [fuel2 [preFinalL [Ev2 [G2 D2]]]].
      remember (S (S (fuel1 + fuel2))) as f0.
      remember (S (fuel1 + fuel2)) as f.
      exists (S f0) (put preFinalL (S v0) (Op.eval_binop op w0 w1)).
      repeat split.
      + simpl. erewrite increase_fuel_still_Success; [| |eassumption]; [|omega].
        apply increase_fuel_still_Success with (fuel1 := f0); [omega|].
        subst f0. simpl.
        erewrite (increase_fuel_still_Success _ _ midL); [| |eassumption]; [|omega].
        subst f. simpl.
        assert (get preFinalL v = Some w0) as G1'. {
          eapply only_differ_get_unchanged; try eassumption.
          cbv. omega.
        }
        rewrite G1'. simpl. rewrite G2. simpl. reflexivity.
      + apply get_put_same.
      + rename s1 into stat1. apply only_differ_trans with (s2 := midL).
        * eapply only_differ_subset; [|eassumption].
          repeat match goal with
          | H : _  |- _ => apply flattenExpr_modVars_spec in H
          end.
          eapply vars_range_subset; omega.
        * eapply only_differ_trans with (s2 := preFinalL).
          { eapply only_differ_subset; [|eassumption].
            repeat match goal with
            | H : _  |- _ => apply flattenExpr_modVars_spec in H
            end.
            eapply vars_range_subset; omega.
          }
          { apply only_differ_put. unfold vars_range.
            repeat match goal with
            | H : _  |- _ => apply flattenExpr_modVars_spec in H
            end.
            cbv. omega.
          }
  Qed.

  Lemma flattenStmt_correct_aux:
    forall fuelH sH sL firstFree newFirstFree initialH finalH initialL dH,
    flattenStmt firstFree sH = (sL, newFirstFree) ->
    extends initialL initialH ->
    undef initialH (vars_range firstFree newFirstFree) ->
    ExprImp.eval_stmt fuelH initialH sH = Some finalH ->
    only_differ initialH dH finalH ->
    exists fuelL finalL,
      FlatImp.eval_stmt fuelL initialL sL = Success finalL /\
      extends finalL finalH /\
      only_differ initialL (union dH (vars_range firstFree newFirstFree)) finalL.
  Proof.
    induction fuelH; introv F Ex U Ev DH; [solve [inversionss] |].
    destruct sH.
    - apply ExprImp.invert_eval_SSet in Ev.
      destruct Ev as [v [Ev Eq]].
      inversions F. destruct_one_match_hyp. destruct_pair_eqs. subst.
      pose proof (flattenExpr_correct_aux _ _ _ _ _ _ _ E Ex U Ev) as P.
      destruct P as [fuelL [prefinalL [Evs [G D]]]].
      remember (S fuelL) as SfuelL.
      exists (S SfuelL). eexists. repeat split.
      + simpl.
        assert (FlatImp.eval_stmt SfuelL initialL s = Success prefinalL) as Evs'. {
          eapply increase_fuel_still_Success; [|eassumption]. omega.
        }
        rewrite Evs'. subst SfuelL. simpl. rewrite G. simpl. reflexivity.
      + apply extends_put_same.
        eapply extends_if_only_differ_in_undef; eassumption.
      + (* we might need modVars for ExprImp, because DH not strong enough? TODO *) admit.
    - inversions F. repeat destruct_one_match_hyp. destruct_pair_eqs. subst.
      apply ExprImp.invert_eval_SIf in Ev.
      destruct Ev as [cv [Evc Ev]].
      pose_flatten_var_ineqs.
      pose proof (flattenExpr_correct_aux _ _ _ _ _ _ cv E Ex) as P.
      specializes P; [|eassumption|]. {
        eapply undef_shrink; [eassumption|]. apply vars_range_subset; omega.
      }
      destruct P as [fuelLcond [initial2L [Evcond [G D]]]].
      destruct Ev as [[Ne EvThen] | [Eq EvElse]].
      + specializes IHfuelH.
        1: eapply E0.
        3: eapply EvThen.
        1: eapply Ex.
        2: eapply DH.
        { eapply undef_shrink; [eassumption|]. apply vars_range_subset; omega. }
        destruct IHfuelH as [fuelL [finalL [Evbranch [Ex2 D2]]]].
        exists (S (fuelLcond + (S fuelL))). eexists.
        repeat split.
        * simpl.
          pose proof increase_fuel_still_Success as P.
          assert (fuelLcond <= fuelLcond + (S fuelL)) as IE by omega.
          specializes P. { eapply IE. } { eapply Evcond. }
          rewrite P. clear IE P.
          pose proof increase_fuel_still_Success as P.
          assert (S fuelL <= fuelLcond + (S fuelL)) as IE by omega.
          eapply (P _ _ _ _ _ IE). clear IE P.
          simpl. rewrite G. simpl. destruct_one_match; [contradiction|].
          admit. (* TODO change initialL in Evbranch to initial2L *)
        * admit. (* TODO extends *)
        * admit. (* TODO only_differ *)
      +

  Abort.

End FlattenExpr.
