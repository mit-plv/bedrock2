Require Import lib.LibTactics.
Require Import compiler.Common.
Require Import compiler.ResMonad.
Require compiler.ExprImp.
Require compiler.FlatImp.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import compiler.Axioms.

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

  Definition extends(s1 s2: state) := forall x v, get s2 x = Some v -> get s1 x = Some v.

  Lemma put_extends: forall s x v,
    extends (put s x v) s.
  Proof. unfold extends. intros. Abort.

  (* models a set of vars *)
  Definition vars := var -> Prop.

  Definition vars_empty: vars := fun _ => False.

  Definition vars_one(x: var): vars := fun y => x = y.

  Definition vars_union(vs1 vs2: vars): vars := fun x => vs1 x \/ vs2 x.

  Definition vars_add(vs: vars)(new: var): vars := vars_union vs (vars_one new).

  (* returns the set of modified vars *)
  Fixpoint modVars(s: @FlatImp.stmt w): vars :=
    match s with
    | FlatImp.SLit x v => vars_one x
    | FlatImp.SOp x op y z => vars_one x
    | FlatImp.SSet x y => vars_one x
    | FlatImp.SIf cond bThen bElse =>
        vars_union (modVars bThen) (modVars bElse)
    | FlatImp.SLoop body1 cond body2 =>
        vars_union (modVars body1) (modVars body2)
    | FlatImp.SSeq s1 s2 =>
        vars_union (modVars s1) (modVars s2)
    | FlatImp.SSkip => vars_empty
    end.

  Definition only_differ(s1: state)(vs: vars)(s2: state) :=
    forall x, vs x \/ get s1 x = get s2 x.

Ltac destruct_one_match_hyp_test type_test :=
  match goal with
  | H: context[match ?e with _ => _ end] |- _ =>
      is_var e;
      let T := type of e in type_test T;
      destruct e
  | H: context[if ?e then _ else _] |- _ =>
      is_var e;
      let T := type of e in type_test T;
      destruct e
  | H: context[match ?e with _ => _ end] |- _ =>
      let T := type of e in type_test T;
      let E := fresh "E" in destruct e eqn: E
  | H: context[if ?e then _ else _] |- _ =>
      let T := type of e in type_test T;
      let E := fresh "E" in destruct e eqn: E
  end.

Ltac destruct_one_match_hyp_of_type T :=
  destruct_one_match_hyp_test ltac:(fun t => unify t T).

Ltac destruct_one_match_hyp :=
  destruct_one_match_hyp_test ltac:(fun t => idtac).

Ltac inversionss :=
  repeat match goal with
  | H: ?a = ?b |- _ => inversion H; subst; clear H;
                       match goal with
                       | H': a = b |- _ => fail 1
                       | _ => idtac
                       end
  end.

  Lemma only_differ_union_l: forall s1 s2 r1 r2,
    only_differ s1 r1 s2 ->
    only_differ s1 (vars_union r1 r2) s2.
  Proof. firstorder. Qed.

  Lemma only_differ_union_r: forall s1 s2 r1 r2,
    only_differ s1 r2 s2 ->
    only_differ s1 (vars_union r1 r2) s2.
  Proof. firstorder. Qed.

  Lemma only_differ_one: forall s x v,
    only_differ s (vars_one x) (put s x v).
  Proof.
    cbv [only_differ vars_one]. intros. destruct (dec (x = x0)); [ auto | ].
    right. symmetry. apply get_put_diff. assumption.
  Qed.

  Lemma only_differ_refl: forall s1 r,
    only_differ s1 r s1.
  Proof. firstorder. Qed.

  Lemma only_differ_sym: forall s1 s2 r,
    only_differ s1 r s2 ->
    only_differ s2 r s1.
  Proof. firstorder. Qed.

  Lemma only_differ_trans: forall s1 s2 s3 r,
    only_differ s1 r s2 ->
    only_differ s2 r s3 ->
    only_differ s1 r s3.
  Proof.
    unfold only_differ. introv E1 E2. intro x.
    specialize (E1 x). specialize (E2 x).
    destruct E1; [auto|]. destruct E2; [auto|]. right. congruence.
  Qed.

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
      + simpl in *. unfold option2res in *.
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

  Lemma range_union_inc_r: forall x1 x2,
    x1 <= x2 ->
    vars_union (vars_range x1 x2) (vars_one x2) = vars_range x1 (S x2).
  Proof.
    intros. unfold vars_union, vars_one, vars_range.
    extensionality x. apply prop_ext; change var with nat in *; omega.
  Qed.

  Lemma range_union_adj: forall x1 x2 x3,
    x1 <= x2 <= x3 ->
    vars_union (vars_range x1 x2) (vars_range x2 x3) = (vars_range x1 x3).
  Proof.
    unfold vars_union, vars_range. intros.
    extensionality x. apply prop_ext; change var with nat in *; omega.
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

  Definition undef(s: state)(vs: vars) := forall x, vs x -> get s x = None.

  Definition subset(vs1 vs2: vars) := forall x, vs1 x -> vs2 x.

  Definition vars_range_subset: forall lo1 hi1 lo2 hi2,
    lo1 >= lo2 ->
    hi1 <= hi2 ->
    subset (vars_range lo1 hi1) (vars_range lo2 hi2).
  Proof.
    unfold subset, vars_range. intros. omega.
  Qed.

  Lemma undef_shrink: forall st vs1 vs2,
    undef st vs1 ->
    subset vs2 vs1 ->
    undef st vs2.
  Proof. unfold undef, subset. firstorder. Qed.

  Lemma only_differ_subset: forall s1 s2 r1 r2,
    subset r1 r2 ->
    only_differ s1 r1 s2 ->
    only_differ s1 r2 s2.
  Proof.
    unfold subset, only_differ. intros. firstorder.
  Qed.

  Lemma extends_if_only_differ_in_undef: forall s1 s2 s vs,
    extends s1 s ->
    undef s vs ->
    only_differ s1 vs s2 ->
    extends s2 s.
  Proof.
    unfold extends, undef, only_differ.
    introv E U O G.
    specialize (O x). destruct O as [O | O].
    - specialize (U _ O). congruence. (* contradiction *)
    - rewrite <- O. apply E. assumption.
  Qed.

  Lemma only_differ_get_unchanged: forall s1 s2 x v d,
    get s1 x = v ->
    only_differ s1 d s2 ->
    ~ d x ->
    get s2 x = v.
  Proof.
    introv G D N.
    unfold only_differ in D. destruct (D x); congruence.
  Qed.

  Lemma only_differ_put: forall s (d: vars) x v,
    d x ->
    only_differ s d (put s x v).
  Proof.
    unfold only_differ. intros.
    destruct (dec (x = x0)).
    - subst x0. left. assumption.
    - right. rewrite get_put_diff; auto.
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
          unfold vars_range. omega.
        }
        rewrite G1'. simpl. rewrite G2. simpl. reflexivity.
      + apply get_put_same.
      + apply only_differ_trans with (s2 := midL).
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
            omega.
          }
  Qed.

End FlattenExpr.


