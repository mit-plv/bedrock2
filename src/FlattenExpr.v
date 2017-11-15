Require Import lib.LibTactics.
Require Import compiler.Common.
Require Import compiler.ResMonad.
Require compiler.ExprImp.
Require compiler.FlatImp.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import compiler.Axioms.
Require Import compiler.StateCalculus.

(* TODO automate such that we don't to Require this, and not always specify which lemma to use *)
Require compiler.StateCalculusTacticTest.

Open Scope Z.

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

  Definition vars_range(x1 x2: var): vars := fun x => x1 <= x < x2.

  Lemma in_vars_range: forall x lo hi, x \in vars_range lo hi <-> lo <= x /\ x < hi.
  Proof. intros. unfold vars_range, contains, Function_Set. omega. Qed.

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

  Lemma set_extensionality: forall (T: Type) s1 s2,
    (forall (x: T), x \in s1 <-> x \in s2) -> s1 = s2.
  Proof.
    intros. extensionality x. apply prop_ext. apply H.
  Qed.

  Lemma vars_one_range: forall x,
    FlatImp.vars_one x = vars_range x (S x).
  Proof.
    intros. apply set_extensionality. intro y.
    rewrite in_vars_range. unfold FlatImp.vars_one.
    rewrite (@singleton_set_spec var). (* TODO why doesn't it work if I don't give var ?? *)
    unfold var in *. unfold S. omega.
  Qed.

  Lemma range_union_inc_r: forall x1 x2,
    x1 <= x2 ->
    union (vars_range x1 x2) (FlatImp.vars_one x2) = vars_range x1 (S x2).
  Proof.
    intros. rewrite vars_one_range in *.
    apply set_extensionality. intro.
    rewrite (@union_spec var). (* TODO implicit args stuff *)
    rewrite? in_vars_range. unfold S. omega.
  Qed.

  Lemma range_union_adj: forall x1 x2 x3,
    x1 <= x2 <= x3 ->
    union (vars_range x1 x2) (vars_range x2 x3) = (vars_range x1 x3).
  Proof.
    intros.
    apply set_extensionality. intro.
    rewrite (@union_spec var). (* TODO implicit args stuff *)
    rewrite? in_vars_range. unfold S. omega.
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
      exists 1%nat (put initialL resVar res). rewrite <- vars_one_range in *.
      unfold FlatImp.vars_one in *.
      repeat split; state_calc.
    - inversionss.
      exists 1%nat (put initialL resVar res). repeat split.
      + simpl. unfold extends in Ex. apply Ex in H0. rewrite H0. reflexivity.
      + rewrite get_put_same. symmetry. assumption.
      + rewrite <- vars_one_range. state_calc.
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
      destruct IHe1 as [fuel1 [midL [Ev1 [G1 D1]]]].
      specialize (IHe2 _ _ _ initialH midL w1 E0).
      specializes IHe2.
      { apply flattenExpr_modVars_spec in E.
        apply flattenExpr_modVars_spec in E0.
        assert (subset (vars_range firstFree (S v)) (vars_range firstFree (S (S v0)))). {
          eapply vars_range_subset; myomega.
        }
        (* TODO make this work without this hint *)
        refine (compiler.StateCalculusTacticTest.extends_if_only_differ_in_undef _ _ _ _ Ex _ D1).
        state_calc. }
      { apply flattenExpr_modVars_spec in E.
        apply flattenExpr_modVars_spec in E0.
        assert (subset (vars_range (S v) (S v0)) (vars_range firstFree (S (S v0)))). {
          eapply vars_range_subset; myomega.
        }
        state_calc.
        (* TODO make this work without the assert hint *) }
      { assumption. }
      destruct IHe2 as [fuel2 [preFinalL [Ev2 [G2 D2]]]].
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
          eapply compiler.StateCalculusTacticTest.only_differ_get_unchanged; try eassumption.
          rewrite in_vars_range. myomega.
        }
        rewrite G1'. simpl. rewrite G2. simpl. reflexivity.
      + apply get_put_same.

(*
      + unfold only_differ, undef, extends in *. intros. specialize (D2 x).
        rewrite in_vars_range in *.
  *)    
      
      (*
      + rename s1 into stat1.
        progress repeat match goal with
        | H : _  |- _ => unique pose proof (proj2 (flattenExpr_modVars_spec _ _ _ _ H))
        end.
        repeat match goal with
        | H: ?T |- _ => match T with
          | extends _ _ => fail 1
          | only_differ _ _ _ => fail 1
          | undef _ _ => fail 1
          | subset _ _ => fail 1
          | @eq nat _ _ => fail 1
          | _ <= _ => fail 1
          | _ => clear H; idtac "cleared" H
          end
        end.
        subst. (* also gets rid of unnecessary variables *)
        repeat match goal with
        | x: ?T |- _ => match type of T with
          | Prop => fail 1
          | _ => clear x; idtac "cleared" x
          end
        end.
  unf; intros; autorewrite with rewrite_set_op_specs in *; rewrite_get_put.
  repeat match goal with
  | x: ?T, H: forall (y: ?T), _ |- _ =>
      match T with
      | var => idtac
      | word _ => idtac
      | nat => idtac (* <-- this also takes w, which it shouldn't, but we keep getting vars as
             nats, e.g. look at the implicit argument of only_differ *)
      end;
      tryif (unify w x) (* TODO how to generalize? *)
      then fail
      else (unique pose proof (H x))
  end.

Inductive marker{T: Type}: T -> Prop :=
| mark: forall (n: T), marker n.

repeat match goal with 
| |- context [vars_range ?lo ?hi] => 
     first [unique pose proof (mark lo) | unique pose proof (mark hi)]
| _: context [vars_range ?lo ?hi] |- _ => 
     first [unique pose proof (mark lo) | unique pose proof (mark hi)]
end.

Inductive marker'{T: Type}: T -> Prop :=
| mark': forall (n: T), marker' n.

repeat match goal with
| _: marker ?v1, _: marker ?v2, y: ?T |- _ =>
   match T with
      | var => idtac
      | nat => idtac
   end;
   tryif (unify w y) (* TODO how to generalize? *)
   then fail
   else unique pose proof (mark' (y, v1, v2))
end.

match goal with
| M: marker' (?y, ?v1, ?v2) |- _ =>
    clear M;
    assert (y \in vars_range v1 v2)
end.

            repeat match goal with
            | H: context C[ ?x \in vars_range ?lo1 ?hi1 ] |- _ => nofail (
                let r := eval cbv in (x \in vars_range lo1 hi1) in
                let T := context C[r] in
                change T in H
              )
            end.
            cbv. Timeout 30 omega. (* <-- takes forever, even though goal is clearly contradictory *)


Time match goal with
| _: marker ?v1, _: marker ?v2, y: ?T |- _ =>
   match T with
      | var => idtac
      | nat => idtac
   end;
   match goal with
   | _: y \in vars_range v1 v2 |- _ => fail 1
   | _ => tryif (unify w y) (* TODO how to generalize? *)
      then fail
      else
      (idtac y v1 v2; assert (y \in vars_range v1 v2) by (
            repeat match goal with
            | H: context C[ ?x \in vars_range ?lo1 ?hi1 ] |- _ => nofail (
                let r := eval cbv in (x \in vars_range lo1 hi1) in
                let T := context C[r] in
                change T in H
              )
            end;
            cbv; omega))
   end
end. (* runs out of memory, why? and there's not even an outermost repeat *)

cbv.

let H := fresh "R" in assert (y \in vars_range v1 v2) as R

(* don't do subset, but do "x in vars_range" 
repeat match goal with
| _: marker ?v1, _: marker ?v2, _: marker ?v3, _: marker ?v4 |- _ => match goal with
  | _: sub *)

(* pose proof (mark 3). *)

  repeat match goal with
  | H: context C[ ?x \in vars_range ?lo ?hi ] |- _ => nofail (
      let r := eval cbv in (x \in vars_range lo hi) in
      let T := context C[r] in
      change T in H
    )
  | |- context C[ ?x \in vars_range ?lo ?hi ] => nofail (
      let r := eval cbv in (x \in vars_range lo hi) in
      let T := context C[r] in
      change T
    )
  end.
  Time repeat (intuition (auto || congruence || omega) || destruct_one_dec_eq).
*)
      + rename s1 into stat1.
        progress repeat match goal with
        | H : _  |- _ => unique pose proof (proj2 (flattenExpr_modVars_spec _ _ _ _ H))
        end.
        repeat match goal with
        | H: ?T |- _ => match T with
          | extends _ _ => fail 1
          | only_differ _ _ _ => fail 1
          | undef _ _ => fail 1
          | subset _ _ => fail 1
          | @eq nat _ _ => fail 1
          | _ <= _ => fail 1
          | _ => clear H; idtac "cleared" H
          end
        end.
        subst. (* also gets rid of unnecessary variables *)
        repeat match goal with
        | x: ?T |- _ => match type of T with
          | Prop => fail 1
          | _ => clear x; idtac "cleared" x
          end
        end.

  unf; intros; autorewrite with rewrite_set_op_specs in *; rewrite_get_put.
  repeat match goal with
  | x: ?T, H: forall (y: ?T), _ |- _ =>
      match T with
      | var => idtac
      | word _ => idtac
      | Z => idtac 
      end;
      (unique pose proof (H x))
  end.

  rewrite in_vars_range in *.

  unfold var, S in *.
Reset Ltac Profile.
Set Ltac Profiling.

  Time repeat (intuition (auto || congruence || omega) || destruct_one_dec_eq). 
  (* 58.919 secs, whereas omega on nat took 94.889 secs *)

Show Ltac Profile. 


(*
  Require Import Coq.micromega.Lia.

  unfold var, S in *.
Reset Ltac Profile.
Set Ltac Profiling.

  Time repeat (intuition (auto || congruence || lia) || destruct_one_dec_eq). 
  (* 42.325 secs, whereas lia on nat took 98.796 secs *)

Show Ltac Profile. 
(* lia takes only 28.3% of the time, while it took 72.3% of the time with nats
    zify still takes time, but only 21% instead of 71% *)
*)
  
  
  
  
(*
Ltac myIntuition :=
  solve [ repeat (intuition (auto || congruence || omega) || destruct_one_dec_eq) ]. 



Ltac specialize2 n := 
  lazymatch n with
  | O => myIntuition
  | S ?m => match goal with
    | x: ?T, H: forall (y: ?T), _ |- _ =>
        match T with
        | var => idtac
        | word _ => idtac
        | nat => idtac (* <-- this also takes w, which it shouldn't, but we keep getting vars as
               nats, e.g. look at the implicit argument of only_differ *)
        end;
  (*      tryif (unify w x) (* TODO how to generalize? *)
        then fail
        else*) (unique pose proof (H x));
        
       specialize2 m
    end
  end.
  
  Time (specialize2 4).




Reset Ltac Profile.
Set Ltac Profiling.


  repeat match goal with
  | H: context C[ ?x \in vars_range ?lo ?hi ] |- _ => nofail (
      let r := eval cbv in (x \in vars_range lo hi) in
      let T := context C[r] in
      change T in H
    )
  | |- context C[ ?x \in vars_range ?lo ?hi ] => nofail (
      let r := eval cbv in (x \in vars_range lo hi) in
      let T := context C[r] in
      change T
    )
  end.
  Time repeat (intuition (auto || congruence || omega) || destruct_one_dec_eq). (* 94.889 secs *)

Show Ltac Profile. (* omega takes 71.1% of the time *)
*)

Time Qed. (* 13.865 secs *)


(* These commands take 73s and 23s, respectively. That's too much!
   With the more manual proof, it takes less than noticeable time.
   Replacing omega by (abstract omega) increases both time measurements.

  (* we're confusing "w: nat" (word width) with vars with fuel, so we're specializing too many
    hyps, and later, vars will be generalized to any location, so we won't have a total order
    any more, so make var type opaque *)
(*
      + rename s1 into stat1.
        progress repeat match goal with
        | H : _  |- _ => unique pose proof (proj2 (flattenExpr_modVars_spec _ _ _ _ H))
        end.
        repeat match goal with
        | H: ?T |- _ => match T with
          | extends _ _ => fail 1
          | only_differ _ _ _ => fail 1
          | undef _ _ => fail 1
          | subset _ _ => fail 1
          | @eq nat _ _ => fail 1
          | _ <= _ => fail 1
          | _ => clear H; idtac "cleared" H
          end
        end.
        (* TODO make state_calc work on this whole thing *)
        apply compiler.StateCalculusTacticTest.only_differ_trans with (s2 := midL).
        * assert (subset (vars_range firstFree (S v)) (vars_range firstFree (S (S v0)))). {
            eapply vars_range_subset; omega.
          }
          eapply compiler.StateCalculusTacticTest.only_differ_subset; eassumption.
          (* TODO make state_calc efficient on this one *)
        * eapply compiler.StateCalculusTacticTest.only_differ_trans with (s2 := preFinalL).
          { eapply compiler.StateCalculusTacticTest.only_differ_subset; [|eassumption].
            eapply vars_range_subset; omega.
          }
          { apply compiler.StateCalculusTacticTest.only_differ_put. unfold vars_range.
            cbv. omega.
          }
*)

      + rename s1 into stat1.
        progress repeat match goal with
        | H : _  |- _ => unique pose proof (proj2 (flattenExpr_modVars_spec _ _ _ _ H))
        end.
        (* TODO make state_calc work on this whole thing *)
        apply compiler.StateCalculusTacticTest.only_differ_trans with (s2 := midL).
        * assert (subset (vars_range firstFree (S v)) (vars_range firstFree (S (S v0)))). {
            eapply vars_range_subset; omega.
          }
          eapply compiler.StateCalculusTacticTest.only_differ_subset; eassumption.
          (* TODO make state_calc efficient on this one *)
        * eapply compiler.StateCalculusTacticTest.only_differ_trans with (s2 := preFinalL).
          { eapply compiler.StateCalculusTacticTest.only_differ_subset; [|eassumption].
            eapply vars_range_subset; omega.
          }
          { apply compiler.StateCalculusTacticTest.only_differ_put. unfold vars_range.
            cbv. omega.
          }
  Qed.
*)

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
      destruct P as [fuelL [prefinalL [Evs [G D]]]].
      remember (Datatypes.S fuelL) as SfuelL.
      exists (Datatypes.S SfuelL). eexists. repeat split.
      + simpl.
        assert (FlatImp.eval_stmt SfuelL initialL s = Success prefinalL) as Evs'. {
          eapply increase_fuel_still_Success; [|eassumption]. omega.
        }
        rewrite Evs'. subst SfuelL. simpl. rewrite G. simpl. reflexivity.
      + clear IHfuelH. apply compiler.StateCalculusTacticTest.extends_put_same.
        eapply compiler.StateCalculusTacticTest.extends_if_only_differ_in_undef; eassumption.
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
      destruct P as [fuelLcond [initial2L [Evcond [G D]]]].
      destruct Ev as [[Ne EvThen] | [Eq EvElse]].
      + specialize (IHfuelH sH1 sL1 (S v) v0 initialH finalH initial2L E0).
        specializes IHfuelH.
        * (* TODO this should be state_calc *)
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
        * (* TODO this should be state_calc *)
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
