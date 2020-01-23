Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.MetricLogging.
Require Import compiler.FlattenExprDef.
Require Import compiler.FlattenExpr.
Require Import compiler.NameGen.
Require Import compiler.Simulation.
Require Import compiler.Simp.


Section Sim.

  Context {p: FlattenExpr.parameters}.

  Definition related_without_functions(done: bool): ExprImp.SimState -> FlatImp.SimState -> Prop :=
    fun '(e1, c1, t1, m1, l1, mc1) '(e2, c2, t2, m2, l2, mc2) =>
      e1 = map.empty /\ e2 = map.empty (* TODO allow non-empty function environments *) /\
      ExprImp2FlatImp0 c1 = c2 /\
      t1 = t2 /\
      m1 = m2 /\
      map.extends l2 l1 /\
      map.undef_on l1 (allFreshVars (freshNameGenState (ExprImp.allVars_cmd_as_list c1))).

  Definition related(max_size: BinInt.Z)(done: bool): ExprImp.SimState -> FlatImp.SimState -> Prop :=
    fun '(e1, c1, t1, m1, l1, mc1) '(e2, c2, t2, m2, l2, mc2) =>
      flatten_functions max_size e1 = Some e2 /\
      ExprImp2FlatImp max_size c1 = Some c2 /\
      t1 = t2 /\
      m1 = m2 /\
      (* TODO flattenExpr has to unset all vars at the end of the compiled stmt *)
      l1 = l2 /\
      (* map.extends l2 l1 /\ *)
      map.undef_on l1 (allFreshVars (freshNameGenState (ExprImp.allVars_cmd_as_list c1))).

  Axiom TODO_sam: False.

  Lemma flatten_functions_empty{hyps: FlattenExpr.assumptions p}:
    forall max_size, flatten_functions max_size map.empty = Some map.empty.
  Proof.
    intros.
    unfold flatten_functions, Properties.map.map_all_values.
    match goal with
    | |- _ _ _ ?E = _ => remember E as m
    end.
    revert Heqm.
    unshelve eapply map.fold_spec. 2: reflexivity. 1: eapply Semantics.funname_env_ok.
    intros. exfalso. eapply (f_equal (fun m => map.get m k)) in Heqm.
    unshelve erewrite map.get_put_same in Heqm. 1: eapply Semantics.funname_env_ok.
    unshelve erewrite map.get_empty in Heqm. 1: eapply Semantics.funname_env_ok.
    discriminate.
  Qed.

  Lemma relate_related{hyps: FlattenExpr.assumptions p}(max_size: BinInt.Z): forall done s1 s2,
      related_without_functions done s1 s2 <-> related max_size done s1 s2.
  Proof.
    intros done (((((e1 & c1) & t1) & m1) & l1) & mc1) (((((e2 & c2) & t2) & m2) & l2) & mc2).
    split; intro H; unfold related_without_functions, related in *.
    - intuition idtac.
      + subst. apply flatten_functions_empty.
      + unfold ExprImp2FlatImp. rewrite H1. case TODO_sam. (* doesn't hold (size check) *)
      + case TODO_sam. (* clearly doesn't hold, extends does not imply equality *)
    - simp. case TODO_sam. (* clearly doesn't hold *)
  Qed.

  Lemma flattenExprSim_without_functions{hyps: FlattenExpr.assumptions p}:
    simulation ExprImp.SimExec FlatImp.SimExec related_without_functions.
  Proof.
    unfold simulation, related_without_functions, ExprImp.SimExec, FlatImp.SimExec.
    intros (((((e1 & c1) & done1) & t1) & m1) & l1) (((((e2 & c2) & done2) & t2) & m2) & l2).
    intros.
    simp.
    unfold ExprImp2FlatImp0.
    match goal with
    | |- context [ fst ?x ] => destruct x as [s ngs] eqn: E
    end.
    simpl.
    assert (PropSet.disjoint (ExprImp.allVars_cmd c1)
                             (allFreshVars (freshNameGenState (ExprImp.allVars_cmd_as_list c1))))
      as D by eapply freshNameGenState_disjoint.
    eapply FlatImp.exec.weaken.
    - eapply @flattenStmt_correct_aux with (eH := map.empty) (max_size := BinNums.Z0).
      + typeclasses eauto.
      + eapply flatten_functions_empty.
      + eassumption.
      + reflexivity.
      + exact E.
      + assumption.
      + assumption.
      + exact D.
    - simpl. intros. simp.
      eexists. split; [|eassumption]. simpl. rewrite E. simpl.
      repeat (split; [solve [auto]|]).
      pose proof (ExprImp.modVars_subset_allVars c1).
      simpl in *. (* PARAMRECORDS *)
      Solver.map_solver FlattenExpr.locals_ok.
  Qed.

  Lemma flattenExprSim{hyps: FlattenExpr.assumptions p}(max_size: BinInt.Z):
    simulation ExprImp.SimExec FlatImp.SimExec (related max_size).
  Proof.
    pose proof flattenExprSim_without_functions as P.
    unfold simulation in *.
    pose proof relate_related as Q.
    intros.
    case TODO_sam.
  Qed.

(*
The postcondition of flattenStmt_correct says

  (mcL' - mc <= mcH' - mc)%metricsH

Assuming metrics subtraction and less-than behave as expected, we can add mc on both sides
of the equation and get

  (mcL' <= mcH')%metricsH

That's an interesting simplification which suggests that we don't really need to compare final metrics to initial metrics, but can just compare low-level to high-level metrics.
*)

End Sim.
