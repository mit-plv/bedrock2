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

  Definition related_without_functions: ExprImp.SimState -> FlatImp.SimState -> Prop :=
    fun '(e1, c1, done1, t1, m1, l1) '(e2, c2, done2, t2, m2, l2) =>
      e1 = map.empty /\ e2 = map.empty (* TODO allow non-empty function environments *) /\
      ExprImp2FlatImp c1 = c2 /\
      done1 = done2 /\
      t1 = t2 /\
      m1 = m2 /\
      map.extends l2 l1 /\
      map.undef_on l1 (allFreshVars (freshNameGenState (ExprImp.allVars_cmd_as_list c1))).

  Definition related: ExprImp.SimState -> FlatImp.SimState -> Prop :=
    fun '(e1, c1, done1, t1, m1, l1) '(e2, c2, done2, t2, m2, l2) =>
      (forall f argvars resvars body1,
          map.get e1 f = Some (argvars, resvars, body1) ->
          map.get e2 f = Some (argvars, resvars, ExprImp2FlatImp body1)) /\
      ExprImp2FlatImp c1 = c2 /\
      done1 = done2 /\
      t1 = t2 /\
      m1 = m2 /\
      (* TODO flattenExpr has to unset all vars at the end of the compiled stmt *)
      l1 = l2 /\
      (* map.extends l2 l1 /\ *)
      map.undef_on l1 (allFreshVars (freshNameGenState (ExprImp.allVars_cmd_as_list c1))).

  Axiom TODO_sam: False.

  Lemma related_change_done: forall done3 e1 c1 done1 t1 m1 l1 e2 c2 done2 t2 m2 l2,
      related (e1, c1, done1, t1, m1, l1) (e2, c2, done2, t2, m2, l2) ->
      related (e1, c1, done3, t1, m1, l1) (e2, c2, done3, t2, m2, l2).
  Proof.
    intros. unfold related in *. simp. auto 10.
  Qed.

  Lemma relate_related{hyps: FlattenExpr.assumptions p}: forall s1 s2,
      related_without_functions s1 s2 <-> related s1 s2.
  Proof.
    intros (((((e1 & c1) & done1) & t1) & m1) & l1) (((((e2 & c2) & done2) & t2) & m2) & l2).
    split; intro H; unfold related_without_functions, related in *.
    - intuition idtac.
      + subst. rewrite @map.get_empty in H6.
        * discriminate.
        * refine (FlattenExpr.funname_env_ok _).
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
    split; [reflexivity|intros].
    unfold ExprImp2FlatImp.
    match goal with
    | |- context [ fst ?x ] => destruct x as [s ngs] eqn: E
    end.
    simpl.
    assert (PropSet.disjoint (ExprImp.allVars_cmd c1)
                             (allFreshVars (freshNameGenState (ExprImp.allVars_cmd_as_list c1))))
      as D. {
      intro x.
      pose proof (NameGen.freshNameGenState_spec (ExprImp.allVars_cmd_as_list c1) x) as P.
      assert (varname_eq_dec: forall a b: Syntax.varname, {a = b} + {a <> b}). {
        intros. destr (Semantics.varname_eqb a b); auto.
      }
      match type of P with
      | List.In ?x ?l -> _ => destruct (List.in_dec varname_eq_dec x l) as
            [Iyes | Ino]
      end.
      * auto.
      * left. clear -Ino.
        intro. apply Ino.
        epose proof (ExprImp.allVars_cmd_allVars_cmd_as_list _ _) as P. destruct P as [P _].
        apply P.
        apply H.
    }
    eapply FlatImp.exec.weaken.
    - eapply @flattenStmt_correct_aux.
      + typeclasses eauto.
      + apply H0r.
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
    Grab Existential Variables. constructor; exact BinInt.Z.one.
  Qed.

  Lemma flattenExprSim{hyps: FlattenExpr.assumptions p}:
    simulation ExprImp.SimExec FlatImp.SimExec related.
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
