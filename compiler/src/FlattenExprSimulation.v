Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.MetricLogging.
Require Import compiler.FlattenExpr.
Require Import compiler.Simulation.
Require Import compiler.Simp.


Section Sim.

  Context {p: FlattenExpr.parameters}.

  Definition State1: Type :=
    Semantics.env * Syntax.cmd * Semantics.trace * Semantics.mem * Semantics.locals * MetricLog.

  Definition exec1: State1 -> (State1 -> Prop) -> Prop :=
    fun '(e, c, t, m, l, mc) post =>
      Semantics.exec e c t m l mc (fun t' m' l' mc' => post (e, c, t', m', l', mc')).

  Definition State2: Type :=
    FlatImp.env * FlatImp.stmt * Semantics.trace * Semantics.mem * Semantics.locals * MetricLog.

  Definition exec2: State2 -> (State2 -> Prop) -> Prop :=
    fun '(e, c, t, m, l, mc) post =>
      FlatImp.exec e c t m l mc (fun t' m' l' mc' => post (e, c, t', m', l', mc')).

  Definition related: State1 -> State2 -> Prop :=
    fun '(e1, c1, t1, m1, l1, mc1) '(e2, c2, t2, m2, l2, mc2) =>
      e1 = map.empty /\ e2 = map.empty (* TODO allow non-empty function environments *) /\
      ExprImp2FlatImp c1 = c2 /\
      t1 = t2 /\
      m1 = m2 /\
      map.extends l2 l1 /\
      (mc2 <= mc1)%metricsH.

  Axiom TODO_restrict_initial_state: False.

  Lemma flattenExprSim{hyps: FlattenExpr.assumptions p}: simulation exec1 exec2 related.
  Proof.
    unfold simulation, exec1, exec2, related.
    intros.
    destruct s1 as [[[[[e1 c1] t1] m1] l1] mc1].
    destruct s2 as [[[[[e2 c2] t2] m2] l2] mc2].
    simp.
    unfold ExprImp2FlatImp.
    match goal with
    | |- context [ fst ?x ] => destruct x as [s ngs] eqn: E
    end.
    simpl.
    eapply FlatImp.exec.weaken.
    - eapply @flattenStmt_correct_aux.
      + typeclasses eauto.
      + eassumption.
      + reflexivity.
      + exact E.
      + assumption.
      + case TODO_restrict_initial_state.
      + intro x.
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
    - simpl. intros. simp.
      eexists. split; [|eassumption]. simpl. rewrite E. simpl.
      repeat (split; [solve [auto]|]).
      solve_MetricLog.
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
