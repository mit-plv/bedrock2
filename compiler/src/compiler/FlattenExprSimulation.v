Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import bedrock2.MetricLogging.
Require Import compiler.FlattenExprDef.
Require Import compiler.FlattenExpr.
Require Import compiler.NameGen.
Require Import compiler.Simulation.
Require Import coqutil.Tactics.Simp.


Section Sim.
  Context {p: FlattenExpr.parameters}.

  Definition related(max_size: Z)(done: bool): ExprImp.SimState -> FlatImp.SimState String.string -> Prop :=
    fun '(t1, m1, l1, mc1) '(t2, m2, l2, mc2) =>
      t1 = t2 /\
      m1 = m2 /\
      l1 = map.empty.

  Lemma flattenExprSim{hyps: FlattenExpr.assumptions p}(max_size: Z)
        (e1: FlattenExpr.ExprImp_env)(e2: FlattenExpr.FlatImp_env)(funname: String.string):
    flatten_functions max_size e1 = Some e2 ->
    simulation (ExprImp.SimExec e1 (Syntax.cmd.call nil funname nil))
               (FlatImp.SimExec String.string e2 (FlatImp.SSeq FlatImp.SSkip (FlatImp.SCall nil funname nil)))
               (related max_size).
  Proof.
    unfold simulation, related, ExprImp.SimExec, FlatImp.SimExec.
    intros H.
    intros (((done1 & t1) & m1) & l1) (((done2 & t2) & m2) & l2).
    intros.
    simp.
    simpl.
    eapply FlatImp.exec.weaken.
    - eapply @flattenStmt_correct_aux with (eH := e1) (ngs := freshNameGenState nil).
      + typeclasses eauto.
      + eassumption.
      + eapply Semantics.exec.call; try eassumption.
        (* "eassumption" fails, but "exact" succeeds ?? *)
        (* works:
        match goal with
        | |- ?G => let T := type of H12 in unify T G; eassumption
        end. *)
        (* works: apply H12. *)
        Fail eassumption.
        match goal with
        | H: _ |- _ => exact H
        end.
      + reflexivity.
      + reflexivity.
      + intros x k A. rewrite map.get_empty in A. discriminate.
      + unfold map.undef_on, map.agree_on. intros. reflexivity.
      + cbv. intros. left. tauto.
    - simpl. intros. simp.
      eexists. split; [|eassumption]. simpl.
      repeat (split; eauto).
      + unfold map.only_differ in *.
        apply map.map_ext.
        intro x.
        match goal with
        | H: _ |- _ => specialize (H x); rename H into B
        end.
        destruct B as [B | B].
        * cbv in B. contradiction.
        * congruence.
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
