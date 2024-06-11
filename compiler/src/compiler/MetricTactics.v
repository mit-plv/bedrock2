Require Import compiler.util.Common.
Require Import bedrock2.MetricLogging.
Require Import compiler.FlatImp.

Open Scope MetricH_scope.

Definition metrics_additive f := forall mc, f mc - mc = f EmptyMetricLog.
#[global] Transparent metrics_additive.

Ltac exec_cost_unfold :=
  unfold exec.cost_SInteract, exec.cost_SCall_internal,
  exec.cost_SCall_external, exec.cost_SLoad, exec.cost_SStore,
  exec.cost_SInlinetable, exec.cost_SStackalloc, exec.cost_SLit, exec.cost_SOp,
  exec.cost_SSet, exec.cost_SIf, exec.cost_SLoop_true, exec.cost_SLoop_false in
  *.

Ltac exec_cost_destr :=
  repeat match goal with
         | x : compphase |- _ => destr x
         | x : operand |- _ => destr x
         | x : bcond _ |- _ => destr x
         | _ : context[if ?x then _ else _] |- _ => destr x
         | |- context[if ?x then _ else _] => destr x
         end; unfold EmptyMetricLog.

Ltac exec_cost_solve := exec_cost_unfold; exec_cost_destr; try solve_MetricLog.
Ltac exec_cost_solve_piecewise := exec_cost_unfold; exec_cost_destr; try solve_MetricLog_piecewise.

Ltac t := unfold metrics_additive; intros; exec_cost_solve_piecewise.

Lemma exec_cost_additive_SInteract : forall phase, metrics_additive (exec.cost_SInteract phase). Proof. t. Qed.
Lemma exec_cost_additive_SCall_internal : forall phase, metrics_additive (exec.cost_SCall_internal phase). Proof. t. Qed.
Lemma exec_cost_additive_SCall_external : forall phase, metrics_additive (exec.cost_SCall_external phase). Proof. t. Qed.
Lemma exec_cost_additive_SLoad : forall varname isReg x a, metrics_additive (@exec.cost_SLoad varname isReg x a). Proof. t. Qed.
Lemma exec_cost_additive_SStore : forall varname isReg x a, metrics_additive (@exec.cost_SStore varname isReg x a). Proof. t. Qed.
Lemma exec_cost_additive_SInlinetable : forall varname isReg x a, metrics_additive (@exec.cost_SInlinetable varname isReg x a). Proof. t. Qed.
Lemma exec_cost_additive_SStackalloc : forall varname isReg x, metrics_additive (@exec.cost_SStackalloc varname isReg x). Proof. t. Qed.
Lemma exec_cost_additive_SLit : forall varname isReg x, metrics_additive (@exec.cost_SLit varname isReg x). Proof. t. Qed.
Lemma exec_cost_additive_SOp : forall varname isReg x y z, metrics_additive (@exec.cost_SOp varname isReg x y z). Proof. t. Qed.
Lemma exec_cost_additive_SSet : forall varname isReg x y, metrics_additive (@exec.cost_SSet varname isReg x y). Proof. t. Qed.
Lemma exec_cost_additive_SIf : forall varname isReg x, metrics_additive (@exec.cost_SIf varname isReg x). Proof. t. Qed.
Lemma exec_cost_additive_SLoop_true : forall varname isReg x, metrics_additive (@exec.cost_SLoop_true varname isReg x). Proof. t. Qed.
Lemma exec_cost_additive_SLoop_false : forall varname isReg x, metrics_additive (@exec.cost_SLoop_false varname isReg x). Proof. t. Qed.

(* COQBUG:
   these cannot have "in *", because this causes a crash if the environment contains a Semantics.ExtSpec.
     Anomaly "Unable to handle arbitrary u+k <= v constraints."
     Please report at http://coq.inria.fr/bugs/.
   to use these in hypotheses, revert them first *)
Ltac exec_cost_additive := repeat (
  rewrite exec_cost_additive_SInteract ||
  rewrite exec_cost_additive_SCall_internal ||
  rewrite exec_cost_additive_SCall_external ||
  rewrite exec_cost_additive_SLoad ||
  rewrite exec_cost_additive_SStore ||
  rewrite exec_cost_additive_SInlinetable ||
  rewrite exec_cost_additive_SStackalloc ||
  rewrite exec_cost_additive_SLit ||
  rewrite exec_cost_additive_SOp ||
  rewrite exec_cost_additive_SSet ||
  rewrite exec_cost_additive_SIf ||
  rewrite exec_cost_additive_SLoop_true ||
  rewrite exec_cost_additive_SLoop_false
  ).

Ltac exec_cost_hammer := exec_cost_additive; try solve [eauto 3 with metric_arith | exec_cost_solve].
