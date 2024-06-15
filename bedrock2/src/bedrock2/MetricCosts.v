Require Import BinIntDef.
Require Import Coq.Strings.String.
Require Import bedrock2.MetricLogging.
From coqutil.Tactics Require Import destr.

Local Open Scope MetricH_scope.

Inductive compphase: Type :=
| PreSpill
| PostSpill.

Section FlatImpExec.

  Context {varname: Type}.
  Variable (phase: compphase).
  Variable (isReg: varname -> bool).

  Definition cost_interact mc :=
    match phase with
    | PreSpill => (addMetricInstructions 100 (addMetricJumps 100 (addMetricStores 100 (addMetricLoads 100 mc))))
    | PostSpill => (addMetricInstructions 50 (addMetricJumps 50 (addMetricStores 50 (addMetricLoads 50 mc))))
    end.

  Definition cost_call_internal mc :=
    match phase with
    | PreSpill => addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc)))
    | PostSpill => addMetricInstructions 50 (addMetricJumps 50 (addMetricLoads 50 (addMetricStores 50 mc)))
    end.

  Definition cost_call_external mc :=
    match phase with
    | PreSpill => addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc)))
    | PostSpill => addMetricInstructions 50 (addMetricJumps 50 (addMetricLoads 50 (addMetricStores 50 mc)))
    end.

  (* TODO think about a non-fixed bound on the cost of function preamble and postamble *)

  Definition cost_load x a mc :=
    match (isReg x, isReg a) with
    | (false, false) => (addMetricInstructions 3 (addMetricLoads 5 (addMetricStores 1 mc)))
    | (false,  true) => (addMetricInstructions 2 (addMetricLoads 3 (addMetricStores 1 mc)))
    | ( true, false) => (addMetricInstructions 2 (addMetricLoads 4 mc))
    | ( true,  true) => (addMetricInstructions 1 (addMetricLoads 2 mc))
    end.

  Definition cost_store a v mc :=
    match (isReg a, isReg v) with
    | (false, false) => (addMetricInstructions 3 (addMetricLoads 5 (addMetricStores 1 mc)))
    | (false,  true) => (addMetricInstructions 2 (addMetricLoads 3 (addMetricStores 1 mc)))
    | ( true, false) => (addMetricInstructions 2 (addMetricLoads 3 (addMetricStores 1 mc)))
    | ( true,  true) => (addMetricInstructions 1 (addMetricLoads 1 (addMetricStores 1 mc)))
    end.

  Definition cost_inlinetable x i mc :=
    match (isReg x, isReg i) with
    | (false, false) => (addMetricInstructions 5 (addMetricLoads 7 (addMetricStores 1 (addMetricJumps 1 mc))))
    | (false,  true) => (addMetricInstructions 4 (addMetricLoads 5 (addMetricStores 1 (addMetricJumps 1 mc))))
    | ( true, false) => (addMetricInstructions 4 (addMetricLoads 6 (addMetricJumps 1 mc)))
    | ( true,  true) => (addMetricInstructions 3 (addMetricLoads 4 (addMetricJumps 1 mc)))
    end.

  Definition cost_stackalloc x mc :=
    match isReg x with
    | false => (addMetricInstructions 2 (addMetricLoads 2 (addMetricStores 1 mc)))
    |  true => (addMetricInstructions 1 (addMetricLoads 1 mc))
    end.

  Definition cost_lit x mc :=
    match isReg x with
    | false => (addMetricInstructions 9 (addMetricLoads 9 (addMetricStores 1 mc)))
    |  true => (addMetricInstructions 8 (addMetricLoads 8 mc))
    end.

  Definition cost_op x y z mc :=
    match (isReg x, isReg y, isReg z) with
    | (false, false, false) => (addMetricInstructions 5 (addMetricLoads 7 (addMetricStores 1 mc)))
    | (false, false,  true) | (false,  true, false) => (addMetricInstructions 4 (addMetricLoads 5 (addMetricStores 1 mc)))
    | (false,  true,  true) => (addMetricInstructions 3 (addMetricLoads 3 (addMetricStores 1 mc)))
    | ( true, false, false) => (addMetricInstructions 4 (addMetricLoads 6 mc))
    | ( true, false,  true) | ( true,  true, false) => (addMetricInstructions 3 (addMetricLoads 4 mc))
    | ( true,  true,  true) => (addMetricInstructions 2 (addMetricLoads 2 mc))
    end.

  Definition cost_set x y mc :=
    match (isReg x, isReg y) with
    | (false, false) => (addMetricInstructions 3 (addMetricLoads 4 (addMetricStores 1 mc)))
    | (false,  true) => (addMetricInstructions 2 (addMetricLoads 2 (addMetricStores 1 mc)))
    | ( true, false) => (addMetricInstructions 2 (addMetricLoads 3 mc))
    | ( true,  true) => (addMetricInstructions 1 (addMetricLoads 1 mc))
    end.

    Definition cost_if x y mc :=
      match (isReg x, match y with | Some y' => isReg y' | None => true end) with
      | (false, false) => (addMetricInstructions 4 (addMetricLoads 6 (addMetricJumps 1 mc)))
      | (false,  true) | ( true, false) => (addMetricInstructions 3 (addMetricLoads 4 (addMetricJumps 1 mc)))
      | ( true,  true) => (addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc)))
      end.

    Definition cost_loop_true x y mc :=
      match (isReg x, match y with | Some y' => isReg y' | None => true end) with
      | (false, false) => (addMetricInstructions 4 (addMetricLoads 6 (addMetricJumps 1 mc)))
      | (false,  true) | ( true, false) => (addMetricInstructions 3 (addMetricLoads 4 (addMetricJumps 1 mc)))
      | ( true,  true) => (addMetricInstructions 2 (addMetricLoads 2 (addMetricJumps 1 mc)))
      end.

    Definition cost_loop_false x y mc :=
      match (isReg x, match y with | Some y' => isReg y' | None => true end) with
      | (false, false) => (addMetricInstructions 3 (addMetricLoads 5 (addMetricJumps 1 mc)))
      | (false,  true) | ( true, false) => (addMetricInstructions 2 (addMetricLoads 3 (addMetricJumps 1 mc)))
      | ( true,  true) => (addMetricInstructions 1 (addMetricLoads 1 (addMetricJumps 1 mc)))
      end.

End FlatImpExec.

Definition isRegZ (var : Z) : bool :=
  Z.leb var 31.

Definition isRegStr (var : String.string) : bool :=
  String.prefix "reg_" var.

Ltac cost_unfold :=
  unfold cost_interact, cost_call_internal, cost_call_external, cost_load,
  cost_store, cost_inlinetable, cost_stackalloc, cost_lit, cost_op, cost_set,
  cost_if, cost_loop_true, cost_loop_false, EmptyMetricLog in *.

Ltac cost_destr :=
  repeat match goal with
         | x : compphase |- _ => destr x
         | _ : context[if ?x then _ else _] |- _ => destr x; try discriminate
         | |- context[if ?x then _ else _] => destr x; try discriminate
         end.

Ltac cost_solve := cost_unfold; cost_destr; try solve_MetricLog.
Ltac cost_solve_piecewise := cost_unfold; cost_destr; try solve_MetricLog_piecewise.

Definition metrics_additive f := forall mc, f mc - mc = f EmptyMetricLog.
#[global] Transparent metrics_additive.

Ltac t := unfold metrics_additive; intros; cost_solve_piecewise.
Lemma cost_additive_interact : forall phase, metrics_additive (cost_interact phase). Proof. t. Qed.
Lemma cost_additive_call_internal : forall phase, metrics_additive (cost_call_internal phase). Proof. t. Qed.
Lemma cost_additive_call_external : forall phase, metrics_additive (cost_call_external phase). Proof. t. Qed.
Lemma cost_additive_load : forall varname isReg x a, metrics_additive (@cost_load varname isReg x a). Proof. t. Qed.
Lemma cost_additive_store : forall varname isReg x a, metrics_additive (@cost_store varname isReg x a). Proof. t. Qed.
Lemma cost_additive_inlinetable : forall varname isReg x a, metrics_additive (@cost_inlinetable varname isReg x a). Proof. t. Qed.
Lemma cost_additive_stackalloc : forall varname isReg x, metrics_additive (@cost_stackalloc varname isReg x). Proof. t. Qed.
Lemma cost_additive_lit : forall varname isReg x, metrics_additive (@cost_lit varname isReg x). Proof. t. Qed.
Lemma cost_additive_op : forall varname isReg x y z, metrics_additive (@cost_op varname isReg x y z). Proof. t. Qed.
Lemma cost_additive_set : forall varname isReg x y, metrics_additive (@cost_set varname isReg x y). Proof. t. Qed.
Lemma cost_additive_if : forall varname isReg x y, metrics_additive (@cost_if varname isReg x y). Proof. t. Qed.
Lemma cost_additive_loop_true : forall varname isReg x y, metrics_additive (@cost_loop_true varname isReg x y). Proof. t. Qed.
Lemma cost_additive_loop_false : forall varname isReg x y, metrics_additive (@cost_loop_false varname isReg x y). Proof. t. Qed.

(* COQBUG:
   these cannot have "in *", because this causes a crash if the environment contains a Semantics.ExtSpec.
     Anomaly "Unable to handle arbitrary u+k <= v constraints."
     Please report at http://coq.inria.fr/bugs/.
   to use these in hypotheses, revert them first *)
Ltac cost_additive := repeat (
  rewrite cost_additive_interact ||
  rewrite cost_additive_call_internal ||
  rewrite cost_additive_call_external ||
  rewrite cost_additive_load ||
  rewrite cost_additive_store ||
  rewrite cost_additive_inlinetable ||
  rewrite cost_additive_stackalloc ||
  rewrite cost_additive_lit ||
  rewrite cost_additive_op ||
  rewrite cost_additive_set ||
  rewrite cost_additive_if ||
  rewrite cost_additive_loop_true ||
  rewrite cost_additive_loop_false
  ).

Ltac cost_hammer := cost_additive; try solve [eauto 3 with metric_arith | cost_solve].
