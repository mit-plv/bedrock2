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
    | PreSpill => mkMetricLog 100 100 100 100
    | PostSpill => mkMetricLog 50 50 50 50
    end + mc.

  Definition cost_call_internal mc :=
    match phase with
    | PreSpill => mkMetricLog 100 100 100 100
    | PostSpill => mkMetricLog 50 50 50 50
    end + mc.

  Definition cost_call_external mc :=
    match phase with
    | PreSpill => mkMetricLog 100 100 100 100
    | PostSpill => mkMetricLog 50 50 50 50
    end + mc.

  (* TODO think about a non-fixed bound on the cost of function preamble and postamble *)

  Definition cost_load x a mc :=
    match (isReg x, isReg a) with
    | (false, false) => mkMetricLog 3 1 5 0
    | (false,  true) => mkMetricLog 2 1 3 0
    | ( true, false) => mkMetricLog 2 0 4 0
    | ( true,  true) => mkMetricLog 1 0 2 0
    end + mc.

  Definition cost_store a v mc :=
    match (isReg a, isReg v) with
    | (false, false) => mkMetricLog 3 1 5 0
    | (false,  true) => mkMetricLog 2 1 3 0
    | ( true, false) => mkMetricLog 2 1 3 0
    | ( true,  true) => mkMetricLog 1 1 1 0
    end + mc.

  Definition cost_inlinetable x i mc :=
    match (isReg x, isReg i) with
    | (false, false) => mkMetricLog 5 1 7 1
    | (false,  true) => mkMetricLog 4 1 5 1
    | ( true, false) => mkMetricLog 4 0 6 1
    | ( true,  true) => mkMetricLog 3 0 4 1
    end + mc.

  Definition cost_stackalloc x mc :=
    match isReg x with
    | false => mkMetricLog 2 1 2 0
    |  true => mkMetricLog 1 0 1 0
    end + mc.

  Definition cost_lit x mc :=
    match isReg x with
    | false => mkMetricLog 9 1 9 0
    |  true => mkMetricLog 8 0 8 0
    end + mc.

  Definition cost_op x y z mc :=
    match (isReg x, isReg y, isReg z) with
    | (false, false, false)                         => mkMetricLog 5 1 7 0
    | (false, false,  true) | (false,  true, false) => mkMetricLog 4 1 5 0
    | (false,  true,  true)                         => mkMetricLog 3 1 3 0
    | ( true, false, false)                         => mkMetricLog 4 0 6 0
    | ( true, false,  true) | ( true,  true, false) => mkMetricLog 3 0 4 0
    | ( true,  true,  true)                         => mkMetricLog 2 0 2 0
    end + mc.

  Definition cost_set x y mc :=
    match (isReg x, isReg y) with
    | (false, false) => mkMetricLog 3 1 4 0
    | (false,  true) => mkMetricLog 2 1 2 0
    | ( true, false) => mkMetricLog 2 0 3 0
    | ( true,  true) => mkMetricLog 1 0 1 0
    end + mc.

    Definition cost_if x y mc :=
      match (isReg x, match y with | Some y' => isReg y' | None => true end) with
      | (false, false)                  => mkMetricLog 4 0 6 1
      | (false,  true) | ( true, false) => mkMetricLog 3 0 4 1
      | ( true,  true)                  => mkMetricLog 2 0 2 1
      end + mc.

    Definition cost_loop_true x y mc :=
      match (isReg x, match y with | Some y' => isReg y' | None => true end) with
      | (false, false)                  => mkMetricLog 4 0 6 1
      | (false,  true) | ( true, false) => mkMetricLog 3 0 4 1
      | ( true,  true)                  => mkMetricLog 2 0 2 1
      end + mc.

    Definition cost_loop_false x y mc :=
      match (isReg x, match y with | Some y' => isReg y' | None => true end) with
      | (false, false)                  => mkMetricLog 3 0 5 1
      | (false,  true) | ( true, false) => mkMetricLog 2 0 3 1
      | ( true,  true)                  => mkMetricLog 1 0 1 1
      end + mc.

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
Ltac cost_hammer := try solve [eauto 3 with metric_arith | cost_solve].
