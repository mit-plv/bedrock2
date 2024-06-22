Require Import Coq.ZArith.BinInt.
Require Import coqutil.Z.Lia.

Section Riscv.

  Open Scope Z_scope.

  Record MetricLog := mkMetricLog {
    instructions: Z;
    stores: Z;
    loads: Z; (* Note that this also includes loads of the PC *)
    jumps: Z;
  }.

  Definition EmptyMetricLog := mkMetricLog 0 0 0 0.

  Definition withInstructions i log := mkMetricLog i (stores log) (loads log) (jumps log).
  Definition withStores s log := mkMetricLog (instructions log) s (loads log) (jumps log).
  Definition withLoads l log := mkMetricLog (instructions log) (stores log) l (jumps log).
  Definition withJumps j log := mkMetricLog (instructions log) (stores log) (loads log) j.

  Definition addMetricInstructions n log := withInstructions (instructions log + n) log.
  Definition addMetricStores n log := withStores (stores log + n) log.
  Definition addMetricLoads n log := withLoads (loads log + n) log.
  Definition addMetricJumps n log := withJumps (jumps log + n) log.

  Definition subMetricInstructions n log := withInstructions (instructions log - n) log.
  Definition subMetricStores n log := withStores (stores log - n) log.
  Definition subMetricLoads n log := withLoads (loads log - n) log.
  Definition subMetricJumps n log := withJumps (jumps log - n) log.

  Definition metricAdd(metric: MetricLog -> Z) finalM initialM : Z :=
    Z.add (metric finalM) (metric initialM).
  Definition metricSub(metric: MetricLog -> Z) finalM initialM : Z :=
    Z.sub (metric finalM) (metric initialM).

  Definition metricsOp op : MetricLog -> MetricLog -> MetricLog :=
    fun initialM finalM =>
      mkMetricLog
        (op instructions initialM finalM)
        (op stores initialM finalM)
        (op loads initialM finalM)
        (op jumps initialM finalM).

  Definition metricsAdd := metricsOp metricAdd.
  Definition metricsSub := metricsOp metricSub.

  Definition metricsMul (n : Z) (m : MetricLog) :=
    mkMetricLog
      (n * instructions m)
      (n * stores m)
      (n * loads m)
      (n * jumps m).

  Definition metricLeq(metric: MetricLog -> Z) m1 m2: Prop :=
    (metric m1) <= (metric m2).

  Definition metricsLeq(m1: MetricLog)(m2: MetricLog): Prop :=
    metricLeq instructions m1 m2 /\
    metricLeq stores m1 m2 /\
    metricLeq loads m1 m2 /\
    metricLeq jumps m1 m2.

End Riscv.

Bind Scope MetricH_scope with MetricLog.
Delimit Scope MetricH_scope with metricsH.

Infix "<=" := metricsLeq : MetricH_scope.
Infix "+" := metricsAdd : MetricH_scope.
Infix "-" := metricsSub : MetricH_scope.
Infix "*" := metricsMul : MetricH_scope.

#[global] Hint Unfold
     withInstructions
     withLoads
     withStores
     withJumps
     addMetricInstructions
     addMetricLoads
     addMetricStores
     addMetricJumps
     subMetricInstructions
     subMetricLoads
     subMetricStores
     subMetricJumps
     metricsOp
     metricAdd
     metricsAdd
     metricSub
     metricsSub
     metricsMul
     metricLeq
     metricsLeq
  : unf_metric_log.

Ltac unfold_MetricLog := autounfold with unf_metric_log in *.

Lemma MetricLog_eq: forall m,
    {|
      instructions := instructions m;
      stores := stores m;
      loads := loads m;
      jumps := jumps m;
    |} = m.
Proof.
  destruct m; reflexivity.
Qed.

Ltac fold_MetricLog :=
  rewrite MetricLog_eq in *.

Ltac simpl_MetricLog :=
  cbn [instructions loads stores jumps] in *.

Ltac solve_MetricLog :=
  repeat unfold_MetricLog;
  repeat simpl_MetricLog;
  blia.

Ltac solve_MetricLog_piecewise :=
  repeat unfold_MetricLog;
  repeat simpl_MetricLog;
  f_equal; blia.

Module MetricArith.

  Open Scope MetricH_scope.

  Lemma mul_sub_distr_r : forall n m p, (n - m) * p = n * p - m * p.
  Proof. intros. unfold_MetricLog. f_equal; apply Z.mul_sub_distr_r. Qed.

  Lemma add_sub_swap : forall n m p, n + m - p = n - p + m.
  Proof. intros. unfold_MetricLog. f_equal; apply Z.add_sub_swap. Qed.

  Lemma le_add_le_sub_r : forall n m p, n + p <= m <-> n <= m - p.
  Proof. solve_MetricLog. Qed.

  Lemma le_trans : forall n m p, n <= m -> m <= p -> n <= p.
  Proof. solve_MetricLog. Qed.

  Lemma le_refl : forall m, m <= m.
  Proof. solve_MetricLog. Qed.

  Lemma le_sub_mono : forall n m p, n - p <= m - p <-> n <= m.
  Proof. solve_MetricLog. Qed.

  Lemma add_0_r : forall mc, (mc + EmptyMetricLog)%metricsH = mc.
  Proof. destruct mc. unfold EmptyMetricLog. solve_MetricLog_piecewise. Qed.

  Lemma sub_0_r : forall mc, (mc - EmptyMetricLog)%metricsH = mc.
  Proof. destruct mc. unfold EmptyMetricLog. solve_MetricLog_piecewise. Qed.

End MetricArith.

Create HintDb metric_arith.
#[export] Hint Resolve MetricArith.le_trans MetricArith.le_refl MetricArith.add_0_r MetricArith.sub_0_r : metric_arith.
#[export] Hint Resolve <- MetricArith.le_sub_mono : metric_arith.
#[export] Hint Resolve -> MetricArith.le_sub_mono : metric_arith.

Lemma applyAddInstructions n a b c d : addMetricInstructions n {| instructions := a; stores := b; loads := c; jumps := d |} = {| instructions := a+n; stores := b; loads := c; jumps := d |}. Proof. auto. Qed.
Lemma applyAddStores n a b c d : addMetricStores n {| instructions := a; stores := b; loads := c; jumps := d |} = {| instructions := a; stores := b+n; loads := c; jumps := d |}. Proof. auto. Qed.
Lemma applyAddLoads n a b c d : addMetricLoads n {| instructions := a; stores := b; loads := c; jumps := d |} = {| instructions := a; stores := b; loads := c+n; jumps := d |}. Proof. auto. Qed.
Lemma applyAddJumps n a b c d : addMetricJumps n {| instructions := a; stores := b; loads := c; jumps := d |} = {| instructions := a; stores := b; loads := c; jumps := d+n |}. Proof. auto. Qed.

Ltac applyAddMetricsGoal := (
  repeat (
    try rewrite applyAddInstructions;
    try rewrite applyAddStores;
    try rewrite applyAddLoads;
    try rewrite applyAddJumps
  );
  repeat rewrite <- Z.add_assoc;
  cbn [Z.add Pos.add Pos.succ]
                         ).

Ltac applyAddMetrics H := (
  repeat (
    try rewrite applyAddInstructions in H;
    try rewrite applyAddStores in H;
    try rewrite applyAddLoads in H;
    try rewrite applyAddJumps in H
  );
  repeat rewrite <- Z.add_assoc in H;
  cbn [Z.add Pos.add Pos.succ] in H
).
