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

  Definition metricAdd(metric: MetricLog -> Z) m1 m2 : Z :=
    Z.add (metric m1) (metric m2).
  Definition metricSub(metric: MetricLog -> Z) m1 m2 : Z :=
    Z.sub (metric m1) (metric m2).

  Definition metricsOp op : MetricLog -> MetricLog -> MetricLog :=
    fun m1 m2 =>
      mkMetricLog
        (op instructions m1 m2)
        (op stores m1 m2)
        (op loads m1 m2)
        (op jumps m1 m2).

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

#[export] Hint Unfold
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

(* need this to define solve_MetricLog, but need solve_MetricLog inside of MetricArith, oops *)
Lemma add_assoc' : forall n m p, (n + (m + p) = n + m + p)%metricsH.
Proof. intros. unfold_MetricLog. f_equal; apply Z.add_assoc. Qed.

Lemma metriclit : forall a b c d a' b' c' d' mc,
  metricsAdd (mkMetricLog a b c d) (metricsAdd (mkMetricLog a' b' c' d') mc) =
  metricsAdd (mkMetricLog (a+a') (b+b') (c+c') (d+d')) mc.
Proof. intros. rewrite add_assoc'. reflexivity. Qed.

Ltac flatten_MetricLog := repeat rewrite metriclit in *.

Ltac solve_MetricLog :=
  flatten_MetricLog;
  repeat unfold_MetricLog;
  repeat simpl_MetricLog;
  blia.

Ltac solve_MetricLog_piecewise :=
  flatten_MetricLog;
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

  Lemma add_comm : forall n m, (n + m = m + n)%metricsH.
  Proof. intros. unfold_MetricLog. f_equal; apply Z.add_comm. Qed.

  Lemma add_assoc : forall n m p, (n + (m + p) = n + m + p)%metricsH.
  Proof. intros. unfold_MetricLog. f_equal; apply Z.add_assoc. Qed.

End MetricArith.

Create HintDb metric_arith.
#[export] Hint Resolve MetricArith.le_trans MetricArith.le_refl MetricArith.add_0_r MetricArith.sub_0_r MetricArith.add_comm MetricArith.add_assoc : metric_arith.
#[export] Hint Resolve <- MetricArith.le_sub_mono : metric_arith.
#[export] Hint Resolve -> MetricArith.le_sub_mono : metric_arith.
