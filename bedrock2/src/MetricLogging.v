Require Import Coq.ZArith.BinInt.
Require Import coqutil.Z.Lia.

Section bedrock2.

  Open Scope Z_scope.
  
  Record MetricLog := mkMetricLog {
    instructions: Z;
    stores: Z;
    loads: Z;
    jumps: Z;
  }.

  Definition EmptyMetricLog := mkMetricLog 0 0 0 0.
  Definition UnitMetricLog := mkMetricLog 1 1 1 1.

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

  Definition metricDifference(metric: MetricLog -> Z) initialM finalM: Z :=
    Z.sub (metric finalM) (metric initialM).

  Definition metricLogOp op : MetricLog -> MetricLog -> MetricLog :=
    fun initialM finalM =>
      mkMetricLog
        (op instructions initialM finalM)
        (op stores initialM finalM)
        (op loads initialM finalM)
        (op jumps initialM finalM).

  Definition metricLogDifference := metricLogOp metricDifference.

  Definition boundMetric(metric: MetricLog -> Z) mBound m1 m2: Prop :=
    (metric m1) <= (metric m2) * (metric mBound).

  Definition boundMetricLog(mBound: MetricLog)(m1: MetricLog)(m2: MetricLog): Prop :=
    boundMetric instructions mBound m1 m2 /\
    boundMetric stores mBound m1 m2 /\
    boundMetric loads mBound m1 m2 /\
    boundMetric jumps mBound m1 m2.

End bedrock2.

Hint Unfold
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
     metricLogOp
     metricDifference
     metricLogDifference
     boundMetric
     boundMetricLog
     UnitMetricLog
  : unf_metric_log.
  
Ltac unfold_MetricLog := autounfold with unf_metric_log in *.

Ltac fold_MetricLog :=
  match goal with
  | _ : _ |- context[?x] =>
    match x with
    | {| instructions := instructions ?y;
         stores := stores ?y;
         loads := loads ?y;
         jumps := jumps ?y; |} => replace x with y by (destruct y; reflexivity)
    end
  end.

Ltac simpl_MetricLog :=
  cbn [fst snd] in *; (* Unfold logs in tuples *)
  cbn [instructions loads stores jumps] in *.

Ltac try_equality_MetricLog :=
  repeat match goal with
         | H : MetricLog |- context[{| instructions := ?i; |}] =>
           progress replace i with (instructions H) by bomega
         | H : MetricLog |- context[{| stores := ?i; |}] =>
           progress replace i with (stores H) by bomega      
         | H : MetricLog |- context[{| loads := ?i; |}] =>
           progress replace i with (loads H) by bomega      
         | H : MetricLog |- context[{| jumps := ?i; |}] =>
           progress replace i with (jumps H) by bomega
         end.

Ltac solve_MetricLog :=
  repeat unfold_MetricLog;
  repeat simpl_MetricLog;
  try_equality_MetricLog;
  bomega || f_equal; bomega || fold_MetricLog.
