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

  Definition metricSub(metric: MetricLog -> Z) finalM initialM : Z :=
    Z.sub (metric finalM) (metric initialM).

  Definition metricsOp op : MetricLog -> MetricLog -> MetricLog :=
    fun initialM finalM =>
      mkMetricLog
        (op instructions initialM finalM)
        (op stores initialM finalM)
        (op loads initialM finalM)
        (op jumps initialM finalM).

  Definition metricsSub := metricsOp metricSub.

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
Infix "-" := metricsSub : MetricH_scope.

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
     metricsOp
     metricSub
     metricsSub
     metricLeq
     metricsLeq
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
