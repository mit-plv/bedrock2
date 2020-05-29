Require Export bedrock2.MetricLogging. (* Naming is easier if this is first *)
Require Export riscv.Platform.MetricLogging.

Section MetricsToRiscv.

  Local Notation metricsH := bedrock2.MetricLogging.MetricLog.
  Local Notation metricsL := Platform.MetricLogging.MetricLog.

  Local Notation instructionsH := bedrock2.MetricLogging.instructions.
  Local Notation jumpsH := bedrock2.MetricLogging.jumps.
  Local Notation loadsH := bedrock2.MetricLogging.loads.
  Local Notation storesH := bedrock2.MetricLogging.stores.

  Local Notation instructionsL := Platform.MetricLogging.instructions.
  Local Notation jumpsL := Platform.MetricLogging.jumps.
  Local Notation loadsL := Platform.MetricLogging.loads.
  Local Notation storesL := Platform.MetricLogging.stores.

  Definition lowerMetrics (mh: metricsH): metricsL := {|
    instructionsL := instructionsH mh;
    jumpsL := jumpsH mh;
    loadsL := loadsH mh;
    storesL := storesH mh;
  |}.

End MetricsToRiscv.

Ltac solve_MetricLog :=
  cbv [lowerMetrics] in *;
  repeat bedrock2.MetricLogging.unfold_MetricLog;
  repeat bedrock2.MetricLogging.simpl_MetricLog;
  riscv.Platform.MetricLogging.solve_MetricLog.
