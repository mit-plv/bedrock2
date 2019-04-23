Require Import Coq.Lists.List.
Import ListNotations.
Require bedrock2.Examples.Demos.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import riscv.Utility.Words64Naive.
Require Import riscv.Utility.DefaultMemImpl64.
Require Import riscv.Utility.Monads.
Require Import compiler.util.Common.
Require Import coqutil.Decidable.
Require        riscv.Utility.InstructionNotations.
Require Import riscv.Platform.MinimalLogging.
Require Import bedrock2.MetricLogging.
Require Import riscv.Platform.MetricMinimal.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.SortedList.
Require Import compiler.ZNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import bedrock2.Byte.
Require bedrock2.Hexdump.
Require Import bedrock2.Examples.swap.

Open Scope Z_scope.


Definition var: Set := Z.
Definition Reg: Set := Z.


Existing Instance DefaultRiscvState.

Instance flatToRiscvDef_params: FlatToRiscvDef.FlatToRiscvDef.parameters := {
  FlatToRiscvDef.FlatToRiscvDef.actname := Empty_set;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call _ := Empty_set_rect _;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_length _ := Empty_set_rect _;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_emits_valid _ _ := Empty_set_rect _;
}.

Notation RiscvMachine := (MetricRiscvMachine Register FlatToRiscvDef.FlatToRiscvDef.actname).

Existing Instance coqutil.Map.SortedListString.map.
Existing Instance coqutil.Map.SortedListString.ok.

Set Refine Instance Mode. Set Printing Implicit.
Instance pipeline_params: Pipeline.parameters := {
  Pipeline.locals := _;
  Pipeline.ext_spec _ _ := Empty_set_rect _;
  Pipeline.ext_guarantee _ := False;
  Pipeline.M := OState RiscvMachine;
  Pipeline.PRParams := MetricMinimalMetricPrimitivesParams;
}.
match goal with
| |- ?G => let t2 := type of (BasicC64Semantics.parameters.(@locals))
                                                in assert (G = t2)
end.
{
  simpl. (* problem: swap uses string var names, compiler needs Z var names *)
Abort.

(*
Instance pipeline_assumptions: @Pipeline.assumptions pipeline_params. Admitted.
 *)
