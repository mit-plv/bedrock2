Require Import Coq.Lists.List.
Import ListNotations.
Require bedrock2.Examples.Demos.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.PipelineWithRename.
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
Require Import compiler.StringNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import bedrock2.Byte.
Require bedrock2.Hexdump.
Require Import bedrock2.Examples.swap.

Open Scope Z_scope.
Open Scope string_scope.

Definition var: Set := Z.
Definition Reg: Set := Z.


Existing Instance DefaultRiscvState.

Axiom TODO: forall {T: Type}, T.

Instance flatToRiscvDef_params: FlatToRiscvDef.FlatToRiscvDef.parameters := {
  FlatToRiscvDef.FlatToRiscvDef.actname := string;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call _ := TODO;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_length _ := TODO;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_emits_valid _ _ := TODO;
}.

Notation RiscvMachine := (MetricRiscvMachine Register FlatToRiscvDef.FlatToRiscvDef.actname).

Existing Instance coqutil.Map.SortedListString.map.
Existing Instance coqutil.Map.SortedListString.ok.

Set Refine Instance Mode.
Instance pipeline_params: Pipeline.parameters := {
  Pipeline.locals := _;
  Pipeline.Registers := _;
  Pipeline.ext_spec _ _ := TODO;
  Pipeline.ext_guarantee _ := False;
  Pipeline.PRParams := TODO;
}.
all: apply TODO.
Defined.

Instance pipeline_assumptions: @Pipeline.assumptions pipeline_params. Admitted.

Instance mapops: RegAlloc.map.ops (SortedListString.map Z).
constructor.
intros s1 s2.
destruct s1.
destruct s2.
unshelve econstructor.
- exact (ListLib.list_intersect value value0).
- exact TODO.
Defined.

Definition allFuns: list swap.bedrock_func := [swap; swap_swap].

Definition e := RegAlloc.map.putmany_of_tuples map.empty allFuns.

Definition funnames: list string := List.map fst allFuns.

Definition s: @cmd.cmd (FlattenExpr.mk_Syntax_params _) :=
  @cmd.call (FlattenExpr.mk_Syntax_params _) [] "swap_swap" [expr.literal 100; expr.literal 108].

Definition swap_asm: list Instruction := Eval cbv in compile_prog e s funnames.

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  (* TODO missing because irregular formatting in Decode.v *)
  Notation "'ld' 'x' r1 , 'x' r2 , i" := (Ld r1 r2 i) (at level 10, i at level 200, format "'//'     'ld'       'x' r1 ,  'x' r2 ,  i").

  Print swap_asm.
End PrintAssembly.
