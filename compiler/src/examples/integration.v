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
Open Scope ilist_scope.

Axiom TODO: forall {T: Type}, T.

Local Existing Instance DefaultRiscvState.
Local Existing Instance coqutil.Map.SortedListString.map.
Local Existing Instance coqutil.Map.SortedListString.ok.
Instance flatToRiscvDef_params: FlatToRiscvDef.FlatToRiscvDef.parameters := {
  FlatToRiscvDef.FlatToRiscvDef.actname := string;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call argnames fname retnames :=
    if string_dec fname "nop" then
      [[Addi Register0 Register0 0]]
    else
      nil;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_length _ := TODO;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_emits_valid _ _ := TODO;
}.
Notation RiscvMachine := (MetricRiscvMachine Register FlatToRiscvDef.FlatToRiscvDef.actname).
Instance pipeline_params: Pipeline.parameters. simple refine {|
  Pipeline.locals := _;
  Pipeline.Registers := _;
  Pipeline.ext_spec _ _ := TODO;
  Pipeline.ext_guarantee _ := False;
  Pipeline.PRParams := TODO;
|}; unshelve (try exact _); apply TODO. Defined.
Instance pipeline_assumptions: @Pipeline.assumptions pipeline_params. Admitted.
Instance mapops: RegAlloc.map.ops (SortedListString.map Z) :=
  {| RegAlloc.map.intersect (s1 s2 : SortedListString.map Z) :=
    {| value := ListLib.list_intersect (value s1) (value s2); _value_ok := TODO |} |}.

Definition compile '(functions, initial, reactive) :=
  compile_prog (RegAlloc.map.putmany_of_tuples map.empty functions) initial reactive (List.map fst functions).
Definition instrencode p : list byte :=
  let word8s := List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) p in
  List.map (fun w => Byte.of_Z (word.unsigned w)) word8s.

Definition prog := (
  [swap; swap_swap],
  @cmd.call (FlattenExpr.mk_Syntax_params _) [] "swap_swap" [expr.literal 100; expr.literal 108],
  @cmd.interact (FlattenExpr.mk_Syntax_params _) [] "nop" []).


Import riscv.Utility.InstructionNotations.
Import bedrock2.Hexdump.
Set Printing Width 100.
Goal True.
  let r := eval cbv in (compile prog) in
  pose r as asm.

  Local Open Scope hexdump_scope.

  let x := eval cbv in (instrencode asm) in
  idtac (* x *).
  do 32 idtac "0a552583".
Abort.
