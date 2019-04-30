Require Import Coq.Lists.List.
Import ListNotations.
Require bedrock2.Examples.Demos.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.PipelineWithRename.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
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
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call argnames fname retnames :=
    if string_dec fname "nop" then
      [[Addi Register0 Register0 0]]
    else
      nil;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_length _ := TODO;
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_emits_valid _ _ := TODO;
}.
Notation RiscvMachine := MetricRiscvMachine.
Definition params : Pipeline.parameters. simple refine {|
  Pipeline.locals := _;
  Pipeline.Registers := _;
  Pipeline.ext_spec _ _ := TODO;
  Pipeline.ext_guarantee _ := False;
  Pipeline.PRParams := TODO;
|}; unshelve (try exact _); apply TODO. Defined.
Definition flatparams := (FlattenExpr.mk_Syntax_params (@Pipeline.FlattenExpr_parameters params)).
Instance pipeline_assumptions: @Pipeline.assumptions params. Admitted.
Instance mapops: RegAlloc.map.ops (SortedListString.map Z) :=
  {| RegAlloc.map.intersect (s1 s2 : SortedListString.map Z) :=
    {| value := ListLib.list_intersect (value s1) (value s2); _value_ok := TODO |} |}.

(* stack grows from high addreses to low addresses, first stack word will be written to
   (stack_pastend-4), next stack word to (stack_pastend-8) etc *)
Definition stack_pastend: Z := 1024.
Definition compile '(functions, initial, reactive) :=
  compile_prog (p:=params) (RegAlloc.map.putmany_of_tuples map.empty functions) stack_pastend initial reactive (List.map fst functions).
Definition instrencode p : list byte :=
  let word8s := List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) p in
  List.map (fun w => Byte.of_Z (word.unsigned w)) word8s.

Definition prog := (
  [swap; swap_swap],
  @cmd.call flatparams [] "swap_swap" [expr.literal (2^9); expr.literal (2^9+4)],
  @cmd.interact flatparams [] "nop" []).


Import riscv.Utility.InstructionNotations.
Import bedrock2.Hexdump.
Local Open Scope hexdump_scope.
Set Printing Width 108.
Goal True.
  let r := eval cbv in (([[
                             Addi 2 0 (2^10-4);
                             Lw 1 2 0;
                             Lw 1 2 0;
                             Lw 1 2 0;
                             Lw 1 2 0;
                             Lw 1 2 0;
                             Sw 2 0 (2^10-4)
                         ]] ++ compile prog)%list) in
  pose r as asm.


  let x := eval cbv in (instrencode asm) in
  idtac x.
Abort.
