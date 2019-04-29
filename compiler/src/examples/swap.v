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

Definition swap_asm: list Instruction := Eval cbv in compile_prog e s cmd.skip funnames.

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Goal True. let r := eval unfold swap_asm in swap_asm in idtac r. Abort.
  (* Annotated:

  main:
     addi    x3, x0, 100   // load literals
     addi    x4, x0, 108
     sd      x2, x3, -16   // push args on stack
     sd      x2, x4, -8
     jal     x1, 64        // call swap_swap

  swap:
     addi    x2, x2, -40   // decrease sp
     sd      x2, x1, 16    // save ra
     sd      x2, x5, 0     // save registers modified by swap
     sd      x2, x6, 8
     ld      x3, x2, 24    // load args
     ld      x4, x2, 32    // body of swap
     ld      x5, x4, 0
     ld      x6, x3, 0
     sd      x4, x6, 0
     sd      x3, x5, 0
     ld      x5, x2, 0     // restore modified registers
     ld      x6, x2, 8
     ld      x1, x2, 16    // load ra
     addi    x2, x2, 40    // increase sp
     jalr    x0, x1, 0     // return

  swap_swap:
     addi    x2, x2, -24   // decrease sp
     sd      x2, x1, 0     // save ra
     ld      x3, x2, 8     // load args from stack
     ld      x4, x2, 16
     sd      x2, x3, -16
     sd      x2, x4, -8
     jal     x1, -84       // first call to swap
     sd      x2, x3, -16   // previous call had no ret vals to be loaded. push args onto stack
     sd      x2, x4, -8
     jal     x1, -96       // second call to swap
     ld      x1, x2, 0     // load ra
     addi    x2, x2, 24    // increase sp
     jalr    x0, x1, 0     // return

  *)
End PrintAssembly.
