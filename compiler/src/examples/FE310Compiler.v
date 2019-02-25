Require Import Coq.Lists.List.
Import ListNotations.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import compiler.Basic32Semantics.
Require Import riscv.util.Monads.
Require Import compiler.util.Common.
Require        riscv.InstructionNotations.
Require Import riscv.MinimalMMIO.
Require Import riscv.Utility.
Require Import riscv.Encode.
Require Import coqutil.Map.SortedList.
Require Import compiler.ZNameGen.
Require Import riscv.InstructionCoercions.
Require Import bedrock2.Byte.
Require bedrock2.Hexdump.
Require Import compiler.examples.MMIO.


Open Scope Z_scope.

Notation RiscvMachine := (RiscvMachine Register MMIOAction).

Instance mmio_params: MMIO.parameters := { (* everything is inferred automatically *) }.

Instance foo: FlatToRiscv.FlatToRiscv.parameters := _.

Instance pipeline_params: Pipeline.parameters := {
  Pipeline.W := Words32Naive.Words32Naive;
  Pipeline.ext_spec := FlatToRiscv.FlatToRiscv.ext_spec;
  Pipeline.ext_guarantee := @FlatToRiscv.FlatToRiscv.ext_guarantee foo;
  Pipeline.M := OStateND RiscvMachine;
  Pipeline.PRParams := MinimalMMIOPrimitivesParams;
}.

Instance pipeline_assumptions: @Pipeline.assumptions pipeline_params. Admitted.

Definition compileFunc: cmd -> list Instruction := exprImp2Riscv.

Definition instructions_to_word8(insts: list Instruction): list Utility.byte :=
  List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) insts.

Definition main(c: cmd): list byte :=
  let instrs := compileFunc c in
  let word8s := instructions_to_word8 instrs in
  List.map (fun w => Byte.of_Z (word.unsigned w)) word8s.

(*
   a = input(magicMMIOAddrLit);
   b = input(magicMMIOAddrLit);
   output(magicMMIOAddrLit, a+b);
*)
Example a: varname := 1.
Example b: varname := 2.
Example mmio_adder: cmd :=
  (cmd.seq (cmd.interact [a] MMInput [expr.literal magicMMIOAddrLit])
  (cmd.seq (cmd.interact [b] MMInput [expr.literal magicMMIOAddrLit])
           (cmd.interact [] MMOutput [expr.literal magicMMIOAddrLit;
                                        expr.op bopname.add (expr.var a) (expr.var b)]))).

Eval vm_compute in compileFunc mmio_adder.

Definition mmio_adder_bytes: list byte := Eval vm_compute in main mmio_adder.

Module PrintBytes.
  Import bedrock2.Hexdump.
  Local Open Scope hexdump_scope.
  Set Printing Width 100.
  Goal True. let x := eval cbv in mmio_adder_bytes in idtac x. Abort.
End PrintBytes.
