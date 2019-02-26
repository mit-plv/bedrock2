Require Import Coq.Lists.List.
Import ListNotations.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.SortedList.
Require Import riscv.Words32Naive.
Require Import riscv.DefaultMemImpl32.
Require Import coqutil.Map.Empty_set_keyed_map.
Require Import coqutil.Map.Z_keyed_SortedListMap.
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

Unset Universe Minimization ToSet.

Open Scope Z_scope.

Notation RiscvMachine := (RiscvMachine Register MMIOAction).

Instance mmio_params: MMIO.parameters := { (* everything is inferred automatically *) }.

Existing Instance MinimalMMIOPrimitivesParams. (* needed because it's in a section *)

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

(* Eval vm_compute in compileFunc mmio_adder. *)

Definition mmio_adder_bytes: list byte := Eval vm_compute in main mmio_adder.


Require Import bedrock2.Examples.FE310CompilerDemo.
Time Definition swap_demo_byte: list byte := Eval vm_compute in main swap_chars_over_uart.

Module PrintAssembly.
  Import riscv.InstructionNotations.
  (* Eval vm_compute in compileFunc swap_chars_over_uart. *)
End PrintAssembly.

(* This example uses the memory only as instruction memory
   TODO make an example which uses memory to store data *)
Definition zeroedRiscvMachine: RiscvMachine := {|
  getRegs := map.empty;
  getPc := word.of_Z 0;
  getNextPc := word.of_Z 4;
  getMem := map.empty;
  getLog := nil;
|}.

Definition imemStart: word. Admitted. (* TODO *)

Definition initialRiscvMachine(imem: list MachineInt): RiscvMachine :=
  putProgram imem imemStart zeroedRiscvMachine.

Definition awesome_postcondition: trace -> Prop. Admitted.

Require bedrock2.WeakestPreconditionProperties.
Lemma WP_framework_is_awesome:
  exec map.empty swap_chars_over_uart nil map.empty map.empty
       (fun t m l => awesome_postcondition t).
Proof.
  eapply bedrock2.WeakestPreconditionProperties.sound_nil.
(* WeakestPrecondition.cmd (fun _ _ _ _ _  => False) *)
(*   swap_chars_over_uart [] map.empty map.empty (fun t _ _ => awesome_postcondition t) *)
Admitted.

Definition initialSwapMachine: RiscvMachine :=
  initialRiscvMachine (List.map encode (compileFunc swap_chars_over_uart)).

(* just to make sure all typeclass instances are available: *)
Definition mcomp_sat:
  OStateND RiscvMachine unit -> RiscvMachine -> (RiscvMachine -> Prop) -> Prop :=
  GoFlatToRiscv.mcomp_sat.

Lemma end2endDemo:
  runsToNonDet.runsTo (mcomp_sat (run1 RV32IM))
                      initialSwapMachine
                      (fun (finalL: RiscvMachine) => awesome_postcondition finalL.(getLog)).
Proof.
  (* TODO why does "eapply @exprImp2Riscv_correct" not work? *)
  unshelve epose proof (@exprImp2Riscv_correct _ _
    swap_chars_over_uart map.empty _ _ _ imemStart _ _ eq_refl _ _ _ _) as P;
    [..|eapply P].
  - cbv - [Z.lt]. (* TODO will need to tighten bounds... *) admit.
  - cbv. repeat constructor.
  - reflexivity.
  - reflexivity.
  - unfold initialSwapMachine, initialRiscvMachine, getMem.
    (* TODO relate putProgram to GoFlatToRiscv.program *) admit.
  - apply WP_framework_is_awesome.
Admitted.
