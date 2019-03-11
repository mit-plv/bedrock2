Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.SortedList.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Empty_set_keyed_map.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import riscv.Utility.Monads.
Require Import compiler.util.Common.
Require        riscv.Utility.InstructionNotations.
Require Import riscv.Platform.MinimalMMIO.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.Encode.
Require Import coqutil.Map.SortedList.
Require Import compiler.ZNameGen.
Require Import riscv.Utility.InstructionCoercions.
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
  Import riscv.Utility.InstructionNotations.
  (* Eval vm_compute in compileFunc swap_chars_over_uart. *)
End PrintAssembly.

Definition zeroedRiscvMachine: RiscvMachine := {|
  getRegs := map.empty;
  getPc := word.of_Z 0;
  getNextPc := word.of_Z 4;
  getMem := map.empty;
  getLog := nil;
|}.

Definition imemStart: word. Admitted. (* TODO *)
Axiom imemStart_div4: word.unsigned imemStart mod 4 = 0.

Definition initialRiscvMachine(imem: list MachineInt): RiscvMachine :=
  putProgram imem imemStart zeroedRiscvMachine.

Require bedrock2.WeakestPreconditionProperties.

Local Instance ext_spec_Proper :   forall
    (trace : list
               (mem * actname * list Semantics.word *
                (mem * list Semantics.word))) (m : mem)
    (act : actname) (args : list Semantics.word),
  Morphisms.Proper
    (Morphisms.respectful
       (Morphisms.pointwise_relation mem
          (Morphisms.pointwise_relation (list Semantics.word) Basics.impl))
       Basics.impl) (ext_spec trace m act args).
Admitted.

Definition initialSwapMachine: RiscvMachine :=
  initialRiscvMachine (List.map encode (compileFunc swap_chars_over_uart)).

(* just to make sure all typeclass instances are available: *)
Definition mcomp_sat:
  OStateND RiscvMachine unit -> RiscvMachine -> (RiscvMachine -> Prop) -> Prop :=
  GoFlatToRiscv.mcomp_sat.

Definition unchecked_store_program(addr: word)(p: list Instruction)(m: mem): mem :=
  unchecked_store_byte_tuple_list addr (List.map (LittleEndian.split 4) (List.map encode p)) m.

Lemma store_program_empty: forall prog addr,
    GoFlatToRiscv.program addr prog (unchecked_store_program addr prog map.empty).
Proof.
  induction prog; intros.
  - cbv. auto.
  - cbv [GoFlatToRiscv.program]. simpl.
    do 2 eexists. split; [|split].
Admitted.


Lemma end2endDemo:
  runsToNonDet.runsTo (mcomp_sat (run1 RV32IM))
                      initialSwapMachine
                      (fun (finalL: RiscvMachine) =>  (fun _ => True) finalL.(getLog)).
Proof.
  (* TODO why does "eapply @exprImp2Riscv_correct" not work? *)
  unshelve epose proof (@exprImp2Riscv_correct _ _
    swap_chars_over_uart map.empty _ _ _ _ _ eq_refl _ _ _ _) as P;
    [..|eapply P].
  - cbv - [Z.lt]. lia.
  - cbv. repeat constructor.
  - reflexivity.
  - reflexivity.
  - exact imemStart_div4.
  - cbv [initialSwapMachine initialRiscvMachine getMem putProgram zeroedRiscvMachine
         getMem withPc withNextPc withMem].
    unfold Separation.sep. do 2 eexists; split; [ | split; [|reflexivity] ].
    1: apply map.split_empty_r; reflexivity.
    apply store_program_empty.
  - eapply bedrock2.WeakestPreconditionProperties.sound_nil.
    eapply bedrock2.Examples.FE310CompilerDemo.swap_chars_over_uart_correct.
Qed.
Print Assumptions end2endDemo.
