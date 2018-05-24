Require Import compiler.ExprImp.
Require Import riscv.RiscvBitWidths.
Require Import compiler.Common.
Require compiler.ExprImpNotations.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import bbv.Word.
Require Import compiler.Common.
Require Import compiler.Pipeline.
Require Import riscv.Riscv.
Require Import riscv.InstructionCoercions.
Require Import riscv.ListMemory.
Require Import riscv.Minimal.
Require riscv.Utility.
Require Import riscv.encode.Encode.
Require Import compiler.PipelineTest.
Require Import compiler.NameGen.

Require Import riscv.RiscvBitWidths32.


Module ExampleSrc.

Import ExprImpNotations. (* only inside this module *)
  
Definition n: var := 1.
Definition i: var := 2.
Definition sumreg: var := 3.
Definition a: var := 4.


Definition input_base: Z := 512.

(* Inputs:
     n: length of list, at address input_base
     A: list of 32-bit ints of length n, at address input_base + 4
   Output: in register 'sumreg'
*)

Example listsum: stmt :=
  sumreg <-- 0;
  n <-* input_base;
  i <-- 0;
  while i < n do
    a <-* (input_base + 4)%Z + 4 * i;
    sumreg <-- sumreg + a;
    i <-- i + 1
  done.

End ExampleSrc.

(* Here we compile: exprImp2Riscv is the main compilation function *)
Definition listsum_riscv: list Instruction := Eval cbv in exprImp2Riscv ExampleSrc.listsum.

Print listsum_riscv.

Eval simpl in (List.length listsum_riscv).

Definition listsum_bits: list (word 32) :=
  Eval cbv in (map (fun i => ZToWord 32 (encode i)) listsum_riscv).

Print listsum_bits.

Definition mk_input(l: list nat): list (word 32) :=
  (natToWord 32 (List.length l)) :: (List.map (natToWord 32) l).

Definition InfiniteJal: Instruction := Jal Register0 0.

Eval cbv in (encode InfiniteJal).

Definition initialMem_without_instructions(l: list nat): list (word 32) :=
  List.repeat (ZToWord 32 (encode InfiniteJal)) (Z.to_nat ExampleSrc.input_base / 4) ++ mk_input l.


Definition instructionMemStart: nat := 0.

Definition initialRiscvMachineCore: RiscvMachineCore := {|
  registers := initialRegs;
  pc := $instructionMemStart;
  nextPC := $instructionMemStart ^+ $4;
  exceptionHandlerAddr := 4321;
|}.

Definition initialRiscvMachine_without_instructions(l: list nat): RiscvMachine := {|
    core := initialRiscvMachineCore;
    machineMem := Memory.store_word_list
                    (initialMem_without_instructions l)
                    (natToWord 32 0)
                    (ListMemory.zero_mem (Z.to_nat ExampleSrc.input_base + 4 * length (mk_input l))%nat)
|}.

Definition initialRiscvMachine(l: list nat): RiscvMachine
  := putProgram listsum_bits (initialRiscvMachine_without_instructions l).

Close Scope Z_scope.

Eval cbv in (map (@wordToNat 8) (initialRiscvMachine [1; 2; 3]).(machineMem)).

Definition run: nat -> RiscvMachine -> option unit * RiscvMachine :=
 @Run.run RiscvBitWidths32 Utility.MachineWidth32 (OState RiscvMachine) (OState_Monad _) _ _  .

Definition listsum_final(fuel: nat)(l: list nat): RiscvMachine :=
  snd (run fuel (initialRiscvMachine l)).

Definition listsum_res(fuel: nat)(l: list nat): word wXLEN :=
  (listsum_final fuel l).(core).(registers) ExampleSrc.sumreg.

Eval vm_compute in (listsum_res 400 [4; 5; 3]).
