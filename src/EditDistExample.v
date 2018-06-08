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
Require Import riscv.MinimalLogging.
Require riscv.Utility.
Require Import riscv.encode.Encode.
Require Import compiler.PipelineTest.
Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import compiler.NameGen.

Require Import riscv.RiscvBitWidths32.


Module ExampleSrc.

Import ExprImpNotations. (* only inside this module *)
  
Definition n: var := 1.
Definition m: var := 2.
Definition i: var := 3.
Definition j: var := 4.
Definition cost1: var := 5.
Definition cost2: var := 6.
Definition cost12: var := 7.
Definition mincost: var := 8.
Definition a: var := 9.
Definition b: var := 10.

Definition input_base := 0.

(* memory layout:
   Inputs:
     n: length of first string, at address input_base
     m: length of second string, at address input_base + 4
     A: first string, at address input_base + 8
     B: second string, at address input_base + 8 + 4n
        Each character is a 32-bit int, and the strings are not null-terminated
   Working memory:
     M: DP matrix ((n+1) x (m+1)), at address input_base + 8 + 4n + 4m
   Output: last entry of M, also loaded into register 'mincost'
*)

Notation "'&A[' i ]" := ((input_base + 8)%Z + 4 * i)%src.
Notation "'&B[' j ]" := ((input_base + 8)%Z + 4 * n + 4 * j)%src.
Notation "'&M[' i , j ]" := ((input_base + 8)%Z + 4 * (n + m + ((n + 1) * j) + i))%src.

Example edit_dist: stmt :=
  n <-* input_base;
  m <-* (input_base + 4);
  i <-- 0;
  while i < n + 1 do
    &M[i, 0] *<- i;
    i <-- i + 1
  done;
  j <-- 0;
  while j < m + 1 do
    &M[0, j] *<- j;
    i <-- 1;
    while i < n + 1 do
      cost1 <-* &M[i-1, j];
      cost1 <-- cost1 + 1;
      cost2 <-* &M[i, j-1];
      cost2 <-- cost2 + 1;
      cost12 <-* &M[i-1, j-1];
      a <-* &A[i-1];
      b <-* &B[j-1];
      If a == b then SSkip else cost12 <-- cost12 + 1 fi;
      mincost <-- cost1;
      If cost2 < mincost then mincost <-- cost2 fi;
      If cost12 < mincost then mincost <-- cost12 fi;
      &M[i, j] *<- mincost;
      i <-- i + 1
    done;
    j <-- j + 1
  done.

End ExampleSrc.

Fixpoint str_to_words(s: string): list (word 32) :=
  match s with
  | String c rest => (NToWord 32 (N_of_ascii c)) :: (str_to_words rest)
  | EmptyString => nil
  end.

Definition a_str: list (word 32) := str_to_words "RISCV".
Definition b_str: list (word 32) := str_to_words "CRISP".

Definition input: list (word 32) :=
  (natToWord 32 (List.length a_str)) :: (natToWord 32 (List.length b_str)) :: a_str ++ b_str.


(* exprImp2Riscv is the main compilation function *)
Definition editdist_riscv0: list Instruction :=
  exprImp2Riscv ExampleSrc.edit_dist.

Definition editdist_riscv: list Instruction := Eval cbv in editdist_riscv0.

Print editdist_riscv.

(* Problem: As we can see, this example requires 181 virtual registers, so we need a register
   allocator before we can run this example *)

Eval simpl in (List.length editdist_riscv).

Definition editdist_bits: list (word 32) :=
  Eval cbv in (map (fun i => ZToWord 32 (encode i)) editdist_riscv).

Print editdist_bits.

Definition initialDataMemory: list (word 32) :=
  input ++ repeat $4321 ((List.length a_str + 1) * (List.length b_str + 1)).

Definition instructionMemStart: nat := (List.length initialDataMemory) * 4.

Definition initialMemoryWords: list (word 32) := initialDataMemory ++ editdist_bits.

(* just enough memory because running examples in Coq is slow *)
Definition mem_size: nat := (List.length initialMemoryWords) * 4.

Eval cbv in mem_size.

Definition initialMemoryBytes: mem 32 :=
  (Memory.store_word_list initialMemoryWords (wzero 32) (zero_mem mem_size)).

Definition initialRiscvMachineCore: RiscvMachineCore := {|
  registers := initialRegs;
  pc := $instructionMemStart;
  nextPC := $instructionMemStart ^+ $4;
  exceptionHandlerAddr := 4321;
|}.

Definition initialRiscvMachine: RiscvMachine := {|
    core := initialRiscvMachineCore;
    machineMem := initialMemoryBytes;
|}.

Definition initialRiscvMachineL: RiscvMachineL := {|
    machine := initialRiscvMachine;
    log := nil;
|}.

Definition run: nat -> RiscvMachineL -> option unit * RiscvMachineL :=
 @Run.run RiscvBitWidths32 Utility.MachineWidth32 (OState RiscvMachineL) (OState_Monad _) _ _  .

Definition editdist_L_final(fuel: nat): RiscvMachineL :=
  snd (run fuel initialRiscvMachineL).

Definition editdist_L_res(fuel: nat): word wXLEN :=
  force_option ((editdist_L_final fuel).(machine).(core).(registers) ExampleSrc.mincost).

Definition editdist_L_trace(fuel: nat): Log :=
  (editdist_L_final fuel).(log).

(* Here we print the first few load/storeWord operations. Most of them are instructions, but
   there are also two (InvalidInstruction 5), which are the length of the first and second
   string being loaded. *)
Eval vm_compute in (editdist_L_trace 200).
