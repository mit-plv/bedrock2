Require Import Coq.Lists.List.
Import ListNotations.
Require bedrock2.Examples.Demos.
Require Import bedrock2.Basic_bopnames.
Require Import lib.LibTacticsMin.
Require Import riscv.util.Word.
Require Import compiler.Decidable.
Require Import compiler.Op.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import compiler.util.MyOmega.
Require Import riscv.util.Monads.
Require Import compiler.util.Common.
Require Import compiler.Decidable.
Require Import riscv.util.BitWidths.
Require        riscv.InstructionNotations.
Require Import riscv.ListMemory.
Require Import riscv.MinimalLogging.
Require Import riscv.Utility.
Require Import riscv.Encode.
Require Import riscv.util.BitWidth32.
Require Import riscv.MachineWidth32.
Require Import compiler.FlatToRiscv32Proofs.
Require Import compiler.FlatToRiscv32Specifics.
Require Import compiler.util.List_Map.
Require Import compiler.ZNameGen.
Require Import riscv.InstructionCoercions.

Open Scope Z_scope.


Definition var: Set := Z.
Definition Reg: Set := Z.

Existing Instance MachineWidth32.MachineWidth32.

Existing Instance DefaultRiscvState.

Existing Instance FlatToRiscv.State_is_RegisterFile.


Definition fib_ExprImp(n: Z): cmd := Eval cbv in
  snd (snd (Demos.fibonacci (bops := (@Basic_bopnames.BasicALU Demos.BasicALU_params)) n)).

(* This is what the bare AST looks like. For a more readable version with notations, see
   bedrock2/Demos.v *)
Print fib_ExprImp.

Definition state := (var -> option word).

Definition name := Z.

Instance fooo: MapFunctions name (list name * list name * cmd). Admitted.

Definition fib_H_res(fuel: nat)(n: Z): option word :=
  match (eval_cmd empty_map fuel empty_map Memory.no_mem (fib_ExprImp n)) with
  | Some (st, m) => Map.get st Demos.Fibonacci.b
  | None => None
  end.


Goal fib_H_res 20 0 = Some (ZToWord 32  1). reflexivity. Qed.
Goal fib_H_res 20 1 = Some (ZToWord 32  1). reflexivity. Qed.
Goal fib_H_res 20 2 = Some (ZToWord 32  2). reflexivity. Qed.
Goal fib_H_res 20 3 = Some (ZToWord 32  3). reflexivity. Qed.
Goal fib_H_res 20 4 = Some (ZToWord 32  5). reflexivity. Qed.
Goal fib_H_res 20 5 = Some (ZToWord 32  8). reflexivity. Qed.
Goal fib_H_res 20 6 = Some (ZToWord 32 13). reflexivity. Qed.

Definition do_regalloc: bool := false.

Definition resVar := Demos.Fibonacci.b.

Definition compileFunc: cmd -> list Instruction :=
  if do_regalloc then (exprImp2Riscv_with_regalloc Lw Sw resVar) else (exprImp2Riscv Lw Sw).

Definition fib_riscv0(n: Z): list Instruction :=
  compileFunc (fib_ExprImp n).

Definition fib6_riscv := Eval cbv in fib_riscv0 6.

Print fib6_riscv.

Module PrintAssembly.
  Import riscv.InstructionNotations.
  Print fib6_riscv.
End PrintAssembly.

Definition fib6_bits: list word :=
  List.map (fun i => ZToWord 32 (encode i)) fib6_riscv.

Eval cbv in fib6_bits.

Definition fib6_bits_as_Z: list Z :=
  List.map (fun i => (encode i)) fib6_riscv.

Eval cbv in fib6_bits_as_Z.

(* This example uses the memory only as instruction memory
   TODO make an example which uses memory to store data *)
Definition zeroedRiscvMachineCore: RiscvMachineCore := {|
  registers := initialRegs;
  pc := ZToWord 32 0;
  nextPC := (ZToWord 32 4);
  exceptionHandlerAddr := 3;
|}.

Definition zeroedRiscvMachine: RiscvMachine := {|
    core := zeroedRiscvMachineCore;
    machineMem := @zero_mem ((Memory.Zlength fib6_riscv + 1) * 4);
|}.

Definition initialRiscvMachine(imem: list word): RiscvMachine :=
  Minimal.putProgram imem (ZToWord 32 0) zeroedRiscvMachine.

Definition zeroedRiscvMachineL: RiscvMachineL := {|
    machine := zeroedRiscvMachine;
    log := nil;
|}.

Definition initialRiscvMachineL(imem: list word): RiscvMachineL :=
  putProgram imem (ZToWord 32 0) zeroedRiscvMachineL.

Definition run: nat -> RiscvMachine -> option unit * RiscvMachine :=
 @Run.run BitWidth32 _ MachineWidth32 (OState RiscvMachine) (OState_Monad _) _ _  .

Definition runL: nat -> RiscvMachineL -> option unit * RiscvMachineL :=
 @Run.run BitWidth32 _ MachineWidth32 (OState RiscvMachineL) (OState_Monad _) _ _  .

Definition fib6_L_final(fuel: nat): RiscvMachine :=
  snd (run fuel (initialRiscvMachine fib6_bits)).

Definition fib6_L_finalL(fuel: nat): RiscvMachineL :=
  snd (runL fuel (initialRiscvMachineL fib6_bits)).

Definition force_option(o: option word): word :=
  match o with
  | Some w => w
  | None => ZToWord 32 0
  end.

Definition fib6_L_res(fuel: nat): word :=
  force_option (Map.get (fib6_L_final fuel).(core).(registers) resVar).

Definition fib6_L_resL(fuel: nat): word :=
  force_option (Map.get (fib6_L_finalL fuel).(machine).(core).(registers) resVar).

Definition fib6_L_trace(fuel: nat): Log :=
  (fib6_L_finalL fuel).(log).

(* only uncomment this if you're sure there are no admits in the computational parts,
   and that no computations match on opaque proofs,
   otherwise this will eat all your memory *)

Eval cbv in (fib6_L_trace 1000).
Eval cbv in (length (fib6_L_trace 1000)).

Eval cbv in (fib6_L_res 400).

(* If cbv and vm_compute block or better performance is needed, we can extract to Haskell:
Definition finalfibres: nat := wordToNat (fib6_L_res 400).
Require Extraction.
Extraction Language Haskell.
Set Warnings "-extraction-reserved-identifier".
Extraction "Fib6.hs" finalfibres.
 *)

(* 1st method: Run it *)
Lemma fib6_L_res_is_13_by_running_it: exists fuel, uwordToZ (fib6_L_res fuel) = 13.
  exists 400%nat.
  cbv.
  reflexivity.
Qed.

Lemma fib_H_res_value: fib_H_res 20 6 = Some (ZToWord 32 13).
Proof. cbv. reflexivity. Qed.

Lemma enough_registers_for_fib6: enough_registers (fib_ExprImp 6).
Proof.
  cbv. auto 20.
Qed.

(* 2nd method: Prove it without running it on low level, but using the
   compiler correctness theorem *)
Lemma fib6_L_res_is_13_by_proving_it: exists fuel, uwordToZ (fib6_L_res fuel) = 13.
  unfold fib6_L_res. unfold fib6_L_final.
  pose proof @exprImp2Riscv_correct as P.
  assert (exists finalH,
    evalH Lw Sw empty_map 20 empty_map Memory.no_mem (fib_ExprImp 6)
    = Some finalH) as F. {
    eexists. reflexivity.
  }
  destruct F as [ [finalH finalMH ] F ].
  specialize P with (2 := enough_registers_for_fib6).
  specialize P with (4 := F).
  specialize P with (initialL := zeroedRiscvMachine).
  edestruct P as [fuelL G].
  - cbv. reflexivity.
  - reflexivity.
  - match goal with
    | |- ?a <= ?b => let a' := eval cbv in a in change a with a'(*;
                         let b' := eval cbv in b in change a with b'*)
    end.
    unfold zeroedRiscvMachine.
    cbv [machineMem zero_mem].
    unfold Memory.memSize, mem_is_Memory.
    rewrite const_mem_mem_size.
    + cbv. congruence.
    + cbv. reflexivity.
    + match goal with
      | |- 0 <= ?a <= ?b => let a' := eval cbv in a in change a with a'
      end.
      cbv.
      split; congruence.
  - unfold FlatToRiscv.mem_inaccessible. intros.
    unfold Memory.no_mem, Memory.read_mem in H.
    destruct_one_match_hyp; discriminate.
  - unfold FlatToRiscvInvariants.containsMem, Memory.no_mem. intros.
    unfold Memory.read_mem in *.
    destruct_one_match_hyp; discriminate.
  - exists fuelL.
    specialize G with (resVar := resVar) (res := (ZToWord 32 13)).
    match type of G with
      | ?A -> _ => assert A as x; [|specialize (G x); clear x]
    end.
    + pose proof fib_H_res_value as R.
      unfold fib_H_res in R.
      unfold evalH in F.
      match type of R with
      | match ?x with _ => _ end = _  => replace x with (Some (finalH, finalMH)) in R
      end.
      assumption.
    + apply (f_equal uwordToZ) in G.
      rewrite uwordToZ_ZToWord in G.
      change (13 mod 2 ^ 32) with 13 in G.
      rewrite <- G; clear G.
      apply f_equal.
      unfold force_option.
      unfold getReg, FlatToRiscv.State_is_RegisterFile.
      change ZToReg with (ZToWord 32).
      apply (f_equal force_option).
      change (@word Basic32Semantics.Basic32Semantics) with (RecordWord.word 32) in *.
      match goal with
        | |- ?M ?A resVar = ?M ?B resVar => replace A with B; [reflexivity|]
      end.
      apply f_equal.
      apply f_equal.
      unfold evalL, execState.
      apply f_equal.
      unfold run.
      apply f_equal.
      unfold initialRiscvMachine.
      apply f_equal.
      reflexivity.
Qed.

Print Assumptions fib6_L_res_is_13_by_proving_it.
