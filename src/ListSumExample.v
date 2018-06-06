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

Local Notation RiscvMachine := (@RiscvMachine RiscvBitWidths32 (mem wXLEN) state).

Definition memory_size: nat := 1024.
Definition instructionMemStart: nat := 0.
Definition input_base: nat := 512.


Module ExampleSrc.

  Import ExprImpNotations. (* only inside this module *)
  
  Definition n: var := 1.
  Definition i: var := 2.
  Definition sumreg: var := 3.
  Definition a: var := 4.

  (* Inputs:
     n: length of list, at address input_base
     A: list of 32-bit ints of length n, at address input_base + 4
   Output: in register 'sumreg'
   *)

  Example listsum: stmt :=
    sumreg <-- 0;
    n <-* Z.of_nat input_base;
    i <-- 0;
    while i < n do
      a <-* (Z.of_nat input_base + 4)%Z + 4 * i;
      sumreg <-- sumreg + a;
      i <-- i + 1
    done.

  Print listsum.

End ExampleSrc.

Print ExampleSrc.listsum.

(* Here we compile: exprImp2Riscv is the main compilation function *)
Definition listsum_riscv: list Instruction := exprImp2Riscv ExampleSrc.listsum.

Eval cbv in listsum_riscv.

Eval simpl in (List.length listsum_riscv).

Definition listsum_bits: list (word 32) := (map (fun i => ZToWord 32 (encode i)) listsum_riscv).

Eval cbv in listsum_bits.

Definition mk_input(l: list nat): list (word 32) :=
  (natToWord 32 (List.length l)) :: (List.map (natToWord 32) l).

Definition InfiniteJal: Instruction := Jal Register0 0.
Eval cbv in (encode InfiniteJal).

Definition infJalMem: list (word 8) :=
  Memory.store_word_list
    (List.repeat (ZToWord 32 (encode InfiniteJal)) (memory_size / 4))
    (natToWord 32 0)
    (ListMemory.zero_mem memory_size).
Eval cbv in infJalMem.

Definition initialRiscvMachineCore: @RiscvMachineCore _ state := {|
  registers := initialRegs;
  pc := $instructionMemStart;
  nextPC := $instructionMemStart ^+ $4;
  exceptionHandlerAddr := 4321;
|}.

Definition initialRiscvMachine_without_instructions(l: list nat): RiscvMachine := {|
    core := initialRiscvMachineCore;
    machineMem := Memory.store_word_list
                    (mk_input l)
                    (natToWord 32 input_base)
                    infJalMem
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
  getReg (listsum_final fuel l).(core).(registers) ExampleSrc.sumreg.

Eval vm_compute in (listsum_res 400 [4; 5; 3]).


Definition initialMemH(l: list nat): Memory.mem :=
  fun (a: word 32) => if dec (wordToNat a < input_base) then
                        None (* make inaccessible to protect instruction memory *)
                      else
                        nth_error (mk_input l) ((wordToNat a - input_base)  / 4).

Definition evalH(fuel: nat)(l: list nat): option (state * Memory.mem) :=
 eval_stmt empty fuel empty (initialMemH l) ExampleSrc.listsum.

Definition listsum_res_H(fuel: nat)(l: list nat): option (word 32) :=
  match evalH fuel l with
  | Some (regs, m) => get regs ExampleSrc.sumreg
  | _ => None
  end.

Eval vm_compute in (listsum_res_H 40 [3; 7; 6]).

(* Note: the high-level program also runs on a memory of size memory_size and also uses just
   32-bit words, so you might have overflows in the high-level program, and the compiler does
   not help you prevent these, but it provably does not introduce any new overflow or memory
   size problems. *)
Lemma listsum_compiled_correctly: forall l fuelH res,
    listsum_res_H fuelH l = Some res ->
    exists fuelL, listsum_res fuelL l = res.
Proof.
  intros.
  unfold listsum_res_H, evalH in H. destruct_one_match_hyp; try discriminate.
  destruct p as [finalRegsH finalMemH].
  unfold listsum_res, listsum_final.
  pose proof exprImp2Riscv_correct as Q.
  specialize Q with (sH := ExampleSrc.listsum)
                    (initialL := (initialRiscvMachine_without_instructions l)).
  unfold Pipeline.evalH in Q.
  edestruct Q as [fuelL P]; try eassumption.
  - change 14 with (8 + 6). rewrite Nat.pow_add_r.
    pose proof (zero_lt_pow2 6).
    forget (pow2 6) as x.
    apply lt_mul_mono; cbv; omega.
  - reflexivity.
  - match goal with
    | |- context [length ?x] => let r := eval cbv in (length x) in change (length x) with r
    end.
    unfold initialRiscvMachine_without_instructions, putProgram.
    cbv [machineMem with_pc with_nextPC with_machineMem].
    pose proof store_word_list_preserves_memSize as R.
    unfold wXLEN, bitwidth, RiscvBitWidths.bitwidth, RiscvBitWidths32 in R|-*; rewrite R.
    unfold infJalMem. rewrite R.
    unfold zero_mem, Memory.memSize, mem_is_Memory.
    rewrite const_mem_mem_size.
    + apply Nat.le_trans with (m := input_base).
      * cbv. omega.
      * unfold input_base, memory_size. omega.
    + reflexivity.
    + change 32 with (10 + 22). rewrite Nat.pow_add_r.
      pose proof (one_le_pow2 22).
      replace memory_size with (memory_size * 1) by omega.
      forget (pow2 22) as x.
      apply Nat.mul_le_mono; cbv; omega.
  - match goal with
    | |- _ _ _ ?x => let x' := eval cbv in x in change x with x'
    end.
    unfold initialMemH, FlatToRiscv.mem_inaccessible.
    intros. unfold Memory.read_mem in *.
    do 2 (destruct_one_match_hyp; try discriminate).
    unfold FlatToRiscv.not_in_range.
    right.
    unfold input_base in n.
    unfold wXLEN, RiscvBitWidths32, RiscvBitWidths.bitwidth in *.
    omega.
  - exists fuelL.
    unfold initialRiscvMachine, putProgram.
    apply P. apply H.
Qed.


Definition sum_gallina(l: list nat): nat := List.fold_right plus 0 l.

Lemma hl_listsum_correct: forall l,
    exists fuel, listsum_res_H fuel l = Some (natToWord 32 (sum_gallina l)).
Proof.
  (* Future work: Proof framework to connect ExprImp programs with Gallina programs *)
Admitted.


Lemma listsum_will_run_correctly: forall l,
    (* TODO: bound on length of l *)
    exists fuelL, listsum_res fuelL l = $(sum_gallina l).
Proof.
  intros.
  destruct (hl_listsum_correct l) as [fuelH E].
  apply (listsum_compiled_correctly l fuelH _ E).
Qed.
