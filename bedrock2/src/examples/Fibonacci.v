Require Import Coq.Lists.List.
Import ListNotations.
Require Import lib.LibTacticsMin.
Require Import bbv.Word.
Require Import compiler.Decidable.
Require Import compiler.Op.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import riscv.Riscv.
Require Import compiler.util.MyOmega.
Require Import riscv.util.Monads.
Require Import compiler.util.Common.
Require Import compiler.NameWithEq.
Require Import riscv.util.BitWidths.
Require        riscv.InstructionNotations.
Require Import riscv.ListMemory.
Require Import riscv.MinimalLogging.
Require Import riscv.Utility.
Require Import riscv.encode.Encode.
Require Import compiler.ZName.
Require Import riscv.util.BitWidth32.
Require Import riscv.MachineWidth32.
Require Import compiler.util.List_Map.
Require Import compiler.ZNameGen.

Open Scope Z_scope.

Definition var: Set := (@name ZName).
Definition Reg: Set := (@name ZName).

Existing Instance DefaultRiscvState.

Existing Instance FlatToRiscv.State_is_RegisterFile.

Definition var_a: var := 1.
Definition var_b: var := 2.
Definition var_c: var := 3.
Definition var_i: var := 4.

(*
a = 0
b = 1
i = 0
while i < n:
  c = a + b
  a = b
  b = c
  i = i + 1
*)

Definition fib_ExprImp(n: word wXLEN): stmt :=
  SSeq (SSet var_a (ELit $0)) (
  SSeq (SSet var_b (ELit $1)) (
  SSeq (SSet var_i (ELit $0)) (
  SWhile (EOp OLt (EVar var_i) (ELit n)) (
    SSeq (SSet var_c (EOp OPlus (EVar var_a) (EVar var_b))) (
    SSeq (SSet var_a (EVar var_b)) (
    SSeq (SSet var_b (EVar var_c)) (
    SSeq (SSet var_i (EOp OPlus (EVar var_i) (ELit $1)))
    SSkip))))))).

Definition state := (var -> option (word wXLEN)).

Existing Instance Pipeline.annoying_instance.

Definition fib_H_res(fuel: nat)(n: word wXLEN): option (word wXLEN) :=
  match (eval_stmt empty_map fuel empty_map Memory.no_mem (fib_ExprImp n)) with
  | Some (st, m) => get st var_b
  | None => None
  end.


Goal fib_H_res 20 $0 = Some $1. reflexivity. Qed.
Goal fib_H_res 20 $1 = Some $1. reflexivity. Qed.
Goal fib_H_res 20 $2 = Some $2. reflexivity. Qed.
Goal fib_H_res 20 $3 = Some $3. reflexivity. Qed.
Goal fib_H_res 20 $4 = Some $5. reflexivity. Qed.
Goal fib_H_res 20 $5 = Some $8. reflexivity. Qed.
Goal fib_H_res 20 $6 = Some $13. reflexivity. Qed.

Definition do_regalloc: bool := false.

Definition compileFunc: stmt -> list Instruction :=
  if do_regalloc then exprImp2Riscv_with_regalloc else exprImp2Riscv.

Definition fib_riscv0(n: word wXLEN): list Instruction :=
  compileFunc (fib_ExprImp n).

Definition fib6_riscv := Eval cbv in fib_riscv0 $6.

Print fib6_riscv.

Import riscv.InstructionNotations.

Print fib6_riscv.

Definition fib6_bits: list (word 32) :=
  List.map (fun i => ZToWord 32 (encode i)) fib6_riscv.

Eval cbv in fib6_bits.

(* This example uses the memory only as instruction memory
   TODO make an example which uses memory to store data *)
Definition zeroedRiscvMachineCore: RiscvMachineCore := {|
  registers := initialRegs;
  pc := $0;
  nextPC := $4;
  exceptionHandlerAddr := 3;
|}.

Definition zeroedRiscvMachine: RiscvMachine := {|
    core := zeroedRiscvMachineCore;
    machineMem := @zero_mem 32 ((length fib6_riscv + 1) * 4);
|}.

Definition initialRiscvMachine(imem: list (word 32)): RiscvMachine :=
  Minimal.putProgram imem $0 zeroedRiscvMachine.

Definition zeroedRiscvMachineL: RiscvMachineL := {|
    machine := zeroedRiscvMachine;
    log := nil;
|}.

Definition initialRiscvMachineL(imem: list (word 32)): RiscvMachineL :=
  putProgram imem $0 zeroedRiscvMachineL.

Definition run: nat -> RiscvMachine -> option unit * RiscvMachine :=
 @Run.run BitWidth32 MachineWidth32 (OState RiscvMachine) (OState_Monad _) _ _  .

Definition runL: nat -> RiscvMachineL -> option unit * RiscvMachineL :=
 @Run.run BitWidth32 MachineWidth32 (OState RiscvMachineL) (OState_Monad _) _ _  .

Definition fib6_L_final(fuel: nat): RiscvMachine :=
  snd (run fuel (initialRiscvMachine fib6_bits)).

Definition fib6_L_finalL(fuel: nat): RiscvMachineL :=
  snd (runL fuel (initialRiscvMachineL fib6_bits)).

Definition force_option(o: option (word wXLEN)): word wXLEN :=
  match o with
  | Some w => w
  | None => $0
  end.

Definition fib6_L_res(fuel: nat): word wXLEN :=
  force_option (get (fib6_L_final fuel).(core).(registers) var_b).

Definition fib6_L_resL(fuel: nat): word wXLEN :=
  force_option (get (fib6_L_finalL fuel).(machine).(core).(registers) var_b).

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
Lemma fib6_L_res_is_13_by_running_it: exists fuel, fib6_L_res fuel = $13.
  exists 400%nat.
  cbv.
  reflexivity.
Qed.

Lemma fib_H_res_value: fib_H_res 20 $6 = Some $13.
Proof. cbv. reflexivity. Qed.

Lemma enough_registers_for_fib6: enough_registers (fib_ExprImp $6).
Proof.
  cbv. auto 20.
Qed.

(* 2nd method: Prove it without running it on low level, but using the
   compiler correctness theorem *)
Lemma fib6_L_res_is_13_by_proving_it: exists fuel, fib6_L_res fuel = $13.
  unfold fib6_L_res. unfold fib6_L_final.
  pose proof @exprImp2Riscv_correct as P.
  assert (exists finalH,
             evalH empty_map 20 empty_map Memory.no_mem (fib_ExprImp $ (6)) = Some finalH) as F. {
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
    | |- (?a <= ?b)%nat => let a' := eval cbv in a in change a with a'(*;
                         let b' := eval cbv in b in change a with b'*)
    end.
    unfold zeroedRiscvMachine.
    cbv [machineMem zero_mem].
    unfold Memory.memSize, mem_is_Memory.
    rewrite const_mem_mem_size.
    + cbv. do 4 apply le_S. apply le_n.
    + cbv. reflexivity.
    + match goal with
      | |- (?a <= ?b)%nat => let a' := eval cbv in a in change a with a'
      end.
      change wXLEN with (9 + 23)%nat.
      rewrite Nat.pow_add_r.
      assert (0 < 2 ^ 23)%nat by (apply zero_lt_pow2). forget (2 ^ 23)%nat as p.
      cbv - [Nat.mul]. omega.
  - unfold FlatToRiscv.mem_inaccessible. intros.
    unfold Memory.no_mem, Memory.read_mem in H.
    destruct_one_match_hyp; discriminate.
  - unfold FlatToRiscv.containsMem, Memory.no_mem. intros.
    unfold Memory.read_mem in *.
    destruct_one_match_hyp; discriminate.
  - exists fuelL.
    unfold force_option, run, fib6_bits, initialRiscvMachine.
    unfold getReg, FlatToRiscv.State_is_RegisterFile, Map.get, List_Map in G.
    unfold evalL, execState in G.
    apply G. clear G.
    assert (forall T (a b: T), Some a = Some b -> a = b) as E. {
      introv R. inversion R. reflexivity.
    }
    pose proof fib_H_res_value as R.
    unfold fib_H_res in R.
    unfold evalH in F.
    match type of R with
    | match ?x with _ => _ end = _  => replace x with (Some (finalH, finalMH)) in R
    end.
    assumption.
Qed.    

Print Assumptions fib6_L_res_is_13_by_proving_it.
