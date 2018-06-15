Require Import compiler.ExprImp.
Require Import riscv.util.BitWidths.
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

Require Import riscv.util.BitWidth32.

Local Notation RiscvMachine := (@RiscvMachine BitWidths32 (mem wXLEN) state).

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
  := putProgram listsum_bits $0 (initialRiscvMachine_without_instructions l).

Close Scope Z_scope.

Eval cbv in (map (@wordToNat 8) (initialRiscvMachine [1; 2; 3]).(machineMem)).

Definition run: nat -> RiscvMachine -> option unit * RiscvMachine :=
 @Run.run BitWidths32 Utility.MachineWidth32 (OState RiscvMachine) (OState_Monad _) _ _  .

Definition listsum_final(fuel: nat)(l: list nat): RiscvMachine :=
  snd (run fuel (initialRiscvMachine l)).

Definition listsum_res(fuel: nat)(l: list nat): word wXLEN :=
  getReg (listsum_final fuel l).(core).(registers) ExampleSrc.sumreg.

Eval vm_compute in (listsum_res 400 [4; 5; 3]).

(*
Definition initialize_with_wXLEN_list_H{Bw : BitWidths}(l: list (word wXLEN))
           (offset: word wXLEN) : Memory.mem :=
  fun (a: word wXLEN) =>
    if dec (#offset <= #a < #offset + (length l * wXLEN_in_bytes)
            /\ #a mod wXLEN_in_bytes = 0) then
      nth_error l (#(a ^- offset)  / wXLEN_in_bytes)
    else
      None.
*)

Definition in_range_dec: forall {w: nat} (addr: word w) (alignment start size: nat),
    Decidable (Memory.in_range addr alignment start size).
Proof.
  intros. unfold Memory.in_range. apply dec_and.
Defined.

Definition initialize_with_wXLEN_list_H{Bw : BitWidths}(l: list (word wXLEN))
           (offset: word wXLEN) : Memory.mem :=
  fun (a: word wXLEN) =>
    if dec (Memory.in_range a wXLEN_in_bytes #offset (wXLEN_in_bytes * length l)) then
      nth_error l (#(a ^- offset) / wXLEN_in_bytes)
    else
      None.

(*
Definition initialize_with_wXLEN_list_H{Bw : BitWidths}(l: list (word wXLEN))
           (offset: word wXLEN) : Memory.mem :=
  fun (a: word wXLEN) =>
    if dec (#offset <= #a) then
      nth_error l (#(a ^- offset) / wXLEN_in_bytes)
    else
      None.
 *)

Lemma invert_initialize_Some: forall l offset w a,
    Memory.read_mem a (initialize_with_wXLEN_list_H l offset) = Some w ->
    nth_error l (#(a ^- offset) / wXLEN_in_bytes) = Some w /\
    #offset <= #a /\
    #a mod 4 = 0.
Proof.
  intros. unfold Memory.read_mem, initialize_with_wXLEN_list_H in *.
  repeat (destruct_one_match_hyp; try discriminate).
  unfold Memory.in_range in *. clear E0. intuition idtac.
Qed.

(*
Lemma invert_initialize_Some': forall l offset w a,
    Memory.read_mem a (initialize_with_wXLEN_list_H l offset) = Some w ->
    nth_error l (#(a ^- offset) / wXLEN_in_bytes) = Some w /\
    #offset <= #a /\
    #a + wXLEN_in_bytes <= #offset + wXLEN_in_bytes * length l /\
    #a mod 4 = 0.
Proof.
  intros. unfold Memory.read_mem, initialize_with_wXLEN_list_H in *.
  repeat (destruct_one_match_hyp; try discriminate).
  assert (# (a ^- offset) / wXLEN_in_bytes < length l). {
    apply nth_error_Some. congruence.
  }
  
  repeat split; auto.
Qed.
 *)

Definition initialMemH(l: list nat): Memory.mem :=
  initialize_with_wXLEN_list_H (mk_input l) $input_base.

Definition evalH(fuel: nat)(l: list nat): option (state * Memory.mem) :=
 eval_stmt empty fuel empty (initialMemH l) ExampleSrc.listsum.

Definition listsum_res_H(fuel: nat)(l: list nat): option (word 32) :=
  match evalH fuel l with
  | Some (regs, m) => get regs ExampleSrc.sumreg
  | _ => None
  end.

Eval vm_compute in (listsum_res_H 40 [3; 7; 6]).

Lemma store_word_list_contains_initialize: forall words offset m,
    #offset mod 4 = 0 ->
    #offset + 4 * length words <= Memory.memSize m ->
    FlatToRiscv.containsMem (Memory.store_word_list words offset m)
                            (initialize_with_wXLEN_list_H words offset).
Proof.
  unfold FlatToRiscv.containsMem.
  unfold FlatToRiscv.loadWordwXLEN, wXLEN, wXLEN_in_bytes,
     BitWidths.bitwidth, BitWidths32.
  intros.
  unfold Memory.read_mem, initialize_with_wXLEN_list_H in H1.
  repeat (destruct_one_match_hyp; try discriminate).
  clear E0.
  unfold Memory.in_range in *.
  rewrite Memory.store_word_list_preserves_memSize.
  Memory.destruct_list_length.
  - apply FlatToRiscv.nth_error_nil_Some in H1. contradiction.
  - unfold wXLEN_in_bytes, BitWidths.bitwidth, BitWidths32 in *.
    (* TODO why doesn't omega work here? *)
    intuition (try (eapply le_trans; eassumption)).
    apply nth_error_nth with (d := $0) in H1. rewrite <- H1.
    pose proof pow2_wXLEN_4 as P. unfold wXLEN, BitWidths.bitwidth, BitWidths32 in P.
    apply Memory.loadWord_inside_store_word_list;
      unfold Memory.in_range;
      unfold Memory.valid_addr;
      intuition omega.
Qed.

Lemma memory_size_infJalMem:  Memory.memSize (w := wXLEN) infJalMem = memory_size.
Proof.
  pose proof @Memory.store_word_list_preserves_memSize as R.
  unfold infJalMem.
  unfold wXLEN, bitwidth, BitWidths.bitwidth, BitWidths32 in R|-*; rewrite R.
  unfold zero_mem, Memory.memSize, mem_is_Memory.
  apply const_mem_mem_size.
  - reflexivity.
  - change 32 with (10 + 22). rewrite Nat.pow_add_r.
    pose proof (one_le_pow2 22).
    replace memory_size with (memory_size * 1) by omega.
    forget (pow2 22) as x.
    apply Nat.mul_le_mono; cbv; omega.
Qed.  

Lemma memory_size_without_instructions: forall l,
  Memory.memSize (machineMem (initialRiscvMachine_without_instructions l)) = memory_size.
Proof.
  intros.
  unfold initialRiscvMachine_without_instructions, putProgram.
  cbv [machineMem with_pc with_nextPC with_machineMem].
  pose proof @Memory.store_word_list_preserves_memSize as R.
  unfold wXLEN, bitwidth, BitWidths.bitwidth, BitWidths32 in R|-*; rewrite R.
  apply memory_size_infJalMem.
Qed.

Lemma cons_length: forall (A: Type) (a: A) (l: list A),
    length (a :: l) = S (length l).
Proof.
  intros. reflexivity.
Qed.

(* Note: the high-level program also runs on a memory of size memory_size and also uses just
   32-bit words, so you might have overflows in the high-level program, and the compiler does
   not help you prevent these, but it provably does not introduce any new overflow or memory
   size problems. *)
Lemma listsum_compiled_correctly: forall l fuelH res,
    input_base + 4 * S (length l) <= memory_size ->
    listsum_res_H fuelH l = Some res ->
    exists fuelL, listsum_res fuelL l = res.
Proof.
  intros.
  unfold listsum_res_H, evalH in H0. destruct_one_match_hyp; try discriminate.
  destruct p as [finalRegsH finalMemH].
  unfold listsum_res, listsum_final.
  pose proof exprImp2Riscv_correct as Q.
  specialize Q with (sH := ExampleSrc.listsum)
                    (initialL := (initialRiscvMachine_without_instructions l)).
  unfold Pipeline.evalH in Q.
  edestruct Q as [fuelL P]; try eassumption.
  - cbv. reflexivity.
  - cbv. auto 20.
  - reflexivity.
  - match goal with
    | |- context [length ?x] => let r := eval cbv in (length x) in change (length x) with r
    end.
    rewrite memory_size_without_instructions.
    apply Nat.le_trans with (m := input_base).
    + cbv. omega.
    + unfold input_base, memory_size. omega.
  - match goal with
    | |- _ _ _ ?x => let x' := eval cbv in x in change x with x'
    end.
    unfold initialMemH, FlatToRiscv.mem_inaccessible.
    intros.
    apply invert_initialize_Some in H1. intuition idtac.
    unfold Memory.not_in_range.
    right.
    unfold input_base in *.
    unfold wXLEN, BitWidths32, BitWidths.bitwidth in *.
    assert (# (natToWord 32 512) = 512) as F by (abstract reflexivity).
    rewrite F in H1.
    omega.
  - unfold initialRiscvMachine_without_instructions, machineMem, initialMemH.
    unfold wXLEN, BitWidths32, BitWidths.bitwidth in *.
    apply store_word_list_contains_initialize; [ reflexivity | ].
    unfold mem, ListMemoryNatAddr.mem.
    rewrite memory_size_infJalMem.
    unfold mk_input.
    rewrite wordToNat_natToWord_idempotent'.
    + rewrite cons_length. rewrite map_length. exact H.
    + change 32 with (10 + 22). rewrite Nat.pow_add_r.
      pose proof (one_lt_pow2 21).
      replace input_base with (input_base * 1) by omega.
      forget (pow2 22) as x.
      apply Nat.mul_lt_mono; cbv; omega.
  - exists fuelL.
    unfold initialRiscvMachine, putProgram.
    apply P. apply H0.
Qed.

Print Assumptions listsum_compiled_correctly.

Definition sum_gallina(l: list nat): nat := List.fold_right plus 0 l.

Lemma hl_listsum_correct: forall l,
    exists fuel, listsum_res_H fuel l = Some (natToWord 32 (sum_gallina l)).
Proof.
  (* Future work: Proof framework to connect ExprImp programs with Gallina programs *)
Admitted.


Lemma listsum_will_run_correctly: forall l,
    input_base + 4 * S (length l) <= memory_size ->
    exists fuelL, listsum_res fuelL l = $(sum_gallina l).
Proof.
  intros.
  destruct (hl_listsum_correct l) as [fuelH E].
  refine (listsum_compiled_correctly l fuelH _ H E).
Qed.
