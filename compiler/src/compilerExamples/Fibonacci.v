(*
Require Import Coq.Lists.List.
Import ListNotations.
Require bedrock2Examples.Demos.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
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
Require Import compiler.ZNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import bedrock2.Byte.
Require bedrock2.Hexdump.

Open Scope Z_scope.


Definition var: Set := Z.
Definition Reg: Set := Z.


Existing Instance DefaultRiscvState.


Definition fib_ExprImp(n: Z): cmd := Eval cbv in
  snd (snd (Demos.fibonacci n)).

(* This is what the bare AST looks like. For a more readable version with notations, see
   bedrock2/Demos.v
Print fib_ExprImp.
*)

Definition fib_H_res(fuel: nat)(n: Z): option word :=
  match (eval_cmd map.empty fuel map.empty map.empty (fib_ExprImp n)) with
  | Some (st, m) => map.get st Demos.Fibonacci.b
  | None => None
  end.


Goal fib_H_res 20 0 = Some (word.of_Z  1). reflexivity. Qed.
Goal fib_H_res 20 1 = Some (word.of_Z  1). reflexivity. Qed.
Goal fib_H_res 20 2 = Some (word.of_Z  2). reflexivity. Qed.
Goal fib_H_res 20 3 = Some (word.of_Z  3). reflexivity. Qed.
Goal fib_H_res 20 4 = Some (word.of_Z  5). reflexivity. Qed.
Goal fib_H_res 20 5 = Some (word.of_Z  8). reflexivity. Qed.
Goal fib_H_res 20 6 = Some (word.of_Z 13). reflexivity. Qed.

Instance flatToRiscvDef_params: FlatToRiscvDef.FlatToRiscvDef.parameters. refine ({|
  FlatToRiscvDef.FlatToRiscvDef.compile_ext_call _ _ _ := nil;
|}).
all: intros; simpl.
- cbv. discriminate.
- unfold FlatToRiscvDef.valid_instructions. intros. destruct H1.
Defined.

Notation RiscvMachine := MetricRiscvMachine.

Existing Instance coqutil.Map.SortedListString.map.
Existing Instance coqutil.Map.SortedListString.ok.

Instance pipeline_params: Pipeline.parameters := {
  Pipeline.ext_spec _ _  _ _ _ := False;
  Pipeline.M := OState RiscvMachine;
  Pipeline.PRParams := MetricMinimalMetricPrimitivesParams;
}.

Axiom TODO: forall {T: Type}, T.

Instance pipeline_assumptions: @Pipeline.assumptions pipeline_params := {
  Pipeline.mem_ok := _ ;
  Pipeline.locals_ok := _ ;
  Pipeline.funname_env_ok := _ ;
  Pipeline.PR := MetricMinimalSatisfiesMetricPrimitives;
  Pipeline.FlatToRiscv_hyps := TODO ;
  Pipeline.ext_spec_ok := TODO;
}.

Definition compileFunc: cmd -> list Instruction := ExprImp2Riscv.

Definition resVar := Demos.Fibonacci.b.

Definition fib_riscv0(n: Z): list Instruction :=
  compileFunc (fib_ExprImp n).

Module PrintFlatImp.
  Import FlatImp bopname.
  Eval vm_compute in (ExprImp2FlatImp0 (fib_ExprImp 6)).
End PrintFlatImp.

Time Definition fib6_riscv := Eval vm_compute in fib_riscv0 6.

Print fib6_riscv.

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Print fib6_riscv.
End PrintAssembly.

Definition fib6_bits: list word :=
  List.map (fun i => word.of_Z (encode i)) fib6_riscv.

(* Eval cbv in fib6_bits. *)

Definition fib6_bits_as_Z: list Z :=
  List.map (fun i => (encode i)) fib6_riscv.

(* Eval cbv in fib6_bits_as_Z. *)

(* This example uses the memory only as instruction memory
   TODO make an example which uses memory to store data *)
Definition zeroedRiscvMachine: RiscvMachine :=
{|
  getMachine := {|
    RiscvMachine.getRegs := map.empty;
    RiscvMachine.getPc := word.of_Z 0;
    RiscvMachine.getNextPc := word.of_Z 4;
    RiscvMachine.getMem := map.empty;
    RiscvMachine.getXAddrs := nil;
    RiscvMachine.getLog := nil;
  |};
  getMetrics := MetricLogging.EmptyMetricLog;
|}.

Definition initialRiscvMachine(imem: list MachineInt): RiscvMachine :=
  putProgram imem (word.of_Z 0) zeroedRiscvMachine.

Definition run: nat -> RiscvMachine -> option unit * RiscvMachine := Run.run RV32IM.

Definition testInitialMem := Eval vm_compute in (initialRiscvMachine fib6_bits_as_Z).(getMem).
(* Print testInitialMem. *)

Definition instructions_to_word8(insts: list Instruction): list Utility.byte :=
  List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) insts.

Definition fib6_as_word8: list Utility.byte := instructions_to_word8 fib6_riscv.

Definition fib6_as_bytes: list byte :=
  List.map (fun w => Byte.of_Z (word.unsigned w)) fib6_as_word8.

Module PrintBytes.
  Import bedrock2.Hexdump.
  Local Open Scope hexdump_scope.
  Set Printing Width 100.
  (* Save this to compiler/src/compilerExamples/Fibonacci.hex *)
  Goal True. let x := eval cbv in fib6_as_bytes in idtac x. Abort.
  (* Then:
  xxd -r -p < compiler/src/compilerExamples/Fibonacci.hex > compiler/src/compilerExamples/Fibonacci.bin
  riscv64-linux-gnu-ld --section-start=.data=0x20400000 --strip-all --format=binary --oformat=elf32-littleriscv compiler/src/compilerExamples/Fibonacci.bin -o compiler/src/compilerExamples/Fibonacci.elf
  riscv64-linux-gnu-objdump -D compiler/src/compilerExamples/Fibonacci.elf
  qemu-system-riscv32 -nographic -gdb tcp::1234 -machine sifive_e -S -kernel compiler/src/compilerExamples/Fibonacci.elf &
  riscv32-linux-gnu-gdb compiler/src/compilerExamples/Fibonacci.elf -ex 'set height unlimited' -ex 'set confirm off' -ex 'target remote localhost:1234' -ex 'disp/i $pc' -ex "break *0x$(riscv64-linux-gnu-objdump -D compiler/src/compilerExamples/Fibonacci.elf | grep unimp | tail -1 | cut -d: -f1)" -ex c -ex 'info registers' -ex 'quit'
  #shorter: riscv32-linux-gnu-gdb compiler/src/compilerExamples/Fibonacci.elf -ex 'target remote localhost:1234' -ex 'disp/i $pc'

  output:
  Breakpoint 1, 0x20400174 in ?? ()
  1: x/i $pc
  => 0x20400174:	unimp
  ra             0x8	0x8
  sp             0xd	0xd
  gp             0xd	0xd
  tp             0x6	0x6
  t0             0x0	0
  t1             0x1	1
  t2             0x0	0
  s0             0x6	0x6
  s1             0x6	6
  a0             0x0	0
  a1             0x5	5
  a2             0x8	8
  a3             0xd	13
  a4             0x8	8
  a5             0xd	13
  a6             0x5	5
  a7             0x1	1
  s2             0x6	6
  s3             0x0	0
  s4             0x0	0
  s5             0x0	0
  s6             0x0	0
  s7             0x0	0
  s8             0x0	0
  s9             0x0	0
  s10            0x0	0
  s11            0x0	0
  t3             0x0	0
  t4             0x0	0
  t5             0x0	0
  t6             0x0	0
  pc             0x20400174	0x20400174
  *)
End PrintBytes.

Definition fib6_final(fuel: nat): RiscvMachine :=
  match run fuel (initialRiscvMachine fib6_bits_as_Z) with
  | (answer, state) => state
  end.

Definition force_option(o: option word): word :=
  match o with
  | Some w => w
  | None => word.of_Z 0
  end.

Definition fib6_res(fuel: nat): word :=
  force_option (map.get (fib6_final fuel).(getRegs) resVar).

(* only uncomment this if you're sure there are no admits in the computational parts,
   and that no computations match on opaque proofs,
   otherwise this will eat all your memory *)

Eval vm_compute in (fib6_res 400).

(* If cbv and vm_compute block or better performance is needed, we can extract to Haskell:
Definition finalfibres: nat := wordToNat (fib6_L_res 400).
Require Extraction.
Extraction Language Haskell.
Set Warnings "-extraction-reserved-identifier".
Extraction "Fib6.hs" finalfibres.
 *)

(* 1st method: Run it *)
Lemma fib6_L_res_is_13_by_running_it: exists fuel, word.unsigned (fib6_res fuel) = 13.
  exists 400%nat.
  cbv.
  reflexivity.
Qed.

Lemma fib_H_res_value: fib_H_res 20 6 = Some (word.of_Z 13).
Proof. cbv. reflexivity. Qed.

Lemma enough_registers_for_fib6: enough_registers (fib_ExprImp 6).
Proof.
  cbv. intuition congruence.
Qed.

(* 2nd method: Prove it without running it on low level, but using the
   compiler correctness theorem *)
Lemma fib6_L_res_is_13_by_proving_it: exists fuel, word.unsigned (fib6_res fuel) = 13.
  unfold fib6_res. unfold fib6_final.
  pose proof @exprImp2Riscv_correct as P.
Abort.
(*
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
    discriminate.
    (*
    rewrite const_mem_mem_size.
    + cbv. congruence.
    + cbv. reflexivity.
    + match goal with
      | |- 0 <= ?a <= ?b => let a' := eval cbv in a in change a with a'
      end.
      cbv.
      split; congruence.
  *)
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
      | match ?x with _ => _ end = _  => destruct x eqn: E; [|discriminate]
      end.
      destruct p.
      etransitivity; [|exact R].
      assert (Some (m, m0) = Some (finalH, finalMH)) as A. {
        etransitivity; [symmetry|]. eassumption.
        clear -F.
        etransitivity; [|exact F].
        clear.
        (* reflexivity. TODO takes forever *)
        admit.
      }
      inversion A. subst.
      reflexivity.
      (*
      match type of R with
      | match ?x with _ => _ end = _  => replace x with (Some (finalH, finalMH)) in R
      end.
      assumption.
      *)
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
      (* apply f_equal. stack overflow *)
Admitted.

Print Assumptions fib6_L_res_is_13_by_proving_it.
 *)
*)
