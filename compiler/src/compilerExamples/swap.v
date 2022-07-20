Require Import Coq.Lists.List.
Import ListNotations.
Require bedrock2Examples.Demos.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
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
Require Import compiler.MemoryLayout.
Require Import compiler.StringNameGen.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MetricRiscvMachine.
Require bedrock2.Hexdump.
Require Import bedrock2Examples.swap.
Require Import bedrock2Examples.stackalloc.
Require Import compilerExamples.SpillingTests.

Open Scope Z_scope.
Open Scope string_scope.
Open Scope ilist_scope.

Definition var: Set := Z.
Definition Reg: Set := Z.


Local Existing Instance DefaultRiscvState.

Axiom TODO: forall {T: Type}, T.

Local Instance funpos_env: map.map string Z := SortedListString.map _.

Definition compile_ext_call(posenv: funpos_env)(mypos stackoffset: Z)(s: FlatImp.stmt Z) :=
  match s with
  | FlatImp.SInteract _ fname _ =>
    if string_dec fname "nop" then
      [[Addi Register0 Register0 0]]
    else
      nil
  | _ => []
  end.

Notation RiscvMachine := MetricRiscvMachine.

Local Existing Instance coqutil.Map.SortedListString.map.
Local Existing Instance coqutil.Map.SortedListString.ok.

Definition main_stackalloc :=
  ("main", ([]: list String.string, []: list String.string,
     cmd.stackalloc "x" 4 (cmd.stackalloc "y" 4 (cmd.call [] "swap_swap" [expr.var "x"; expr.var "y"])))).

Definition allFuns: list Syntax.func := [swap; swap_swap; main_stackalloc; stacknondet; stackdisj; long1].

Definition e := map.putmany_of_list allFuns map.empty.

(* stack grows from high addreses to low addresses, first stack word will be written to
   (stack_pastend-8), next stack word to (stack_pastend-16) etc *)
Definition stack_pastend: Z := 2048.

Lemma f_equal2: forall {A B: Type} {f1 f2: A -> B} {a1 a2: A},
    f1 = f2 -> a1 = a2 -> f1 a1 = f2 a2.
Proof. intros. congruence. Qed.

Lemma f_equal3: forall {A B C: Type} {f1 f2: A -> B -> C} {a1 a2: A} {b1 b2: B},
    f1 = f2 -> a1 = a2 -> b1 = b2 -> f1 a1 b1 = f2 a2 b2.
Proof. intros. congruence. Qed.

Lemma f_equal3_dep: forall {A B C: Type} {f1 f2: A -> B -> C} {a1 a2: A} {b1 b2: B},
    f1 = f2 -> a1 = a2 -> b1 = b2 -> f1 a1 b1 = f2 a2 b2.
Proof. intros. congruence. Qed.


Local Instance RV32I_bitwidth: FlatToRiscvCommon.bitwidth_iset 32 RV32I.
Proof. reflexivity. Qed.

Definition swap_asm: list Instruction.
  let r := eval cbv in (compile compile_ext_call e) in set (res := r).
  match goal with
  | res := Success (?x, _, _) |- _ => exact x
  end.
Defined.

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Goal True. let r := eval unfold swap_asm in swap_asm in idtac (* r *). Abort.
  (*
  swap_swap:
     addi    x2, x2, -20   // decrease sp
     sw      x2, x1, 8     // save ra
     sw      x2, x3, 0     // save registers modified by swap_swap
     sw      x2, x4, 4
     lw      x3, x2, 12    // load args
     lw      x4, x2, 16
     sw      x2, x3, -8    // store args for first call to swap
     sw      x2, x4, -4
     jal     x1, 36        // first call to swap
     sw      x2, x3, -8    // store args for second call to swap
     sw      x2, x4, -4
     jal     x1, 24        // second call to swap
     lw      x3, x2, 0     // restore registers modified by swap_swap
     lw      x4, x2, 4
     lw      x1, x2, 8     // load ra
     addi    x2, x2, 20    // increase sp
     jalr    x0, x1, 0     // return

  swap:
     addi    x2, x2, -28   // decrease sp
     sw      x2, x1, 16    // save ra
     sw      x2, x5, 0     // save registers modified by swap
     sw      x2, x6, 4
     sw      x2, x3, 8
     sw      x2, x4, 12
     lw      x3, x2, 20    // load args
     lw      x4, x2, 24
     lw      x5, x4, 0     // body of swap
     lw      x6, x3, 0
     sw      x4, x6, 0
     sw      x3, x5, 0
     lw      x5, x2, 0     // restore registers modified by swap
     lw      x6, x2, 4
     lw      x3, x2, 8
     lw      x4, x2, 12
     lw      x1, x2, 16    // restore ra
     addi    x2, x2, 28    // increase sp
     jalr    x0, x1, 0     // return

  stacknondet:
     addi    x2, x2, -56
     sw      x2, x1, 44
     sw      x2, x5, 4
     sw      x2, x6, 8
     sw      x2, x7, 12
     sw      x2, x3, 16
     sw      x2, x8, 20
     sw      x2, x9, 24
     sw      x2, x10, 28
     sw      x2, x11, 32
     sw      x2, x12, 36
     sw      x2, x4, 40
     addi    x5, x2, 0
     lw      x6, x5, 0
     addi    x7, x0, 8
     srl     x3, x6, x7
     addi    x8, x0, 3
     add     x9, x3, x8
     addi    x10, x0, 42
     sb      x9, x10, 0
     lw      x11, x5, 0
     addi    x12, x0, 8
     srl     x4, x11, x12
     sw      x2, x3, 48
     sw      x2, x4, 52
     lw      x5, x2, 4
     lw      x6, x2, 8
     lw      x7, x2, 12
     lw      x3, x2, 16
     lw      x8, x2, 20
     lw      x9, x2, 24
     lw      x10, x2, 28
     lw      x11, x2, 32
     lw      x12, x2, 36
     lw      x4, x2, 40
     lw      x1, x2, 44
     addi    x2, x2, 56
     jalr    x0, x1, 0

  stackdisj:
     addi    x2, x2, -28
     sw      x2, x1, 16
     sw      x2, x3, 8
     sw      x2, x4, 12
     addi    x3, x2, 4
     addi    x4, x2, 0
     sw      x2, x3, 20
     sw      x2, x4, 24
     lw      x3, x2, 8
     lw      x4, x2, 12
     lw      x1, x2, 16
     addi    x2, x2, 28
     jalr    x0, x1, 0

  main:
     addi    x2, x2, -20   // decrease sp
     sw      x2, x1, 16    // save ra
     sw      x2, x3, 8     // save registers modified by main
     sw      x2, x4, 12
     addi    x3, x2, 4     // first stackalloc invocation returns sp+4
     addi    x4, x2, 0     // second stackalloc invocation returns sp
     sw      x2, x3, -8    // store args for call to swap_swap
     sw      x2, x4, -4
     jal     x1, -380      // call swap_swap
     lw      x3, x2, 8     // restore registers modified by main
     lw      x4, x2, 12
     lw      x1, x2, 16    // restore ra
     addi    x2, x2, 20    // increase sp
     jalr    x0, x1, 0     // return
  *)
End PrintAssembly.

Definition swap_as_bytes: list Byte.byte := instrencode swap_asm.

Module PrintBytes.
  Import bedrock2.Hexdump.
  Local Open Scope hexdump_scope.
  Set Printing Width 100.
  Goal True. let x := eval cbv in swap_as_bytes in idtac (* x *). Abort.
End PrintBytes.
