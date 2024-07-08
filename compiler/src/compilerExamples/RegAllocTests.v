Require Import bedrock2.NotationsCustomEntry.
Require Import Coq.Lists.List.
Import ListNotations.
Require bedrock2Examples.Demos.
Require Import coqutil.Decidable.
Require Import bedrock2.NotationsCustomEntry coqutil.Macros.WithBaseName.
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

Open Scope Z_scope.
Open Scope string_scope.
Open Scope ilist_scope.

(* ********************************************************* *)
(* Preliminaries *)
(* ********************************************************* *)

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

Definition main_stackalloc := func! {
  stackalloc 4 as x; stackalloc 4 as y; swap_swap(x, y) }.


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




(* ********************************************************* *)
(* Tests *)
(* ********************************************************* *)

Definition swap := func! (a, b) {
  t = load(b);
  store(b, load(a));
  store(a, t)
}.

(* Based on `long1` from compilerExamples/SpillingTests.v *)
(* Expected to fail, since too many `reg` variables are live simultaneously *)
Definition too_many_regs := func! (reg_a0, reg_b0) ~> (reg_a19, reg_b19) {
  (* TODO once spilling is improved, test that it still works if these two lines are removed
     (currently the test that all resnames are <32 fails if these two lines are removed) *)
  reg_a19 = $0;
  reg_b19 = $0;

  swap(reg_a0, reg_b0);
  reg_a1 = reg_a0 + reg_b0 * reg_b0;
  swap(reg_a1, reg_b0);
  reg_a12 = reg_a1 - reg_a0 - reg_b0;
  reg_b12 = reg_a1 + reg_a12 * reg_b0;
  reg_a5 = reg_a12 * reg_b12;
  reg_a9 = reg_a5 - reg_a0 - reg_b0;
  reg_a4 = reg_a1;
  reg_b3 = reg_a4 + reg_a12 * reg_b0;
  reg_b4 = reg_a4;
  reg_a10 = reg_a1 - reg_a0 - reg_b4;
  reg_b12 = reg_a1 + reg_a12 * reg_b0;
  reg_a3 = reg_a1;
  reg_a6 = reg_a10 + reg_b12;
  reg_a15 = reg_a3 - reg_a0 - reg_b0;
  reg_a2 = reg_a1;
  reg_b12 = reg_a2 + reg_a12 * reg_b0;
  reg_a11 = reg_a10 - reg_a0 - reg_b0;
  reg_b5 = reg_a1;
  reg_b4 = reg_a6 + reg_a12 * reg_b5;
  reg_a2 = reg_a11 - reg_a0 - reg_b0;
  reg_b12 = reg_a1 + reg_a12 * reg_b0;
  reg_a16 = reg_a12 - reg_a0 - reg_b0;
  reg_a7 = reg_a2;
  reg_b14 = reg_a7 + reg_a12 * reg_b0;
  reg_a13 = reg_b4;
  reg_a17 = $2;
  reg_b6 = $33;
  reg_a12 = reg_a13 - reg_a17 - reg_b6;
  reg_b12 = reg_a1 + reg_a12 * reg_b0;
  reg_a18 = $18;
  reg_b19 = $19;
  reg_a17 = reg_a1 - reg_a18 - reg_b19;
  reg_b12 = reg_a1 + reg_a9 * reg_b0;
  reg_a14 = $14;
  reg_a12 = reg_a14 - reg_a0 - reg_b0;
  reg_a8 = reg_b12;
  reg_b13 = reg_a8 + reg_a12 * reg_b0;
  reg_a12 = reg_a1 - reg_a0 - reg_b0;
  reg_b2 = reg_a1 + reg_a12 * reg_b0;
  reg_a18 = reg_a1 - reg_a0 - reg_b0;
  reg_b16 = $23;
  reg_b12 = reg_a15 + reg_a8 * reg_b16;
  reg_a12 = reg_a1 - reg_a0 - reg_b3;
  reg_b12 = reg_a1 + reg_a12 * reg_b0;

  reg_a19 = reg_a1 - reg_a0 - reg_b0;
  reg_b19 = reg_a9 + reg_a7 * reg_b0;

  reg_b0 = reg_b0 + reg_a1;
  reg_b0 = reg_b0 + reg_a12;
  reg_b0 = reg_b0 + reg_b12;
  reg_b0 = reg_b0 + reg_a5;
  reg_b0 = reg_b0 + reg_a9;
  reg_b0 = reg_b0 + reg_a4;
  reg_b0 = reg_b0 + reg_b3;
  reg_b0 = reg_b0 + reg_b4;
  reg_b0 = reg_b0 + reg_a10;
  reg_b0 = reg_b0 + reg_b12;
  reg_b0 = reg_b0 + reg_a3;
  reg_b0 = reg_b0 + reg_a6;
  reg_b0 = reg_b0 + reg_a15;
  reg_b0 = reg_b0 + reg_a2;
  reg_b0 = reg_b0 + reg_b12;
  reg_b0 = reg_b0 + reg_a11;
  reg_b0 = reg_b0 + reg_b5;
  reg_b0 = reg_b0 + reg_b4;
  reg_b0 = reg_b0 + reg_a2;
  reg_b0 = reg_b0 + reg_b12;
  reg_b0 = reg_b0 + reg_a16;
  reg_b0 = reg_b0 + reg_a7;
  reg_b0 = reg_b0 + reg_b14;
  reg_b0 = reg_b0 + reg_a13;
  reg_b0 = reg_b0 + reg_a17;
  reg_b0 = reg_b0 + reg_b6;
  reg_b0 = reg_b0 + reg_a12;
  reg_b0 = reg_b0 + reg_b12;
  reg_b0 = reg_b0 + reg_a18;
  reg_b0 = reg_b0 + reg_b19;
  reg_b0 = reg_b0 + reg_a17;
  reg_b0 = reg_b0 + reg_b12;
  reg_b0 = reg_b0 + reg_a14;
  reg_b0 = reg_b0 + reg_a12;
  reg_b0 = reg_b0 + reg_a8;
  reg_b0 = reg_b0 + reg_b13;
  reg_b0 = reg_b0 + reg_a12;
  reg_b0 = reg_b0 + reg_b2;
  reg_b0 = reg_b0 + reg_a18;
  reg_b0 = reg_b0 + reg_b16;
  reg_b0 = reg_b0 + reg_b12;
  reg_b0 = reg_b0 + reg_a12;
  reg_b0 = reg_b0 + reg_b12;
  reg_b0 = reg_b0 + reg_a19;
  reg_b0 = reg_b0 + reg_b19;

  reg_a19 = reg_b0;
  reg_b19 = reg_b0
}.                              

Remark too_many_regs_fails:
  exists x, compile compile_ext_call &[,too_many_regs] = Failure x.
Proof.
  (* let r := eval cbv in (compile compile_ext_call &[,too_many_regs]) in set (res := r). *)
  eexists; cbv; reflexivity. 
Qed.


Definition some_regs :=
  func! (reg_a0, b0) ~> (reg_a0, b0) {
      reg_a1  = reg_a0 +  $1;
      reg_a2  = reg_a0 +  $2;
      reg_a3  = reg_a0 +  $3;
      reg_a4  = reg_a0 +  $4;
      reg_a5  = reg_a0 +  $5;
      reg_a6  = reg_a0 +  $6;
      reg_a7  = reg_a0 +  $7;
      reg_a8  = reg_a0 +  $8;
      reg_a9  = reg_a0 +  $9;
      reg_a10 = reg_a0 + $10;
      reg_a11 = reg_a0 + $11;
      reg_a12 = reg_a0 + $12;
      reg_a13 = reg_a0 + $13;
      reg_a14 = reg_a0 + $14;
      reg_a15 = reg_a0 + $15;
      reg_a16 = reg_a0 + $16;

      b0 = b0 + reg_a0;
      b0 = b0 + reg_a1;
      b0 = b0 + reg_a2;
      b0 = b0 + reg_a3;
      b0 = b0 + reg_a4;
      b0 = b0 + reg_a5;
      b0 = b0 + reg_a6;
      b0 = b0 + reg_a7;
      b0 = b0 + reg_a8;
      b0 = b0 + reg_a9;
      b0 = b0 + reg_a10;
      b0 = b0 + reg_a11;
      b0 = b0 + reg_a12;
      b0 = b0 + reg_a13;
      b0 = b0 + reg_a14;
      b0 = b0 + reg_a15;
      b0 = b0 + reg_a16;

      reg_a0 = reg_a0 + b0;
      b0 = b0 + reg_a0
}.

Definition some_regs_asm: list Instruction.
  let r := eval cbv in (compile compile_ext_call &[,some_regs]) in set (res := r).
  match goal with
  | res := Success (?x, _, _) |- _ => exact x
  end.
Defined.

Module PrintSomeRegsAsm.
  Import riscv.Utility.InstructionNotations.
  Goal True. let r := eval unfold some_regs_asm in some_regs_asm in idtac r. Abort.
End PrintSomeRegsAsm.

Definition long_some_regs := func! (reg_a0, b0) ~> (reg_a19, b19) {
  reg_a19 = $0;
  b19 = $0;

  swap(reg_a0, b0);
  reg_a1 = reg_a0 + b0 * b0;
  swap(reg_a1, b0);
  reg_a12 = reg_a1 - reg_a0 - b0;
  b12 = reg_a1 + reg_a12 * b0;
  reg_a5 = reg_a12 * b12;
  reg_a9 = reg_a5 - reg_a0 - b0;
  reg_a4 = reg_a1;
  b3 = reg_a4 + reg_a12 * b0;
  b4 = reg_a4;
  reg_a10 = reg_a1 - reg_a0 - b4;
  b12 = reg_a1 + reg_a12 * b0;
  reg_a3 = reg_a1;
  reg_a6 = reg_a10 + b12;
  reg_a15 = reg_a3 - reg_a0 - b0;
  a2 = reg_a1;
  b12 = a2 + reg_a12 * b0;
  reg_a11 = reg_a10 - reg_a0 - b0;
  b5 = reg_a1;
  b4 = reg_a6 + reg_a12 * b5;
  a2 = reg_a11 - reg_a0 - b0;
  b12 = reg_a1 + reg_a12 * b0;
  reg_a16 = reg_a12 - reg_a0 - b0;
  reg_a7 = a2;
  b14 = reg_a7 + reg_a12 * b0;
  reg_a13 = b4;
  reg_a17 = $2;
  b6 = $33;
  reg_a12 = reg_a13 - reg_a17 - b6;
  b12 = reg_a1 + reg_a12 * b0;
  reg_a18 = $18;
  b19 = $19;
  reg_a17 = reg_a1 - reg_a18 - b19;
  b12 = reg_a1 + reg_a9 * b0;
  reg_a14 = $14;
  reg_a12 = reg_a14 - reg_a0 - b0;
  reg_a8 = b12;
  b13 = reg_a8 + reg_a12 * b0;
  reg_a12 = reg_a1 - reg_a0 - b0;
  b2 = reg_a1 + reg_a12 * b0;
  reg_a18 = reg_a1 - reg_a0 - b0;
  b16 = $23;
  b12 = reg_a15 + reg_a8 * b16;
  reg_a12 = reg_a1 - reg_a0 - b3;
  b12 = reg_a1 + reg_a12 * b0;

  reg_a19 = reg_a1 - reg_a0 - b0;
  b19 = reg_a9 + reg_a7 * b0;

  b0 = b0 + reg_a1;
  b0 = b0 + reg_a12;
  b0 = b0 + b12;
  b0 = b0 + reg_a5;
  b0 = b0 + reg_a9;
  b0 = b0 + reg_a4;
  b0 = b0 + b3;
  b0 = b0 + b4;
  b0 = b0 + reg_a10;
  b0 = b0 + b12;
  b0 = b0 + reg_a3;
  b0 = b0 + reg_a6;
  b0 = b0 + reg_a15;
  b0 = b0 + b12;
  b0 = b0 + reg_a11;
  b0 = b0 + b5;
  b0 = b0 + b4;
  b0 = b0 + b12;
  b0 = b0 + reg_a16;
  b0 = b0 + reg_a7;
  b0 = b0 + b14;
  b0 = b0 + reg_a13;
  b0 = b0 + reg_a17;
  b0 = b0 + b6;
  b0 = b0 + reg_a12;
  b0 = b0 + b12;
  b0 = b0 + reg_a18;
  b0 = b0 + b19;
  b0 = b0 + reg_a17;
  b0 = b0 + b12;
  b0 = b0 + reg_a14;
  b0 = b0 + reg_a12;
  b0 = b0 + reg_a8;
  b0 = b0 + b13;
  b0 = b0 + reg_a12;
  b0 = b0 + b2;
  b0 = b0 + reg_a18;
  b0 = b0 + b16;
  b0 = b0 + b12;
  b0 = b0 + reg_a12;
  b0 = b0 + b12;
  b0 = b0 + reg_a19;
  b0 = b0 + b19;

  reg_a19 = b0;
  b19 = b0
}.                     

Definition long_some_regs_asm: list Instruction.
  let r := eval cbv in (compile compile_ext_call &[,swap;long_some_regs]) in set (res := r).
  match goal with
  | res := Success (?x, _, _) |- _ => exact x
  end.
Defined.

Module PrintLongSomeRegsAsm.
  Import riscv.Utility.InstructionNotations.
  Goal True. let r := eval unfold long_some_regs_asm in long_some_regs_asm in idtac r. Abort.
End PrintLongSomeRegsAsm.


Definition long_no_regs := func! (a0, b0) ~> (a19, b19) {
  a19 = $0;
  b19 = $0;

  swap(a0, b0);
  a1 = a0 + b0 * b0;
  swap(a1, b0);
  a12 = a1 - a0 - b0;
  b12 = a1 + a12 * b0;
  a5 = a12 * b12;
  a9 = a5 - a0 - b0;
  a4 = a1;
  b3 = a4 + a12 * b0;
  b4 = a4;
  a10 = a1 - a0 - b4;
  b12 = a1 + a12 * b0;
  a3 = a1;
  a6 = a10 + b12;
  a15 = a3 - a0 - b0;
  a2 = a1;
  b12 = a2 + a12 * b0;
  a11 = a10 - a0 - b0;
  b5 = a1;
  b4 = a6 + a12 * b5;
  a2 = a11 - a0 - b0;
  b12 = a1 + a12 * b0;
  a16 = a12 - a0 - b0;
  a7 = a2;
  b14 = a7 + a12 * b0;
  a13 = b4;
  a17 = $2;
  b6 = $33;
  a12 = a13 - a17 - b6;
  b12 = a1 + a12 * b0;
  a18 = $18;
  b19 = $19;
  a17 = a1 - a18 - b19;
  b12 = a1 + a9 * b0;
  a14 = $14;
  a12 = a14 - a0 - b0;
  a8 = b12;
  b13 = a8 + a12 * b0;
  a12 = a1 - a0 - b0;
  b2 = a1 + a12 * b0;
  a18 = a1 - a0 - b0;
  b16 = $23;
  b12 = a15 + a8 * b16;
  a12 = a1 - a0 - b3;
  b12 = a1 + a12 * b0;

  a19 = a1 - a0 - b0;
  b19 = a9 + a7 * b0;

  b0 = b0 + a1;
  b0 = b0 + a12;
  b0 = b0 + b12;
  b0 = b0 + a5;
  b0 = b0 + a9;
  b0 = b0 + a4;
  b0 = b0 + b3;
  b0 = b0 + b4;
  b0 = b0 + a10;
  b0 = b0 + b12;
  b0 = b0 + a3;
  b0 = b0 + a6;
  b0 = b0 + a15;
  b0 = b0 + b12;
  b0 = b0 + a11;
  b0 = b0 + b5;
  b0 = b0 + b4;
  b0 = b0 + b12;
  b0 = b0 + a16;
  b0 = b0 + a7;
  b0 = b0 + b14;
  b0 = b0 + a13;
  b0 = b0 + a17;
  b0 = b0 + b6;
  b0 = b0 + a12;
  b0 = b0 + b12;
  b0 = b0 + a18;
  b0 = b0 + b19;
  b0 = b0 + a17;
  b0 = b0 + b12;
  b0 = b0 + a14;
  b0 = b0 + a12;
  b0 = b0 + a8;
  b0 = b0 + b13;
  b0 = b0 + a12;
  b0 = b0 + b2;
  b0 = b0 + a18;
  b0 = b0 + b16;
  b0 = b0 + b12;
  b0 = b0 + a12;
  b0 = b0 + b12;
  b0 = b0 + a19;
  b0 = b0 + b19;

  a19 = b0;
  b19 = b0
}.                     

Definition long_no_regs_asm: list Instruction.
  let r := eval cbv in (compile compile_ext_call &[,swap;long_no_regs]) in set (res := r).
  match goal with
  | res := Success (?x, _, _) |- _ => exact x
  end.
Defined.

Module PrintLongNoRegsAsm.
  Import riscv.Utility.InstructionNotations.
  Goal True. let r := eval unfold long_no_regs_asm in long_no_regs_asm in idtac r. Abort.
End PrintLongNoRegsAsm.




(* Definition long_lived_in_regs := *)
(*   func! (reg_a0) ~> (reg_a0) { *)
(*       reg_a1  = reg_a0 +  $1; *)
(*       reg_a2  = reg_a0 +  $2; *)
(*       reg_a3  = reg_a0 +  $3; *)
(*       reg_a4  = reg_a0 +  $4; *)
(*       reg_a5  = reg_a0 +  $5; *)
(*       reg_a6  = reg_a0 +  $6; *)
(*       reg_a7  = reg_a0 +  $7; *)
(*       reg_a8  = reg_a0 +  $8; *)
(*       reg_a9  = reg_a0 +  $9; *)
(*       reg_a10 = reg_a0 + $10; *)
(*       reg_a11 = reg_a0 + $11; *)
(*       reg_a12 = reg_a0 + $12; *)
(*       reg_a13 = reg_a0 + $13; *)
(*       reg_a14 = reg_a0 + $14; *)
(*       reg_a15 = reg_a0 + $15; *)
(*       reg_a16 = reg_a0 + $16; *)

(*       b1 = b1 + reg_a1; *)
(*       reg_a1 = reg_a1 + b1; *)
(*       b2 = b2 + reg_a2; *)
(*       reg_a2 = reg_a2 + b2; *)
(*       b3 = b3 + reg_a3; *)
(*       reg_a3 = reg_a3 + b3; *)
(*       b4 = b4 + reg_a4; *)
(*       reg_a4 = reg_a4 + b4; *)
(*       b5 = b5 + reg_a5; *)
(*       reg_a5 = reg_a5 + b5; *)
(*       b6 = b6 + reg_a6; *)
(*       reg_a6 = reg_a6 + b6; *)
(*       b7 = b7 + reg_a7; *)
(*       reg_a7 = reg_a7 + b7; *)
(*       b8 = b8 + reg_a8; *)
(*       reg_a8 = reg_a8 + b8; *)
(*       b9 = b9 + reg_a9; *)
(*       reg_a9 = reg_a9 + b9; *)
(*       b10 = b10 + reg_a10; *)
(*       reg_a10 = reg_a10 + b10; *)
(*       b11 = b11 + reg_a11; *)
(*       reg_a11 = reg_a11 + b11; *)
(*       b12 = b12 + reg_a12; *)
(*       reg_a12 = reg_a12 + b12; *)
(*       b13 = b13 + reg_a13; *)
(*       reg_a13 = reg_a13 + b13; *)
(*       b14 = b14 + reg_a14; *)
(*       reg_a14 = reg_a14 + b14; *)
(*       b15 = b15 + reg_a15; *)
(*       reg_a15 = reg_a15 + b15; *)
(*       b16 = b16 + reg_a16; *)
(*       reg_a16 = reg_a16 + b16; *)

(*       reg_a0 = reg_a16 *)
(* }. *)

(* Definition long_lived_in_regs_asm: list Instruction. *)
(*   let r := eval cbv in (compile compile_ext_call &[,long_lived_in_regs]) in set (res := r). *)
(*   match goal with *)
(*   | res := Success (?x, _, _) |- _ => exact x *)
(*   end. *)
(* Defined. *)

(* Module PrintLongLivedInRegsAsm. *)
(*   Import riscv.Utility.InstructionNotations. *)
(*   Goal True. let r := eval unfold long_lived_in_regs_asm in long_lived_in_regs_asm in idtac r. Abort. *)
(* End PrintLongLivedInRegsAsm. *)






