Require Import ZArith coqutil.Z.div_mod_to_equations.
Require Import bedrock2.NotationsCustomEntry.
Import Syntax BinInt String List.ListNotations ZArith.
Require Import coqutil.Z.Lia.
Require Import bedrock2Examples.rpmul.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(* Variant of "ipow" implementing multiplication in terms of addition instead
* of exponentiation in terms of multiplication. *)

Definition softmul :=
  ("softmul", (["inst"; "a_regs"], @nil String.string, bedrock_func_body:(
  (* TODO for Andres *)
  a = $2;
  b = $3;
  unpack! c = rpmul(a, b)
))).

From bedrock2 Require Import Semantics BasicC32Semantics WeakestPrecondition ProgramLogic.
From coqutil Require Import Word.Properties Word.Interface Tactics.letexists.
Require Import riscv.Spec.Decode riscv.Utility.Utility.
Require Import bedrock2.SepAutoArray bedrock2.SepAuto.
Open Scope bool_scope.

(* like (decode RV32I), but additionally also accepts the Mul instruction
   (but no other instructions from the M extension) *)
Definition mdecode(inst: Z): Instruction :=
  let opcode := bitSlice inst 0 7 in
  let rd := bitSlice inst 7 12 in
  let funct3 := bitSlice inst 12 15 in
  let rs1 := bitSlice inst 15 20 in
  let rs2 := bitSlice inst 20 25 in
  let funct7 := bitSlice inst 25 32 in
  if (opcode =? opcode_OP) && (funct3 =? funct3_MUL) && (funct7 =? funct7_MUL)
  then MInstruction (Mul rd rs1 rs2)
  else decode RV32I inst.

Definition idecode: Z -> Instruction := decode RV32I.

#[export] Instance spec_of_softmul : spec_of "softmul" :=
  fnspec! "softmul" inst a_regs / rd rs1 rs2 regvals R,
  { requires t m :=
      mdecode (word.unsigned inst) = MInstruction (Mul rd rs1 rs2) /\
      List.length regvals = 32%nat /\
      seps [a_regs |-> word_array regvals; R] m;
      (* Alternative way of expressing the length constraint:
      seps [a_regs |-> with_len 32 word_array regvals; R] m; *)
    ensures t' m' :=
      t = t' /\
      seps [a_regs |-> word_array (List.upd regvals (Z.to_nat rd) (word.mul
               (List.nth (Z.to_nat rs1) regvals default)
               (List.nth (Z.to_nat rs2) regvals default))); R] m
 }.

Lemma softmul_ok : program_logic_goal_for_function! softmul.
Proof.
  (* TODO for Andres *)
Admitted.
