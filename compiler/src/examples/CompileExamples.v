Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Strings.String.
Require bedrock2.Examples.Demos.
Require Import bedrock2.Basic_bopnames.
Require Import lib.LibTacticsMin.
Require Import riscv.util.Word.
Require Import coqutil.Decidable.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Pipeline.
Require Import compiler.util.Common.
Require Import riscv.util.BitWidths.
Require Import riscv.util.BitWidth32.
Require Import compiler.FlatToRiscv32Specifics.
Require Import coqutil.Map.SortedList.
Require Import compiler.ZNameGen.
Require Import riscv.InstructionCoercions.
Require compiler.FlatImp.
Require Import compiler.RegAlloc3.
Require Import bedrock2.Byte.
Require Import compiler.RegAllocAnnotatedNotations.
Require Import riscv.InstructionNotations.
Require Import bedrock2.Hexdump.

Open Scope Z_scope.
Open Scope string_scope.


Definition var: Set := Z.
Definition func: Set := Empty_set.
Definition Reg: Set := Z.


Existing Instance DefaultRiscvState.

Existing Instance FlatToRiscv.State_is_RegisterFile.

(*
Record example := mk_example {
  name: string;
  inputVars: set var;
  outputVars: set var;
  src: cmd;
  flattened: FlatImp.stmt;
  (*
  regallocAnnotated: astmt var var func;
  regallocChecked: FlatImp.stmt var func;
  *)
  riscv_instructions: list Instruction;
  riscv_bytes: list byte;
}.

Arguments mk_example
          name%string
          inputVars
          outputVars
          src
          flattened
          regallocAnnotated%regalloc_scope
          regallocChecked
          riscv_instructions (* TODO add scope to riscv.InstructionNotations *)
          riscv_bytes%hexdump_scope.

Instance bops: @BasicALU.operations (@syntax Basic32Semantics.Basic32Semantics) :=
  @Basic_bopnames.BasicALU {|
    Basic_bopnames.varname := var;
    Basic_bopnames.funcname := func;
    Basic_bopnames.actname := Empty_set;
  |}.

Definition list_to_id_map(l: list var): map var var :=
  fold_left (fun m v => put m v v) l empty_map.

Definition Ex(p: Demos.Prog): example :=
  let '(name, (inputVarList, outputVarList, src)) := p in
  let inputVars: set var := of_list inputVarList in
  let outputVars := of_list outputVarList in
  let flattened := flatten src in
  let regallocAnnotated := regalloc var var func
         Register0
         riscvRegisters
         (list_to_id_map inputVarList)
         flattened
         empty_set
         (list_to_id_map outputVarList) in
  let regallocChecked :=
    match checker var var func (list_to_id_map inputVarList) regallocAnnotated with
    | Some s => s
    | None => FlatImp.SSkip
    end in
  let riscv_instructions := FlatToRiscv.compile_stmt Lw Sw regallocChecked in
  let riscv_words := List.map (fun i => ZToWord 32 (encode i)) riscv_instructions in
  let riscv_word8s := store_word_list riscv_words
                                      (Utility.ZToReg 0)
                                      (zero_mem ((Memory.Zlength riscv_instructions) * 4)) in
  let riscv_bytes := List.map (fun w => Byte.of_Z (uwordToZ w)) riscv_word8s in
  mk_example
    name
    inputVars
    outputVars
    src
    flattened
    regallocAnnotated
    regallocChecked
    riscv_instructions
    riscv_bytes.

Time Definition allCompilationResults: list example :=
  Eval cbv in (List.map Ex Demos.allProgs).

Set Printing Width 100.
Print allCompilationResults.
*)
