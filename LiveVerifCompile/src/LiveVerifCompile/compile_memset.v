Require Import Coq.Strings.String. Local Open Scope string_scope.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import LiveVerifExamples.memset.
Require Import bedrock2.BasicC32Semantics.
Require bedrock2.Hexdump.
Require riscv.Utility.InstructionNotations.
Require compiler.Pipeline.

#[local] Instance RV32I_bitwidth: FlatToRiscvCommon.bitwidth_iset 32 Decode.RV32I.
Proof. reflexivity. Qed.

Definition funimpls: list (String.string *  Syntax.func) :=
  cons ("Memset", (fst Memset)) nil.

Definition memset_insts_result :=
  Pipeline.compile (string_keyed_map := SortedListString.map)
    (fun _ _ _ _ => nil) funimpls.

Definition memset_insts_tuple: list Decode.Instruction * list (string * Z) * Z.
  let r := eval vm_compute in memset_insts_result in
    match r with
    | Result.Success ?p => exact p
    end.
Defined.

Definition memset_insts: list Decode.Instruction :=
  Eval compute in fst (fst memset_insts_tuple).
Definition memset_insts_fpos: list (string * Z) :=
  Eval compute in snd (fst memset_insts_tuple).
Definition memset_insts_req_stack: Z := Eval compute in snd (memset_insts_tuple).

Definition memset_binary: list Byte.byte := Pipeline.instrencode memset_insts.

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Goal True. let r := eval cbv in memset_insts in idtac r. Abort.
End PrintAssembly.

Module PrintBytes.
  Import bedrock2.Hexdump.
  Local Open Scope hexdump_scope.
  Set Printing Width 100.
  Goal True. let r := eval cbv in memset_binary in idtac r. Abort.
End PrintBytes.
