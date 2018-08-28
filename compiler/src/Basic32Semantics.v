Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Map.UnorderedList.
Require Import bedrock2.ZNamesSyntax.
Require Import compiler.Op.
Require Import riscv.MachineWidth32.

Definition TODO{T: Type}: T. Admitted.

Instance Basic32Semantics: bedrock2.Semantics.parameters := {|
  syntax := ZNames;
  interp_binop bop := eval_binop bop;
|}.
  (* all other fields are unused: *)
  all: apply TODO.
Defined.
