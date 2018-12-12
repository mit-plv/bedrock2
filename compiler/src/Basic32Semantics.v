Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import coqutil.Map.SortedList.
Require Import bedrock2.ZNamesSyntax.
Require Import compiler.Op.
Require Import riscv.MachineWidth32.

Definition TODO{T: Type}: T. Admitted.

Instance Basic32Semantics: bedrock2.Semantics.parameters. unshelve refine {|
  Semantics.syntax := {|
    Syntax.varname := Z;
    Syntax.funname := Empty_set;
    Syntax.actname := Empty_set;
    Syntax.bopname := bopname;
  |};
  Semantics.interp_binop bop := eval_binop bop;
|}.
Proof.
  all: try exact _.
  (* all other fields are unused: *)
  all: apply TODO.
Defined.
