Require Import Coq.ZArith.BinInt.
Require Import bedrock2.Syntax.
Require Import compiler.Op.

Instance Names: Syntax_parameters := {|
  varname := Z;
  funname := Z;
  actname := Empty_set;
  bopname := binop;
|}.
