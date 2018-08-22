Require Import Coq.ZArith.BinInt.
Require Import bedrock2.Syntax.
Require Import compiler.Op.

Instance Names: bedrock2.Syntax.parameters := {|
  bedrock2.Syntax.varname := Z;
  bedrock2.Syntax.funname := Z;
  bedrock2.Syntax.actname := Empty_set;
  bedrock2.Syntax.bopname := binop;
|}.
