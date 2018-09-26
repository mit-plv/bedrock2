Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import bedrock2.BasicBopnamesSyntax.

Instance ZNames : Syntax.parameters := {|
  Syntax.varname := Z;
  Syntax.funname := Z;

  Syntax.actname := Empty_set;
  Syntax.bopname := bopname;
|}.
