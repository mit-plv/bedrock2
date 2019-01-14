Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.

Definition ZNames : Syntax.parameters := {|
  Syntax.varname := Z;
  Syntax.funname := Z;

  Syntax.actname := Empty_set;
|}.
