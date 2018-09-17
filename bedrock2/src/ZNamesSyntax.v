Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax.
Require Import bedrock2.Basic_bopnames.

Instance ZNames : Syntax.parameters := {|
  Syntax.varname := Z;
  Syntax.globname := Z;

  Syntax.actname := Empty_set;
  Syntax.bopname := bopname;
|}.
