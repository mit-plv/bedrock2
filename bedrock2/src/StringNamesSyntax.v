Require Import bedrock2.Syntax.

Require Import Coq.Strings.String.

Class parameters := {
  actname : Set;
  bopname : Set;
}.

Instance make (p : parameters) : Syntax.parameters := {|
  Syntax.varname := string;
  Syntax.globname := string;

  Syntax.actname := actname;
  Syntax.bopname := bopname;
|}.
