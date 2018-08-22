Require Import bedrock2.Syntax.

Require Import Coq.Strings.String.

Class StringNames_parameters := {
  actname : Set;
  bopname : Set;
}.

Instance StringNames_to_Syntax_parameters (p : StringNames_parameters)
: Syntax_parameters := {|
  Syntax.varname := string;
  Syntax.funname := string;

  Syntax.actname := actname;
  Syntax.bopname := bopname;
|}.
