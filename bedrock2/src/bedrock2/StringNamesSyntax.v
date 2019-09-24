Require Import bedrock2.Syntax.

Require Import Coq.Strings.String.

Class parameters := {
  actname : Type;
}.

Instance make (p : parameters) : Syntax.parameters := {|
  Syntax.varname := string;
  Syntax.funname := string;

  Syntax.actname := actname;
|}.
