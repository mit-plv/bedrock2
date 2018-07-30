Require Import bedrock2.Syntax.

Require Import Coq.Strings.String.

Module Syntax.
  Class parameters := {
    actname : Type;
    bopname : Type;
  }.

  Global Instance make (p : parameters) : bedrock2.Syntax.parameters := {|
    bedrock2.Syntax.varname := string;
    bedrock2.Syntax.funname := string;

    bedrock2.Syntax.actname := actname;
    bedrock2.Syntax.bopname := bopname;
  |}.
End Syntax.