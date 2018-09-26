Require bedrock2.Syntax.
Require bedrock2.BasicALU.

Module Import bopname.
  Inductive bopname := add | sub | mul | and | or | xor | sru | slu | srs | lts | ltu | eq.
End bopname.
Notation bopname := bopname.bopname.

Class parameters := {
  varname: Set;
  funcname: Set;
  actname: Set;
}.

Instance make (p: parameters) : Syntax.parameters := {|
  Syntax.varname := @varname p;
  Syntax.funname := @funcname p;
  Syntax.actname := @actname p;
  Syntax.bopname := bopname;
|}.

Instance BasicALU{p: parameters}: BasicALU.operations :=
  BasicALU.Build_operations _ add sub mul and or xor sru slu srs lts ltu eq.
