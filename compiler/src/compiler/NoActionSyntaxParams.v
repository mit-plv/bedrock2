Require bedrock2.Syntax.

Class parameters := {
  varname: Set;
  funcname: Set;
}.

Instance to_Basic_bopnames(p: parameters): Syntax.parameters := {|
  Syntax.varname := varname;
  Syntax.funname := funcname;
  Syntax.actname := Empty_set;
|}.
