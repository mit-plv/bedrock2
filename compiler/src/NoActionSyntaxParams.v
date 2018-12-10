Require bedrock2.Basic_bopnames.

Class parameters := {
  varname: Set;
  funcname: Set;
}.

Instance to_Basic_bopnames(p: parameters): Basic_bopnames.parameters := {|
  Basic_bopnames.varname := varname;
  Basic_bopnames.funcname := funcname;
  Basic_bopnames.actname := Empty_set;
|}.
