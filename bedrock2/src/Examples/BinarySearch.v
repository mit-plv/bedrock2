Require Import bedrock2.Macros bedrock2.Syntax.
Require Import bedrock2.StringNamesSyntax bedrock2.BasicALU.
Require bedrock2.NotationsInConstr.

Import BinInt String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Class bsearch_names {p: unique! Syntax.parameters} := {
  left : varname;
  right : varname;
  target : varname;
  mid : varname;
  tmp : varname;
}.

Section bsearch.
  Import bedrock2.NotationsInConstr.
  Local Coercion var{p : unique! Syntax.parameters}(x : @varname p): @expr.expr p :=
    @expr.var p x.

  Context {p : unique! Syntax.parameters} {b : BasicALU.operations}.
  Local Coercion literal (z : Z) : expr := expr.literal z.

  Context {names: unique! bsearch_names}.

  Definition bsearch := ((left::right::target::nil), (left::nil), bedrock_func_body:(
    while (left < right) {{
      mid = left + (((right-left) >> 4) << 3);
      tmp = *(uint64_t*) mid;
      if (tmp < target) {{
        left = mid + 8
      }} else {{
        right = mid
      }}
    }}
  )).
End bsearch.

Require bedrock2.BasicC64Syntax.

Local Instance bsearch_string_names:
  @bsearch_names (StringNamesSyntax.make BasicC64Syntax.params) :=
{
  left := "left";
  right := "right";
  target := "target";
  mid := "mid";
  tmp := "tmp";
}.

Example bsearch_c_string := Eval compute in
  BasicC64Syntax.c_func "bsearch" (bsearch (b:=BasicC64Syntax.BasicALU)).

Print bsearch_c_string.

Require bedrock2.ZNamesSyntax.

Local Instance bsearch_string_ZNames:
  @bsearch_names ZNamesSyntax.ZNames :=
{
  left := 1;
  right := 2;
  target := 3;
  mid := 4;
  tmp := 5;
}.

Require Import bedrock2.Basic_bopnames.

Class my_parameters := {
  varname: Set;
  funcname: Set;
  actname: Set;
}.

Local Instance make (p: my_parameters) : Syntax.parameters := {|
  Syntax.varname := @varname p;
  Syntax.funname := @funcname p;
  Syntax.actname := @actname p;
  Syntax.bopname := Basic_bopnames.bopname;
|}.

Import bopname.

Local Instance MyBasicALU{p: my_parameters}: BasicALU.operations :=
  BasicALU.Build_operations _ add sub mul and or xor sru slu srs lts ltu eq.

Example bsearch_z_ast{p: unique! my_parameters} :=
  Eval cbv [bsearch left right target mid tmp ZNamesSyntax.ZNames bsearch_string_ZNames
            var literal] in
    @bsearch ZNamesSyntax.ZNames MyBasicALU bsearch_string_ZNames.

Print bsearch_z_ast.
