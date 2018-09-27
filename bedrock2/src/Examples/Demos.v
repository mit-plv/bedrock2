Require Import bedrock2.Macros bedrock2.Syntax.
Require Import bedrock2.StringNamesSyntax bedrock2.BasicALU.
Require bedrock2.NotationsInConstr.

Import BinInt String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.


Section Demos.

  (* note: this coercion must have its own p, because varname depends on p, and the
     coercion only kicks in if p can be chosen freely *)
  Local Coercion var{p : unique! Syntax.parameters}(x : @varname p): @expr.expr p :=
    @expr.var p x.

  Context {p : unique! Syntax.parameters} {b : BasicALU.operations}.

  (* note: this coercion must use the section's p, because its argument z does not
     allow Coq to infer p *)
  Local Coercion literal (z : Z) : expr := expr.literal z.

  Class bsearch_names := {
    left : varname;
    right : varname;
    target : varname;
    mid : varname;
    tmp : varname;
  }.

  Context {names: unique! bsearch_names}.

  Import bedrock2.NotationsInConstr.

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
End Demos.

Require bedrock2.BasicC64Syntax.

Local Instance bsearch_string_names:
  @bsearch_names (StringNamesSyntax.make BasicC64Syntax.StringNames_params) :=
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

Local Instance bsearch_string_ZNames: @bsearch_names ZNamesSyntax.ZNames := {
  left := 1;
  right := 2;
  target := 3;
  mid := 4;
  tmp := 5;
}.

Require Import bedrock2.Basic_bopnames.

Definition BasicALU_params: Basic_bopnames.parameters := {|
  varname := Z;
  funcname := Z;
  actname := Empty_set;
|}.

Example bsearch_z_ast :=
  Eval cbv in
    @bsearch ZNamesSyntax.ZNames
             (@Basic_bopnames.BasicALU BasicALU_params)
             bsearch_string_ZNames.

Print bsearch_z_ast.
