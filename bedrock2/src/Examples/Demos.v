Require Import bedrock2.Macros bedrock2.Syntax.
Require Import bedrock2.StringNamesSyntax bedrock2.BasicALU.
Require bedrock2.NotationsInConstr.
Require bedrock2.BasicC64Syntax.
Require bedrock2.ZNamesSyntax.

Import BinInt String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition StringNamesSyntaxParams: Syntax.parameters :=
  StringNamesSyntax.make BasicC64Syntax.StringNames_params.
Definition ZNamesSyntaxParams: Syntax.parameters :=
  ZNamesSyntax.ZNames.

(* Boilerplate to get variable names.
   The names are in separate modules to allow the same variable name to be used in several
   programs defined in the same file. *)

Module BinarySearch.
  Class Names{p : unique! Syntax.parameters} := {
    left : varname;
    right : varname;
    target : varname;
    mid : varname;
    tmp : varname;
  }.
  Module StringNames.
    Instance Inst: @Names StringNamesSyntaxParams := {
      left := "left";
      right := "right";
      target := "target";
      mid := "mid";
      tmp := "tmp";
    }.
  End StringNames.
  Module ZNames.
    Instance Inst: @Names ZNamesSyntaxParams := {
      left := 1;
      right := 2;
      target := 3;
      mid := 4;
      tmp := 5;
    }.
  End ZNames.
End BinarySearch.

Module ListSum.
  Class Names{p : unique! Syntax.parameters} := {
    n: varname;
    i: varname;
    sumreg: varname;
    a: varname;
  }.
  Module StringNames.
    Instance Inst: @Names StringNamesSyntaxParams := {
      left := "left";
      right := "right";
      target := "target";
      mid := "mid";
      tmp := "tmp";
    }.
  End StringNames.




End ListSum.


Section Demos.

  (* note: this coercion must have its own p, because varname depends on p, and the
     coercion only kicks in if p can be chosen freely *)
  Local Coercion var{p : unique! Syntax.parameters}(x : @varname p): @expr.expr p :=
    @expr.var p x.

  Context {p : unique! Syntax.parameters} {b : BasicALU.operations}.

  (* note: this coercion must use the section's p, because its argument z does not
     allow Coq to infer p *)
  Local Coercion literal (z : Z) : expr := expr.literal z.

  Import bedrock2.NotationsInConstr.

  Context {bsearchNames: unique! BinarySearch.Names}.
  Import BinarySearch.
  Definition bsearch := ((left::right::target::nil), (left::nil), bedrock_func_body:(
    while (left < right) {{
      mid = left + (((right-left) >> 4) << 3);;
      tmp = *(uint64_t*) mid;;
      if (tmp < target) {{
        left = mid + 8
      }} else {{
        right = mid
      }}
    }}
  )).

  Context {names: unique! BinarySearch.Names}.
  Import BinarySearch.

(*(*(*
  Class
  Let n: varname := 1.
  Let i: varname := 2.
  Let sumreg: varname := 3.
  Let a: varname := 4.
   (* input_base is an address fixed at compilation time *)
  Definition listsum(input_base: Z) := bedrock_func_body:(
    sumreg = 0;
    n = *(uint32_t*) input_base;
    i = 0;
    while (Var i < Var n) {{
      a = *(uint32_t*) ((input_base + 4)%Z + (4 * Var i));
      sumreg = Var sumreg + Var a;
      i = Var i + 1
    }}
*)

End Demos.



Local Instance bsearch_string_names:
  @BinarySearch.Names (StringNamesSyntax.make BasicC64Syntax.StringNames_params) :=
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

Local Instance bsearch_string_ZNames: @BinarySearch.Names ZNamesSyntax.ZNames := {
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
