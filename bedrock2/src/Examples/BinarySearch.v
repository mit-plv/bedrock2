Require Import bedrock2.Macros bedrock2.Syntax.
Require Import bedrock2.StringNames bedrock2.BasicALU bedrock2.NotationsInConstr.

Import BinInt String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Section bsearch.
  Context {p : unique! StringNames_parameters} {b : BasicALU.operations}.
  Local Coercion literal (z : Z) : expr := expr.literal z.
  Local Coercion var (x : String.string) : expr := expr.var x.

  Let left : varname := "left".
  Let right : varname := "right".
  Let target : varname := "target".

  Let mid : varname := "mid".
  Let tmp : varname := "tmp".

  Definition bsearch := ((left::right::target::nil), (left::nil), bedrock_func(
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

Example bsearch_c_string := Eval compute in
  BasicC64Syntax.c_func "bsearch" (bsearch (b:=BasicC64Syntax.BasicALU)).
(* Print bsearch_c_string. *)