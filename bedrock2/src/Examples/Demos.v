Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax bedrock2.Syntax.Basic bedrock2.NotationsInConstr.

Import BinInt String.
Local Existing Instance Syntax.Basic.parameters.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Local Coercion var (x : string): expr.expr := expr.var x.
Local Coercion literal (z : Z) : expr := expr.literal z.

Local Notation Prog := ((string * (list varname * list varname * cmd))%type).

Definition bsearch :=
  let left := "left" in
  let right := "right" in
  let target := "target" in
  let mid := "mid" in
("bsearch", ([left; right; target], [left], bedrock_func_body:(
  while (right - left) {{
    mid = left + (((right-left) >> 4) << 3);;
    if ((expr.load access_size.word mid) < target) {{
      left = mid + 8
    }} else {{
      right = mid
    }};;
    cmd.unset mid
  }}
))).

(* input_base is an address fixed at compile time *)
Definition listsum (input_base: Z) : Prog :=
  let sumreg := "sumreg" in
  let n := "n" in
  let i := "i" in
  let a := "a" in
("listsum", ([], [sumreg], bedrock_func_body:(
  sumreg = 0;;
  n = *(uint32_t*) input_base;;
  i = 0;;
  while (i < n) {{
    a = *(uint32_t*) ((input_base + 4)%Z + (4 * i));;
    sumreg = sumreg + a;;
    i = i + 1
  }}
))).

(* input is fixed at compile time *)
Definition fibonacci (n: Z) : Prog :=
  let a := "a" in
  let b := "b" in
  let i := "i" in
  let c := "c" in
("fibonacci", ([], [b], bedrock_func_body:(
  a = 0;;
  b = 1;;
  i = 0;;
  while (i < n) {{
    c = a + b;;
    a = b;;
    b = c;;
    i = i + 1
  }}
))).