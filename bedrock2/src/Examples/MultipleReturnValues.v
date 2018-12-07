Require Import coqutil.subst coqutil.unique bedrock2.Syntax.
Require Import bedrock2.StringNamesSyntax bedrock2.BasicALU bedrock2.NotationsInConstr.

Import BinInt String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Section MultipleReturnValues.
  Context {p : unique! StringNamesSyntax.parameters} {ALU : BasicALU.operations}.
  Local Coercion literal (z : Z) : expr := expr.literal z.
  Local Coercion var (x : String.string) : expr := expr.var x.

  Let a : varname := "a".
  Let b : varname := "b".
  Let x : varname := "x".
  Let y : varname := "y".

  Example addsub := ("addsub", ((a::b::nil), (x::y::nil), bedrock_func_body:(
    x = a + b;;
    y = a - b
  ))).

  Let ret : varname := "ret".

  Example addsub_test := ("addsub_test", (@nil varname, ("ret"::nil)%list, bedrock_func_body:(
    cmd.call (ret::ret::nil)%list "addsub" (expr.literal 14::expr.literal 7::nil)%list;;
    ret = (ret - 7)
  ))).
End MultipleReturnValues.

Require bedrock2.BasicC64Syntax.

Example addsub_c_string := Eval compute in
  BasicC64Syntax.c_func (addsub (ALU:=BasicC64Syntax.BasicALU)).
Example addsub_test_c_string := Eval compute in
  BasicC64Syntax.c_func (addsub_test (ALU:=BasicC64Syntax.BasicALU)).

(*
Print addsub_c_string.
Print addsub_test_c_string.
*)

(*
uintptr_t addsub(uintptr_t a, uintptr_t b, uintptr_t* _x) {
  uintptr_t x, y;
  x = (a)+(b);
  y = (a)-(b);
  *_x = x;
  return y;
}

uintptr_t addsub_test() {
  uintptr_t ret;
  ret = addsub(14ULL, 7ULL, &ret);
  ret = (ret)-(7ULL);
  return ret;
}
*)