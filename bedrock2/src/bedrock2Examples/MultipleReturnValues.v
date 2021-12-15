Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry Coq.Lists.List.

Import BinInt String ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Section MultipleReturnValues.
  Example addsub : func :=
    ("addsub", (["a";"b"], ["x";"y"], bedrock_func_body:(
    x = a + b;
    y = a - b
  ))).

  Example addsub_test : func :=
    ("addsub_test", ([], ["ret"], bedrock_func_body:(
    unpack! ret, ret = addsub($14, $7);
    ret = ret - $7
  ))).
End MultipleReturnValues.

Require Import bedrock2.ToCString.

Example addsub_c_string := Eval compute in c_func addsub.
Example addsub_test_c_string := Eval compute in c_func addsub_test.

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
