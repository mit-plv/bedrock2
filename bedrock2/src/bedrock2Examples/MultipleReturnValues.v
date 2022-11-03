Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry Coq.Lists.List.

Import BinInt String ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Section MultipleReturnValues.
  Example addsub := func! (a, b) ~> (x, y) {
    x = a + b;
    y = a - b
  }.

  Example addsub_test := func! () ~> ret {
    unpack! ret, ret = addsub($14, $7);
    ret = ret - $7
  }.
End MultipleReturnValues.

(*
Require Import bedrock2.ToCString coqutil.Macros.WithBaseName.
Compute c_module &[,addsub_test; addsub].
*)

(*
uintptr_t addsub_test(void) {
  uintptr_t ret;
  ret = addsub((uintptr_t)(UINTMAX_C(14)), (uintptr_t)(UINTMAX_C(7)), &ret);
  ret = (ret)-((uintptr_t)(UINTMAX_C(7)));
  return ret;
}

static uintptr_t addsub(uintptr_t a, uintptr_t b, uintptr_t* _x) {
  uintptr_t x, y;
  x = (a)+(b);
  y = (a)-(b);
  *_x = x;
  return y;
}
*)
