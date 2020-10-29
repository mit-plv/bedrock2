Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require Import coqutil.sanity.

Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.
Import BinInt String.
Local Coercion expr.literal : Z >-> expr.
Local Coercion expr.var : String.string >-> expr.
Local Coercion name_of_func (f : function) : String.string := fst f.

Definition bsearch: func :=
  let left := "left" in let right := "right" in let target := "target" in let mid := "mid" in
  ("bsearch", ([left; right; target], [left], bedrock_func_body:(
  while (right - left) {
    mid = left + (((right-left) >> coq:(4)) << coq:(3));
    if (load(mid) < target) {
      left = mid + coq:(8)
    } else {
      right = mid
    };
    coq:(cmd.unset mid)
  }
))).

(* input_base is an address fixed at compile time *)
Definition listsum(input_base: Z): func :=
  let sumreg := "sumreg" in let n := "n" in let i := "i" in let a := "a" in
  ("listsum", ([], [sumreg], bedrock_func_body:(
  sumreg = coq:(0);
  n = load4(input_base);
  i = coq:(0);
  while (i < n) {
    a = load4(coq:(input_base + 4) + (i << coq:(2)));
    sumreg = sumreg + a;
    i = i + coq:(1)
  }
))).

(* input_base is an address fixed at compile time *)
Definition fibonacci(n: Z): func :=
  let a := "a" in let b := "b" in let i := "i" in let n := "n" in let c := "c" in
  ("fibonacci", ([], [b], bedrock_func_body:(
  a = coq:(0);
  b = coq:(1);
  i = coq:(0);
  while (i < n) {
    c = a + b;
    a = b;
    b = c;
    i = i + coq:(1)
  }
))).

Definition fibonacciServer (n_load_addr n_store_addr: Z): func :=
  let b := "b" in let n := "n" in let a := "a" in let i := "i" in let c := "c" in
  ("fibonacciserver", ([], [b], bedrock_func_body:(
  n = load4(n_load_addr);
  a = coq:(0);
  b = coq:(1);
  i = coq:(0);
  if (n < coq:(47)) {
    while (i < n) {
      c = a + b;
      a = b;
      b = c;
      i = i + coq:(1)
    }
  } else {
    b = coq:(-1)
  };
  store4(n_store_addr, b)
))).

Definition dummy: func := ("dummy", ([], [], cmd.skip)).

Definition allProgs: list func :=
  Eval unfold bsearch, listsum, fibonacci in
    [bsearch; listsum 1024; fibonacci 6].

(*
Print allProgs.
*)

Require Import bedrock2.ToCString.
Definition allProgsAsCString : string :=
  Eval cbv in c_module allProgs.

(*
Print allProgsAsCString.
*)
