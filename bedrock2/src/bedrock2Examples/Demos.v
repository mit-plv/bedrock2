Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.
Require bedrock2.NotationsInConstr.
Require Import coqutil.sanity.

Import BinInt String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

(* Boilerplate to get variable names.
   The names are in separate modules to allow the same variable name to be used in several
   programs defined in the same file. *)

Module BinarySearch.
  Class Names := {
    left : String.string;
    right : String.string;
    target : String.string;
    mid : String.string;
    tmp : String.string;
  }.
  Module StringNames.
    Instance Inst: Names := {
      left := "left";
      right := "right";
      target := "target";
      mid := "mid";
      tmp := "tmp";
    }.
  End StringNames.
End BinarySearch.

Module ListSum.
  Class Names := {
    n: String.string;
    i: String.string;
    sumreg: String.string;
    a: String.string;
  }.
  Module StringNames.
    Instance Inst: Names := {
      n := "n";
      i := "i";
      sumreg := "sumreg";
      a := "a";
    }.
  End StringNames.
End ListSum.

Module Fibonacci.
  Class Names := {
    a: String.string;
    b: String.string;
    c: String.string;
    i: String.string;
  }.
  Module StringNames.
    Instance Inst: Names := {
      a := "a";
      b := "b";
      c := "c";
      i := "i";
    }.
  End StringNames.
End Fibonacci.


Module FibonacciServer.
  Class Names := {
    a: String.string;
    b: String.string;
    c: String.string;
    i: String.string;
    n: String.string;
  }.
  Module StringNames.
    Instance Inst: Names := {
      a := "a";
      b := "b";
      c := "c";
      i := "i";
      n := "n";
    }.
  End StringNames.
End FibonacciServer.

Section Demos.

  Local Coercion var(x : String.string): expr.expr := expr.var x.
  Local Coercion literal (z : Z) : expr := expr.literal z.

  Definition Prog: Type := string * (list String.string * list String.string * cmd).

  Import bedrock2.NotationsInConstr.
  Import BinarySearch.
  Definition bsearch: Prog := ("bsearch", ([left; right; target], [left], bedrock_func_body:(
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

  Import ListSum.
  (* input_base is an address fixed at compile time *)
  Definition listsum(input_base: Z): Prog := ("listsum", ([], [sumreg], bedrock_func_body:(
    sumreg = 0;;
    n = *(uint32_t*) input_base;;
    i = 0;;
    while (i < n) {{
      a = *(uint32_t*) ((input_base + 4)%Z + (i << 2));;
      sumreg = sumreg + a;;
      i = i + 1
    }}
  ))).

  Import Fibonacci.
  (* input_base is an address fixed at compile time *)
  Definition fibonacci(n: Z): Prog := ("fibonacci", ([], [b], bedrock_func_body:(
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

  Import FibonacciServer.
  Definition fibonacciServer (n_load_addr n_store_addr: Z): Prog := ("fibonacciserver", ([], [b], bedrock_func_body:(
    n = *(uint32_t*) n_load_addr;;
    a = 0;;
    b = 1;;
    i = 0;;
    if (n < 47) {{
      while (i < n) {{
        c = a + b;;
        a = b;;
        b = c;;
        i = i + 1
      }}
    }} else {{
      b = -1
    }};;
    *(uint32_t*) n_store_addr = b
  ))).

  Definition dummy: Prog := ("dummy", ([], [], cmd.skip)).

  Definition allProgs: list Prog :=
    Eval unfold bsearch, listsum, fibonacci in
      [bsearch; listsum 1024; fibonacci 6].

  (*Print allProgs.*)

  Definition prog(name: string): Prog :=
    match find (fun '(n, _) => if string_dec n name then true else false) allProgs with
    | Some p => p
    | None => dummy
    end.

End Demos.

(* let's print them again in AST form: *)
(* Print allProgs. *)

Require Import bedrock2.ToCString.
Definition allProgsAsCStrings: list string :=
  Eval cbv in (map c_func allProgs).

(* Print allProgsAsCStrings. *)

Definition allProgsE :=
  Eval cbv in allProgs.

(* Print allProgsE. *)
