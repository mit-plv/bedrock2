Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax.
Require bedrock2.NotationsInConstr.
Require bedrock2.BasicCSyntax.
Require Import coqutil.sanity.

Import BinInt String.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition StringNamesSyntaxParams: Syntax.parameters :=
  StringNamesSyntax.make BasicCSyntax.StringNames_params.

Definition ZNamesSyntaxParams: Syntax.parameters := {|
  Syntax.varname := Z;
  Syntax.funname := string;
  Syntax.actname := string;
|}.


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
      n := "n";
      i := "i";
      sumreg := "sumreg";
      a := "a";
    }.
  End StringNames.
  Module ZNames.
    Instance Inst: @Names ZNamesSyntaxParams := {
      n := 1;
      i := 2;
      sumreg := 3;
      a := 4;
    }.
  End ZNames.
End ListSum.

Module Fibonacci.
  Class Names{p : unique! Syntax.parameters} := {
    a: varname;
    b: varname;
    c: varname;
    i: varname;
  }.
  Module StringNames.
    Instance Inst: @Names StringNamesSyntaxParams := {
      a := "a";
      b := "b";
      c := "c";
      i := "i";
    }.
  End StringNames.
  Module ZNames.
    Instance Inst: @Names ZNamesSyntaxParams := {
      a := 1;
      b := 2;
      c := 3;
      i := 4;
    }.
  End ZNames.
End Fibonacci.


Section Demos.

  (* note: this coercion must have its own p, because varname depends on p, and the
     coercion only kicks in if p can be chosen freely *)
  Local Coercion var{p : unique! Syntax.parameters}(x : @varname p): @expr.expr p :=
    @expr.var p x.

  Context {p : unique! Syntax.parameters}.

  (* note: this coercion must use the section's p, because its argument z does not
     allow Coq to infer p *)
  Local Coercion literal (z : Z) : expr := expr.literal z.

  Definition Prog: Type := string * (list varname * list varname * cmd).

  Import bedrock2.NotationsInConstr.

  Context {bsearchNames: unique! BinarySearch.Names}.
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

  Context {listsumNames: unique! ListSum.Names}.
  Import ListSum.
  (* input_base is an address fixed at compile time *)
  Definition listsum(input_base: Z): Prog := ("listsum", ([], [sumreg], bedrock_func_body:(
    sumreg = 0;;
    n = *(uint32_t*) input_base;;
    i = 0;;
    while (i < n) {{
      a = *(uint32_t*) ((input_base + 4)%Z + (4 * i));;
      sumreg = sumreg + a;;
      i = i + 1
    }}
  ))).

  Context {fibonacciNames: unique! Fibonacci.Names}.
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

Definition allProgsAsCStrings: list string :=
  Eval cbv in (map BasicCSyntax.c_func allProgs).

(* Print allProgsAsCStrings. *)

Definition allProgsWithZNames :=
  Eval cbv in allProgs (p:=ZNamesSyntaxParams).

(* Print allProgsWithZNames. *)
