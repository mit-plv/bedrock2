Require Import bedrock2.Macros bedrock2.Syntax.
Require Import bedrock2.ZNamesSyntax bedrock2.BasicALU bedrock2.NotationsInConstr.
Require Import Coq.ZArith.BinInt.

Local Open Scope Z_scope.

(* TODO make varname abstract so that it doesn't clash with the Lit coercion,
   and also abstract over fresh name generation. *)
Section listsum.
  Context {b : BasicALU.operations}.
  
  Local Coercion Lit (z: Z): expr := expr.literal z.
  Local Coercion Var (x: varname): expr := expr.var x.

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
  ).

End listsum.
