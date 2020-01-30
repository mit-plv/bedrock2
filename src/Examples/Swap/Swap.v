Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Require Import bedrock2.BasicCSyntax.
Require Import bedrock2.NotationsCustomEntry.
Require bedrock2.WeakestPrecondition.
Local Open Scope Z_scope. Local Open Scope string_scope.
Import ListNotations.

(* bedrock2 code *)
Module Bedrock2.
  Local Existing Instance bedrock2.BasicCSyntax.StringNames_params.
  Definition bedrock_func : Type :=
    funname * (list varname * list varname * cmd).
  Local Coercion literal (z : Z) : Syntax.expr := expr.literal z.
  Local Coercion var (x : string) : Syntax.expr := expr.var x.
  Local Coercion name_of_func (f : bedrock_func) := fst f.

  Definition swap : bedrock_func :=
    let a : varname := "a" in
    let b : varname := "b" in
    let tmp : varname := "tmp" in
    ("swap",
     ([a; b], [], bedrock_func_body:(
       tmp = ( load( a ) ) ;
       store( a, load( b ) );
       store( b, tmp )))).
End Bedrock2.
