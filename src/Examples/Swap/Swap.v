Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Require Import bedrock2.NotationsCustomEntry.
Require bedrock2.WeakestPrecondition.
Local Open Scope Z_scope. Local Open Scope string_scope.
Import ListNotations.

(* bedrock2 code *)
Module Bedrock2.

  Definition bedrock_func : Type :=
    string * (list string * list string * cmd).
  Local Coercion literal (z : Z) : Syntax.expr := expr.literal z.
  Local Coercion var (x : string) : Syntax.expr := expr.var x.
  Local Coercion name_of_func (f : bedrock_func) := fst f.

  Definition swap : bedrock_func :=
    let a : string := "a" in
    let b : string := "b" in
    let tmp : string := "tmp" in
    ("swap",
     ([a; b], [], bedrock_func_body:(
       tmp = ( load( a ) ) ;
       store( a, load( b ) );
       store( b, tmp )))).
End Bedrock2.
