Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax. Import Syntax.Coercions.
Require Import bedrock2.NotationsCustomEntry.
Require bedrock2.WeakestPrecondition.
Local Open Scope Z_scope. Local Open Scope string_scope.
Import ListNotations.

(* bedrock2 code *)
Module Bedrock2.
  Definition swap : func :=
    let a : string := "a" in
    let b : string := "b" in
    let tmp : string := "tmp" in
    ("swap",
     ([a; b], [], bedrock_func_body:(
       tmp = ( load( a ) ) ;
       store( a, load( b ) );
       store( b, tmp )))).
End Bedrock2.
