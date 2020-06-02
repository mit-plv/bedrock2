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

  Axiom wordsize : Z. (* in bytes *)
  Axiom toupper : bedrock_func.
  Definition charsize : Z := 1.

  (* TODO: use bedrock2 Structs? *)
  Definition capitalize_String : bedrock_func :=
    let s_ptr : string := "s_ptr" in
    let ret : string := "ret" in
    let len : string := "len" in
    let i : string := "i" in
    let x : string := "x" in
    let c_ptr : string := "c_ptr" in
    ("capitalize_String",
     ([s_ptr], [ret], bedrock_func_body:(
       len = (load( s_ptr )) ;
       i = (constr:(0)) ;
       c_ptr = (s_ptr + wordsize) ;
       while (i < len) {{
         unpack! x = toupper (load1( c_ptr )) ;
         store1(c_ptr, x) ;
         c_ptr = (c_ptr + charsize) ;
         i = (i + constr:(1))
       }} ;
       ret = (constr:(1))))).

  Definition capitalize_3rd : bedrock_func :=
    let inp : string := "inp" in
    let ret : string := "ret" in
    let offset : Z := 2 * wordsize in
    ("capitalize_3rd",
     ([inp], [ret], bedrock_func_body:(
       unpack! ret = capitalize_String(load( (inp + offset) ))))).
End Bedrock2.

(* Gallina code *)
Module Gallina.
  Section Gallina.
    Context {char : Type}
            {toupper : char -> char}.

    Record String := { len : nat; chars : list char}.
    Definition dummy : String := {| len := 0; chars := [] |}.

    Definition capitalize_String (s : String) : String :=
      {| len := len s; chars := map toupper (chars s) |}.

    Definition capitalize_3rd (inp : list String) : list String :=
      let cap := capitalize_String (nth_default dummy inp 2) in
      (List.firstn 2 inp ++ cap :: List.skipn 3 inp)%list.
  End Gallina.
End Gallina.
