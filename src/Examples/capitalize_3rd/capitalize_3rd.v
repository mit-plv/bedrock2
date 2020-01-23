Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List.
Require Import Coq.Strings.String.
Require Import bedrock2.Syntax.
Require Import bedrock2.BasicCSyntax.
Require Import bedrock2.NotationsCustomEntry.
Local Open Scope Z_scope. Local Open Scope string_scope.
Import ListNotations.

(* bedrock2 code *)
Module Bedrock2.
  Local Existing Instance bedrock2.BasicCSyntax.StringNames_params.
  Local Definition bedrock_func : Type :=
    funname * (list varname * list varname * cmd).
  Local Coercion literal (z : Z) : Syntax.expr := expr.literal z.
  Local Coercion var (x : string) : Syntax.expr := expr.var x.
  Local Coercion name_of_func (f : bedrock_func) := fst f.

  Axiom wordsize : Z. (* in bytes *)
  Axiom toupper : bedrock_func.

  Definition capitalize_String : bedrock_func :=
    let s : varname := "s" in
    let ret : varname := "ret" in
    let len : varname := "len" in
    let i : varname := "i" in
    let x : varname := "x" in
    let loc : varname := "loc" in
    ("capitalize_String",
     ([s], [ret], bedrock_func_body:(
       len = (load( s )) ;
         i = (constr:(0)) ;
         while (i < len) {{
           i = (i + constr:(1)) ;
           loc = (s + (i * wordsize)) ;
           unpack! x = toupper (load(loc)) ;
           store(loc, x)
         }} ;
         ret = (constr:(1))))).

  Definition capitalize_3rd : bedrock_func :=
    let inp : varname := "in" in
    let ret : varname := "ret" in
    let loc : Z := 2 * wordsize in
    ("capitalize_3rd",
     ([inp], [ret], bedrock_func_body:(
       unpack! ret = capitalize_String(load((inp + loc)))))).
End Bedrock2.

(* Gallina code *)
Module Gallina.
  Section Gallina.
    Context {char : Type} (toupper : char -> char).

    Record String := { length : Z; chars : list char }.
    Definition dummy : String := {| length := 0; chars := [] |}.

    Definition capitalize_String (s : String) : String * bool := 
      ({| length := length s; chars := map toupper (chars s) |}, true).

    Definition capitalize_3rd (inp : list String)
      : list String * bool :=
      let cap := capitalize_String (nth_default dummy inp 2) in
      (firstn 2 inp ++ fst cap :: skipn 3 inp, snd cap)%list.
  End Gallina.
End Gallina.
