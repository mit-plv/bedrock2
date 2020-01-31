Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax bedrock2.ToCString.
Require Import coqutil.Datatypes.String.

Require Import Coq.Strings.String Coq.Numbers.DecimalZ Coq.Numbers.DecimalString.

Import bedrock2.Syntax.bopname.

(* (name, (arguments, returnvalues, body)) *)
Definition function : Type := String.string * (list String.string * list String.string * cmd).

Definition to_c_parameters : ToCString.parameters := {|
  c_lit w := "(uintptr_t)" ++ DecimalString.NilZero.string_of_int (BinInt.Z.to_int w) ++ "ULL";
  c_bop := fun e1 op e2 =>
             match op with
             | add => e1++"+"++e2
             | sub => e1++"-"++e2
             | and => e1++"&"++e2
             | or => e1++"|"++e2
             | xor => e1++"^"++e2
             | sru => e1++">>"++e2
             | slu => e1++"<<"++e2
             | srs => "(intptr_t)"++e1++">>"++e2
             | lts => "(intptr_t)"++e1++"<"++"(intptr_t)"++e2
             | ltu => e1++"<"++e2
             | eq => e1++"=="++e2
             end%string;
     c_var := id;
     c_fun := id;
     c_act := ToCString.c_call;

     rename_away_from x xs :=
       let x' := "_" ++ x in
       if List.existsb (String.eqb x') xs
       then "#error rename_away_from '" ++ x ++"' = '" ++ x' ++"'"
       else x'
  |}%string.

Definition c_func := @c_func to_c_parameters.
