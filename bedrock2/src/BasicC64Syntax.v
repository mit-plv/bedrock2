Require Import coqutil.Macros.subst coqutil.Macros.unique bedrock2.Syntax bedrock2.ToCString.
Require Import bedrock2.StringNamesSyntax bedrock2.BasicALU coqutil.Datatypes.String.

Require Import Coq.Strings.String Coq.Numbers.DecimalZ Coq.Numbers.DecimalString.

Require Export bedrock2.Basic_bopnames.
Import bedrock2.Basic_bopnames.bopname.

Definition StringNames_params: bedrock2.StringNamesSyntax.parameters := {|
  StringNamesSyntax.bopname := bedrock2.Basic_bopnames.bopname;
  StringNamesSyntax.actname := string
|}.

Definition Basic_bopnames_params: bedrock2.Basic_bopnames.parameters := {|
  Basic_bopnames.varname := string;
  Basic_bopnames.funcname := string;
  Basic_bopnames.actname := string;
|}.

Definition BasicALU: @BasicALU.operations (StringNamesSyntax.make StringNames_params) :=
  @Basic_bopnames.BasicALU Basic_bopnames_params.

Definition to_c_parameters : ToCString.parameters := {|
  syntax := (StringNamesSyntax.make StringNames_params);
  c_lit w := DecimalString.NilZero.string_of_int (BinInt.Z.to_int w) ++ "ULL";
  c_bop := fun e1 op e2 =>
             match op with
             | add => e1++"+"++e2
             | sub => e1++"-"++e2
             | mul => e1++"*"++e2
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

     varname_eqb := String.eqb;
     rename_away_from x xs :=
       let x' := "_" ++ x in
       if List.existsb (String.eqb x') xs
       then "#error rename_away_from '" ++ x ++"' = '" ++ x' ++"'"
       else x'
  |}%string.

Definition c_func := @c_func to_c_parameters.
