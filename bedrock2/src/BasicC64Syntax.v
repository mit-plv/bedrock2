Require Import bedrock2.Macros bedrock2.Syntax bedrock2.ToCString.
Require Import bedrock2.StringNames bedrock2.BasicALU bedrock2.String.

Require Import Coq.Strings.String Coq.Numbers.DecimalZ Coq.Numbers.DecimalString.

Module Import bopname.
  Inductive bopname := add | sub | and | or | xor | sru | slu | srs | lts | ltu | eq.
End bopname.

Definition parameters : bedrock2.Syntax.parameters := StringNames.Syntax.make {|
  StringNames.Syntax.bopname := bopname;
  StringNames.Syntax.actname := Empty_set
|}.

Definition BasicALU : BasicALU.operations (p:=parameters) :=
  Build_operations parameters add sub and or xor sru slu srs lts ltu eq.


Definition to_c_parameters : ToCString.parameters := {|
  syntax := parameters;
  c_lit w := DecimalString.NilZero.string_of_int (BinInt.Z.to_int w) ++ "ULL";
  c_bop := fun e1 op e2 =>
             match op with
             | add => e1++"+"++e2
             | sub => e1++"-"++e2
             | and => e1++"&"++e2
             | or => e1++"|"++e2
             | xor => e1++"^"++e2
             | sru => e1++">>"++e2
             | slu => e1++"<<"++e2
             | srs => "(intptr_t)"++e1++">>"++"(intptr_t)"++e2
             | lts => "(intptr_t)"++e1++"<"++"(intptr_t)"++e2
             | ltu => e1++"<"++e2
             | eq => e1++"=="++e2
             end%string;
     c_var := id;
     c_fun := id;
     c_act := fun _ _ _ => "#error";

     varname_eqb := string_eqb;
     rename_away_from x xs := "_" ++ x; (* FIXME *)
  |}%string.

Definition c_func := @c_func to_c_parameters.