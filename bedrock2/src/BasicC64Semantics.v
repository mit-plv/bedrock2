Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.BasicC64Syntax bedrock2.Semantics.
Require bedrock2.String bedrock2.Map.SortedList bedrock2.Map.SortedListString.
Require Import coqutil.Word.Interface.
Require coqutil.Word.Naive.

Instance parameters : parameters :=
  let word := Word.Naive.word 64 eq_refl in
  let byte := Word.Naive.word 8 eq_refl in
  {|
  syntax := StringNamesSyntax.make BasicC64Syntax.StringNames_params;
  mem := SortedList.map (SortedList.parameters.Build_parameters word byte word.eqb word.ltu);
  locals := SortedListString.map _;
  interp_binop := Basic_bopnames.interp_binop;
  funname_eqb := String.eqb;
|}.
Existing Instance Word.Naive.ok.