Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.BasicC64Syntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface.
Require coqutil.Word.Naive.

Axiom StrictOrderWord : forall width word, @word.ok width word -> @SortedList.parameters.strict_order (@word.rep _ word) (@word.ltu _ word).

Existing Instance Word.Naive.ok.
Instance parameters : parameters :=
  let word := Word.Naive.word 64 eq_refl in
  let byte := Word.Naive.word 8 eq_refl in
  {|
  syntax := StringNamesSyntax.make BasicC64Syntax.StringNames_params;
  mem := SortedList.map (SortedList.parameters.Build_parameters word byte word.ltu) (StrictOrderWord _ _ _);
  locals := SortedListString.map _;
  env := SortedListString.map _;
  funname_eqb := String.eqb;
  ext_spec := fun _ _ _ _ _ => False;
|}.
