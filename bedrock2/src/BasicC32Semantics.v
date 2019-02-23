Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Syntax.Basic bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface.
Require coqutil.Word.Naive.

Axiom StrictOrderWord : forall width word, @word.ok width word -> @SortedList.parameters.strict_order (@word.rep _ word) (@word.ltu _ word).

Definition parameters : parameters :=
  let word := Word.Naive.word 32 eq_refl in
  let byte := Word.Naive.word 8 eq_refl in
  {|
  syntax := Syntax.Basic.parameters;
  mem := SortedList.map (SortedList.parameters.Build_parameters word byte word.ltu) (StrictOrderWord _ _ _);
  locals := SortedListString.map _;
  env := SortedListString.map _;
  funname_eqb := String.eqb;
  ext_spec := fun _ _ _ _ _ => False;
|}.