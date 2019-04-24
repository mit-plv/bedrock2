Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.BasicCSyntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface coqutil.Map.SortedListWord.
Require coqutil.Word.Naive.

Instance parameters : parameters :=
  let word := Word.Naive.word 32 eq_refl in
  let byte := Word.Naive.word 8 eq_refl in
  {|
  width := 32;
  syntax := StringNamesSyntax.make BasicCSyntax.StringNames_params;
  mem := SortedListWord.map _ _;
  locals := SortedListString.map _;
  funname_env := SortedListString.map;
  funname_eqb := String.eqb;
  ext_spec := fun _ _ _ _ _ => False;
|}.

Instance mapok: coqutil.Map.Interface.map.ok mem := SortedListWord.ok (Naive.word 32 eq_refl) _.
Instance wordok: coqutil.Word.Interface.word.ok Semantics.word := coqutil.Word.Naive.ok _ _.
Instance byteok: coqutil.Word.Interface.word.ok Semantics.byte := coqutil.Word.Naive.ok _ _.
