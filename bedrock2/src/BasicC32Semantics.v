Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.BasicCSyntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface coqutil.Map.SortedListWord.
Require coqutil.Word.Naive.

Instance parameters : parameters :=
  let word := Naive.word32 in
  let byte := Naive.word8 in
  {|
  width := 32;
  syntax := StringNamesSyntax.make BasicCSyntax.StringNames_params;
  mem := SortedListWord.map _ _;
  locals := SortedListString.map _;
  funname_env := SortedListString.map;
  funname_eqb := String.eqb;
  ext_spec := fun _ _ _ _ _ => False;
|}.

Instance mapok: coqutil.Map.Interface.map.ok mem := SortedListWord.ok Naive.word32 _.
Instance wordok: coqutil.Word.Interface.word.ok Semantics.word := Naive.word32_ok.
Instance byteok: coqutil.Word.Interface.word.ok Semantics.byte := Naive.word8_ok.
Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := Semantics.word)),
       constants [Properties.word_cst]).
Add Ring bring : (Properties.word.ring_theory (word := Semantics.byte))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := Semantics.byte)),
       constants [Properties.word_cst]).