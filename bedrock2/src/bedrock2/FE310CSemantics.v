Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.BasicCSyntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface coqutil.Map.SortedListWord.
Require coqutil.Word.Naive.
Require Import coqutil.Z.HexNotation.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition MMIOREAD : string := "MMIOREAD".
Definition MMIOWRITE : string := "MMIOWRITE".

Instance parameters : parameters :=
  let word := Naive.word32 in
  let byte := Naive.word8 in

  {|
  width := 32;
  syntax := StringNamesSyntax.make BasicCSyntax.StringNames_params;
  varname_eqb := String.eqb;
  funname_eqb := String.eqb;
  actname_eqb := String.eqb;
  mem := SortedListWord.map _ _;
  locals := SortedListString.map _;
  funname_env := SortedListString.map;
  ext_spec t m action args post :=
    if string_dec action MMIOREAD then
    match args with
    | [addr] =>
      ((Ox"10012000" <= word.unsigned addr < Ox"10013000") \/
       (Ox"10024000" <= word.unsigned addr < Ox"10025000")  )
      /\ forall v, post m [v]
    | _ => False
    end else
    if string_dec action MMIOWRITE then
    match args with
    | [addr; val] =>
      ((Ox"10012000" <= word.unsigned addr < Ox"10013000") \/
       (Ox"10024000" <= word.unsigned addr < Ox"10025000")  )
      /\ post m []
    |  _ => False
    end else False;
|}.

Global Instance ok : Semantics.parameters_ok parameters.
Proof.
  split; cbv [funname_env locals mem parameters]; try exact _. 
  { cbv; auto. }
  { eapply SortedListString.ok. }
  { intros; eapply SortedListString.ok. }
  split.
  { admit. }
  { cbv [ext_spec parameters]; intros.
    cbv [Morphisms.Proper Morphisms.respectful Morphisms.pointwise_relation Basics.impl] in *;
      repeat match goal with |- context [string_dec ?a ?b] => destruct (string_dec a b) end;
      destruct args as [|? [|? [|]]]; intuition idtac.
    all: eapply H; eauto. }
  { admit. }
Admitted.

(* TODO why does typeclass search fail here? *)
Instance mapok: Interface.map.ok mem := SortedListWord.ok Naive.word32 _.
Instance wordok: word.ok Semantics.word := Naive.word32_ok.
Instance byteok: word.ok Semantics.byte := Naive.word8_ok.
Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := Semantics.word)),
       constants [Properties.word_cst]).
Add Ring bring : (Properties.word.ring_theory (word := Semantics.byte))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := Semantics.byte)),
       constants [Properties.word_cst]).
