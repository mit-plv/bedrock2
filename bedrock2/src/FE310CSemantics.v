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

Instance parameters : parameters. refine (
  let word := Word.Naive.word 32 eq_refl in
  let byte := Word.Naive.word 8 eq_refl in

  {|
  width := 32;
  syntax := StringNamesSyntax.make BasicCSyntax.StringNames_params;
  mem := SortedListWord.map _ _;
  locals := SortedListString.map _;
  funname_env := SortedListString.map;
  funname_eqb := String.eqb;
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
|}). Unshelve. reflexivity.
Defined.

Global Instance ok trace m0 act args :
  Morphisms.Proper
    (Morphisms.respectful
       (Morphisms.pointwise_relation Interface.map.rep
          (Morphisms.pointwise_relation (list Semantics.word) Basics.impl))
       Basics.impl) (Semantics.ext_spec trace m0 act args).
Proof.
  cbv [ext_spec parameters].
  cbv [Morphisms.Proper Morphisms.respectful Morphisms.pointwise_relation Basics.impl] in *;
  repeat match goal with |- context [string_dec ?a ?b] => destruct (string_dec a b) end;
  destruct args as [|? [|? [|]]]; intuition idtac.
  all: eapply H; eauto.
Qed.
