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
    match action, args with
    | MMIOREAD, [addr] =>
      ((Ox"10012000" <= word.unsigned addr < Ox"10013000") \/
       (Ox"10024000" <= word.unsigned addr < Ox"10025000")  ) 
      /\ forall v, post m [v]
    | MMIOWRITE, [addr; val] =>
      ((Ox"10012000" <= word.unsigned addr < Ox"10013000") \/
       (Ox"10024000" <= word.unsigned addr < Ox"10025000")  )
      /\ post m []
    | _, _ => False
    end;
|}.

Global Instance ok trace m0 act args :
  Morphisms.Proper
    (Morphisms.respectful
       (Morphisms.pointwise_relation Interface.map.rep
          (Morphisms.pointwise_relation (list Semantics.word) Basics.impl))
       Basics.impl) (Semantics.ext_spec trace m0 act args).
Proof.
  cbv [ext_spec parameters].
  cbv [Morphisms.Proper Morphisms.respectful Morphisms.pointwise_relation Basics.impl] in *.
  destruct args as [|? [|? [|]]]; intuition idtac.
  all:eapply H; eauto.
Qed.
