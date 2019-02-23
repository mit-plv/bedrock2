Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Syntax.Basic bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface.
Require coqutil.Word.Naive.
Require Import coqutil.Z.HexNotation.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Axiom StrictOrderWord : forall width word, @word.ok width word -> @SortedList.parameters.strict_order (@word.rep _ word) (@word.ltu _ word).

Definition MMIOREAD : string := "MMIOREAD".
Definition MMIOWRITE : string := "MMIOWRITE".


Definition parameters : parameters := 
  let word := Word.Naive.word 32 eq_refl in
  let byte := Word.Naive.word 8 eq_refl in

  {|
  syntax := Syntax.Basic.parameters;
  mem := SortedList.map (SortedList.parameters.Build_parameters word byte word.ltu) (StrictOrderWord _ _ _);
  locals := SortedListString.map _;
  env := SortedListString.map _;
  funname_eqb := String.eqb;
  ext_spec := fun t m a args post => 
     exists addr,

   (Logic.or 
      (a = MMIOREAD /\ args = [addr] /\ forall v, post m [v]) 
      (a = MMIOWRITE /\ exists val, args = [addr;val] /\ post m []))
    /\
    (* address should be an MMIO address. we use GPIO1 and QSPI1 *)
    (((word.ltu (word.of_Z (Ox"10012000")) addr = true \/
         word.eqb (word.of_Z (Ox"10012000")) addr = true) /\
        word.ltu addr (word.of_Z (Ox"10013000")) = true)
       \/
       ((word.ltu (word.of_Z (Ox"10024000")) addr = true \/
        word.eqb (word.of_Z (Ox"10024000")) addr = true) /\
        word.ltu addr (word.of_Z (Ox"10025000")) = true));
|}.

Lemma __map_ok (_:=parameters) : Map.Interface.map.ok Semantics.mem. (* FIXME *)
  cbn.
  (* eapply SortedList.map_ok. (* fails, IDK why ~ andres *) *)
Admitted.
Existing Instance __map_ok. 