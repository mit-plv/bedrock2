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

Module parameters.
  Class parameters := {
    word :> Word.Interface.word 32;
    word_ok :> word.ok word; (* for impl of mem below *)
    byte :> Word.Interface.word 8;
    byte_ok :> word.ok byte; (* for impl of mem below *)
    mem :> Interface.map.map word byte;
    mem_ok :> Interface.map.ok mem; (* for impl of mem below *)
  }.
End parameters. Notation parameters := parameters.parameters.

Section WithParameters.
  Context {p : parameters}.
  Global Instance semantics_parameters  : Semantics.parameters :=
    {|
    syntax := StringNamesSyntax.make BasicCSyntax.StringNames_params;
    Semantics.word := parameters.word;
    Semantics.byte := parameters.byte;
    varname_eqb := String.eqb;
    funname_eqb := String.eqb;
    actname_eqb := String.eqb;
    mem := parameters.mem;
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
  
  Axiom TODO_andres_differential_memory_log : False.
  Global Instance ok : Semantics.parameters_ok semantics_parameters.
  Proof.
    split; cbv [funname_env locals mem semantics_parameters]; try exact _.
    { cbv; auto. }
    { exact (SortedListString.ok _). }
    { exact SortedListString.ok. }
    split.
    { case TODO_andres_differential_memory_log. }
    1,2:
      cbv [ext_spec semantics_parameters]; intros;
      cbv [Morphisms.Proper Morphisms.respectful Morphisms.pointwise_relation Basics.impl] in *;
        repeat match goal with |- context [string_dec ?a ?b] => destruct (string_dec a b) end;
        destruct args as [|? [|? [|]]]; intuition eauto.
  Qed.
  
  (* COPY-PASTE these *)
  Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.word)),
         constants [Properties.word_cst]).
  Add Ring bring : (Properties.word.ring_theory (word := Semantics.byte))
        (preprocess [autorewrite with rew_word_morphism],
         morphism (Properties.word.ring_morph (word := Semantics.byte)),
         constants [Properties.word_cst]).
End WithParameters.
