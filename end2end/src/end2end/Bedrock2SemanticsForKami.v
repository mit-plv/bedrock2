Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.BasicCSyntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface coqutil.Map.SortedListWord.
Require Import coqutil.Z.HexNotation.
Require Import processor.KamiWord.
Require Import compilerExamples.MMIO.

Import String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition MMIOREAD : string := "MMIOREAD".
Definition MMIOWRITE : string := "MMIOWRITE".

Instance word: word.word 32 := KamiWord.word 32.
Instance byte: word.word 8 := KamiWord.word 8.

Instance word_ok: word.ok word := KamiWord.ok 32 eq_refl.
Instance byte_ok: word.ok byte := KamiWord.ok 8 eq_refl.


Instance semantics: Semantics.parameters. refine ({|
  width := 32;
  syntax := StringNamesSyntax.make BasicCSyntax.StringNames_params;
  varname_eqb := String.eqb;
  funname_eqb := String.eqb;
  actname_eqb := String.eqb;
  mem := SortedListWord.map _ _;
  locals := SortedListString.map _;
  funname_env := SortedListString.map;
  ext_spec := _;
|}).
unshelve refine (@MMIO.bedrock2_interact {| MMIO.funname_env := SortedListString.map |}).
eapply SortedListString.ok.
Defined.

Instance ok : Semantics.parameters_ok semantics.
Proof.
  split; cbv [funname_env locals mem semantics]; try exact _.
  { cbv; auto. }
  { eapply SortedListString.ok. }
  { intros; eapply SortedListString.ok. }
  (* case TODO. abstracting over TODO leads to untypable term! *)
Admitted.

(* TODO why does typeclass search fail here? *)
Instance mapok: Interface.map.ok mem := SortedListWord.ok word _.

Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := Semantics.word)),
       constants [Properties.word_cst]).
Add Ring bring : (Properties.word.ring_theory (word := Semantics.byte))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := Semantics.byte)),
       constants [Properties.word_cst]).
