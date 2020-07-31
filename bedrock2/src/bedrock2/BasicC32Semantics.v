Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require coqutil.Datatypes.String coqutil.Map.SortedList coqutil.Map.SortedListString.
Require Import coqutil.Word.Interface coqutil.Map.SortedListWord.
Require coqutil.Word.Naive.

Instance parameters : parameters :=
  let word := Naive.word32 in
  {|
  width := 32;
  mem := SortedListWord.map _ _;
  locals := SortedListString.map _;
  env := SortedListString.map _;
  ext_spec := fun _ _ _ _ _ => False;
|}.

Global Instance ok trace m0 act args :
  Morphisms.Proper
    (Morphisms.respectful
       (Morphisms.pointwise_relation Interface.map.rep
          (Morphisms.pointwise_relation (list Semantics.word) Basics.impl))
       Basics.impl) (Semantics.ext_spec trace m0 act args).
Proof.
  cbn in *.
  unfold Morphisms.Proper, Morphisms.respectful, Morphisms.pointwise_relation, Basics.impl.
  intros.
  assumption.
Qed.

Instance localsok: coqutil.Map.Interface.map.ok locals := SortedListString.ok _.
Instance mapok: coqutil.Map.Interface.map.ok mem := SortedListWord.ok Naive.word32 _.
Instance wordok: coqutil.Word.Interface.word.ok Semantics.word := Naive.word32_ok.
Add Ring wring : (Properties.word.ring_theory (word := Semantics.word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := Semantics.word)),
       constants [Properties.word_cst]).

Global Instance ext_spec_ok trace m0 act args :
  Morphisms.Proper
    (Morphisms.respectful
       (Morphisms.pointwise_relation Interface.map.rep
          (Morphisms.pointwise_relation (list Semantics.word) Basics.impl))
       Basics.impl) (Semantics.ext_spec trace m0 act args).
Proof.
  cbn in *.
  unfold Morphisms.Proper, Morphisms.respectful, Morphisms.pointwise_relation, Basics.impl.
  intros.
  assumption.
Qed.

Instance parameters_ok : parameters_ok parameters.
  constructor; intros; try typeclasses eauto.
  - cbv. left. reflexivity.
  - unfold env, parameters. exact (SortedListString.ok _).
  - constructor.
    all: try typeclasses eauto; intros; cbn in *; contradiction.
Qed.
