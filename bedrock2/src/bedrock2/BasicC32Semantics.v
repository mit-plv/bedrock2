From coqutil Require Export
  Bitwidth32.

From bedrock2 Require Export
  BasicCSemantics.

Require Import -(hints) bedrock2.Syntax bedrock2.Semantics.

Require Import ZArith.

#[export] Hint Extern 0 (word.word _) => exact (Naive.word 32%Z) : typeclass_instances.
Notation word := (Naive.word 32%Z).
Notation locals := (SortedListString.map word).
Notation mem := (SortedListWord.map word (Coq.Init.Byte.byte)).

Add Ring wring : (Properties.word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word)),
       constants [Properties.word_cst]).

Section TypeclassTests.
  Goal Interface.word 32.
    typeclasses eauto.
  Qed.
  Goal Interface.word 64.
    Fail typeclasses eauto.
  Abort.
End TypeclassTests.
