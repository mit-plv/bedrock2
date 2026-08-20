From coqutil Require Export
  Bitwidth64.

From bedrock2 Require Export
  BasicCSemantics.

Require Import ZArith.
Require Import -(hints) bedrock2.Syntax bedrock2.Semantics.

#[export] Hint Extern 0 (word.word _) => exact (Naive.word 64%Z) : typeclass_instances.
Notation word := (Naive.word 64%Z).
Notation locals := (SortedListString.map word).
Notation mem := (SortedListWord.map word (Coq.Init.Byte.byte)).

Add Ring wring : (Properties.word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (Properties.word.ring_morph (word := word)),
       constants [Properties.word_cst]).

Section TypeclassTests.
  (* word *)
  Goal Interface.word 64.
    typeclasses eauto.
  Qed.
  Goal Interface.word 32.
    Fail typeclasses eauto.
  Abort.
End TypeclassTests.
