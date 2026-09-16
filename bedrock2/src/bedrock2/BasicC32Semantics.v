From coqutil Require Export
  Bitwidth32.

From bedrock2 Require Export
  BasicCSemantics.

Require Import -(hints) bedrock2.Syntax bedrock2.Semantics.

Require Import ZArith.

Notation word := (bits 32).
Notation locals := (SortedListString.map word).
Notation mem := (SortedListWord.map 32 (Coq.Init.Byte.byte)).

