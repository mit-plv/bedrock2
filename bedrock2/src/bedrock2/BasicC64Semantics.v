From coqutil Require Export
  Bitwidth64.

From bedrock2 Require Export
  BasicCSemantics.

Require Import ZArith.
Require Import -(hints) bedrock2.Syntax bedrock2.Semantics.

Notation word := (bits 64).
Notation locals := (SortedListString.map word).
Notation mem := (SortedListWord.map 64 (Coq.Init.Byte.byte)).

