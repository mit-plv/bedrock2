Require Import Coq.ZArith.BinInt.
Require Import compiler.NameWithEq.

Instance ZName: NameWithEq := {| name := Z |}.
