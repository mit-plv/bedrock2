Require Import lib.fiat_crypto_tactics.Test.

(** [not tac] is equivalent to [fail tac "succeeds"] if [tac] succeeds, and is equivalent to [idtac] if [tac] fails *)
Tactic Notation "not" tactic3(tac) := try ((test tac); fail 1 tac "succeeds").
