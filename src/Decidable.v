(** Typeclass for decidable propositions *)
(** simplification of  fiat-crypto/src/Util/Decidable.v *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.

Class Decidable (P : Prop) := dec : {P} + {~P}.
Arguments dec _%type_scope {_}.

Notation DecidableRel R := (forall x y, Decidable (R x y)).
Notation DecidableEq T := (forall (x y: T), Decidable (x = y)).

Global Instance dec_eq_nat : DecidableEq nat := Nat.eq_dec.
Global Instance dec_le_nat : DecidableRel le := Compare_dec.le_dec.
Global Instance dec_lt_nat : DecidableRel lt := Compare_dec.lt_dec.
Global Instance dec_ge_nat : DecidableRel ge := Compare_dec.ge_dec.
Global Instance dec_gt_nat : DecidableRel gt := Compare_dec.gt_dec.
