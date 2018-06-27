(** Typeclass for decidable propositions *)
(** simplification of  fiat-crypto/src/Util/Decidable.v *)

Require Import Coq.Arith.PeanoNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.ZArith.BinInt.
Require Import Coq.NArith.NArith.
Require Import bbv.Word.
Require Import bbv.NLib.

Class Decidable (P : Prop) := dec : {P} + {~P}.
Arguments dec _%type_scope {_}.

Notation DecidableRel R := (forall x y, Decidable (R x y)).
Notation DecidableEq T := (forall (x y: T), Decidable (x = y)).

Global Instance dec_eq_nat : DecidableEq nat := Nat.eq_dec.
Global Instance dec_le_nat : DecidableRel le := Compare_dec.le_dec.
Global Instance dec_lt_nat : DecidableRel lt := Compare_dec.lt_dec.
Global Instance dec_ge_nat : DecidableRel ge := Compare_dec.ge_dec.
Global Instance dec_gt_nat : DecidableRel gt := Compare_dec.gt_dec.

Global Instance dec_eq_Z : DecidableEq Z := Z.eq_dec.
Global Instance dec_lt_Z : DecidableRel BinInt.Z.lt := ZArith_dec.Z_lt_dec.
Global Instance dec_le_Z : DecidableRel BinInt.Z.le := ZArith_dec.Z_le_dec.
Global Instance dec_gt_Z : DecidableRel BinInt.Z.gt := ZArith_dec.Z_gt_dec.
Global Instance dec_ge_Z : DecidableRel BinInt.Z.ge := ZArith_dec.Z_ge_dec.

Global Instance dec_eq_N : DecidableEq N := N.eq_dec.
Global Instance dec_lt_N : DecidableRel N.lt := Nlt_dec.

Global Instance decidable_eq_option {A} `{DecidableEq A}: DecidableEq (option A).
  intros. unfold Decidable. destruct x; destruct y.
  - destruct (DecidableEq0 a a0).
    + subst. left. reflexivity.
    + right. unfold not in *. intro E. inversion E. auto.
  - right. intro. discriminate.
  - right. intro. discriminate.
  - left. reflexivity.
Defined.

Global Instance dec_and {A B} `{Decidable A, Decidable B} : Decidable (A /\ B).
  unfold Decidable in *; destruct H; destruct H0; tauto.
Defined.

Global Instance dec_or {A B} `{Decidable A, Decidable B} : Decidable (A \/ B).
  unfold Decidable in *; destruct H; destruct H0; tauto.
Defined.

Global Instance dec_not {A} `{Decidable A} : Decidable (~ A).
  unfold Decidable in *. destruct H; tauto.
Defined.

Global Instance dec_eq_word : forall sz, DecidableEq (word sz) := weq.
