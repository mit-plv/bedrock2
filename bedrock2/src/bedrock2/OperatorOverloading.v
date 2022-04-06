Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import bedrock2.Map.SeparationLogic.
Require Export coqutil.Datatypes.OperatorOverloading.
Require Export bedrock2.ListIndexNotations.

#[export] Instance MulSepClause{K V: Type}{M: map.map K V}(a b: @map.rep K V M -> Prop)
  : Multiplication a b (sep a b) | 10 := {}.

#[export] Instance MulSepClauseType{K V: Type}{M: map.map K V}(a b: @map.rep K V M -> Prop)
  : @Multiplication (M -> Prop) (M -> Prop) (M -> Type) a b (sep a b) | 20 := {}.

Local Set Warnings "-notation-overridden".
Notation "a * b" := (sep a b) (only printing) : type_scope.
Local Set Warnings "notation-overridden".

Notation "a * b" := (sep a b) (only printing) : oo_scope.

Notation "a * b" := (infer! Multiplication a b) (only parsing) : type_scope.


Require Import bedrock2.Scalars.

Class PointsTo{width: Z}{word: word.word width}{mem: map.map word Byte.byte}{V: Type}
      (addr: word)(val: V)(pred: mem -> Prop) := {}.

(* Precedence: `*` is at level 40, and we want to bind stronger than `*`, and moreover,
   `^` is at level 30, and for consistency, we also want to bind stronger than `^`,
   so we choose 25. *)
Notation "a |-> v" := (infer! PointsTo a v)
  (at level 25, only parsing).

#[export] Instance PointsToScalar{width}{word: word.word width}{mem: map.map word Byte.byte}
 (a v: word): PointsTo a v (scalar a v) := {}.

Notation "a |-> v" := (scalar a v)
  (at level 25, format "'[  ' a  |->  '/' v ']'", only printing).

Require Import bedrock2.Array.


Section TestNotations.
  Context {width: Z} {word: word.word width} {mem: map.map word Byte.byte}.
  Local Open Scope oo_scope.

  Goal forall (P Q: mem -> Prop), P * Q = sep P Q. intros. srefl. Abort.
  Goal forall (P Q: mem -> Prop), Lift1Prop.iff1 (P * Q) (sep P Q).
    intros. reflexivity.
  Abort.

  Goal forall (P Q R: mem -> Prop), P * Q * R = sep (sep P Q) R. intros. srefl. Abort.

  Goal forall (a1 a2 ofs sz v1 v2: word) (R: mem -> Prop) (m: mem), (R * R) m. Abort.
  Goal forall (a1 a2 ofs sz v1 v2: word) (R: mem -> Prop) (m: mem), (a1 |-> v1) m. Abort.
  Goal forall (a1 a2 ofs sz v1 v2: word) (R: mem -> Prop) (m: mem),
      (R * a1 |-> v1) m.
  Abort.
  Goal forall (a1 a2 ofs sz v1 v2: word) (R: mem -> Prop) (m: mem),
      ((a1 |-> v1) * R) m.
  Abort.
  Goal forall (a1 a2 ofs sz v1 v2: word) (R: mem -> Prop) (m: mem),
      (a1 |-> v1 * a2 |-> v2 * R) m.
    intros.
  Abort.
  Goal forall (a1 a2 ofs sz v1 v2: word) (R: mem -> Prop) (m: mem),
      ((a1 + ofs * sz) |-> v1 * a2 |-> v2 * R) m.
    intros.
  Abort.
End TestNotations.
