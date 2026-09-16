Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import bedrock2.Map.SeparationLogic.
Require Export coqutil.Datatypes.OperatorOverloading.
Require Export coqutil.Datatypes.ToConversion.
Require Export bedrock2.ListIndexNotations.

#[export] Instance MulSepClause{K V: Type}{M: map.map K V}(a b: @map.rep K V M -> Prop)
  : Multiplication a b (sep a b) | 10 := {}.

#[export] Instance MulSepClauseType{K V: Type}{M: map.map K V}(a b: @map.rep K V M -> Prop)
  : @Multiplication (M -> Prop) (M -> Prop) (M -> Type) a b (sep a b) | 20 := {}.

Local Set Warnings "-notation-overridden".
Notation "a * b" := (sep a b) (only printing) : type_scope.
Notation "a * b" := (infer! Multiplication a b) (only parsing) : type_scope.
Local Set Warnings "notation-overridden".

Notation "a * b" := (sep a b) (only printing) : oo_scope.


Require Import bedrock2.Scalars.

Class PointsTo{width: Z}{mem: map.map (bits width) Byte.byte}{V: Type}
      (addr: bits width)(val: V)(pred: mem -> Prop): Prop := {}.
Global Hint Mode PointsTo + + + + + - : typeclass_instances.

(* Precedence: `*` is at level 40, and we want to bind stronger than `*`, and moreover,
   `^` is at level 30, and for consistency, we also want to bind stronger than `^`,
   so we choose 25. *)
Notation "a ~> v" := (infer! PointsTo a v)
  (at level 25, only parsing) : oo_scope.

Class PointsToPredicate{width}{mem: map.map (bits width) Byte.byte}
      (V: Type)(pred: bits width -> V -> mem -> Prop): Prop := {}.
Global Hint Mode PointsToPredicate + + + - : typeclass_instances.

(* separate typeclass because some predicates don't have a constant size *)
Class PredicateSize{width}{mem: map.map (bits width) Byte.byte}{V: Type}
      (pred: bits width -> V -> mem -> Prop){p: PointsToPredicate V pred}(sz: Z): Prop := {}.
Global Hint Mode PredicateSize + + + - - - : typeclass_instances.

#[export] Instance PointsToPredicate_to_PointsTo
 {width}{mem: map.map (bits width) Byte.byte}{V: Type}
 (pred: bits width -> V -> mem -> Prop){p: PointsToPredicate V pred}
 (a: bits width)(v: V): PointsTo a v (pred a v) := {}.

#[export] Instance PointsToScalarPredicate
 {width}{mem: map.map (bits width) Byte.byte}:
  PointsToPredicate (bits width) scalar := {}.
Notation "a ~> v" := (scalar a v)
  (at level 25, format "'[  ' a  ~>  '/' v ']'", only printing) : oo_scope.
#[export] Instance Scalar32Size{mem: map.map (bits 32) Byte.byte}:
  PredicateSize (scalar (width := 32)) 4 | 5 := {}.
#[export] Instance Scalar64Size{mem: map.map (bits 64) Byte.byte}:
  PredicateSize (scalar (width := 64)) 8 | 5 := {}.
#[export] Instance ScalarGenericSize
 {width: Z}{mem: map.map (bits width) Byte.byte}:
  PredicateSize (scalar (width := width)) (Memory.bytes_per_word width) | 6 := {}.

#[export] Instance PointsToBytePredicate
 {width}{mem: map.map (bits width) Byte.byte}:
  PointsToPredicate Byte.byte (ptsto (map := mem)) := {}.
Notation "a ~> v" := (ptsto a v) (only printing) : oo_scope.
#[export] Instance PtstoSize{width: Z}{mem: map.map (bits width) Byte.byte}:
  PredicateSize (ptsto (map := mem)) 1 := {}.


Require Import bedrock2.Array.

Class PointsToArray{width}{mem: map.map (bits width) Byte.byte}{V: Type}
      (a: bits width)(vs: list V)(pred: mem -> Prop): Prop := {}.
Notation "a --> vs" := (infer! PointsToArray a vs)
  (at level 25, only parsing) : oo_scope.
Notation "a --> vs" := (array _ _ a vs)
  (at level 25, format "'[  ' a  -->  '/' vs ']'", only printing) : oo_scope.

#[export] Instance DerivePointsToArray
 {width: Z}{mem: map.map (bits width) Byte.byte}{V: Type}
 (a: bits width)(vs: list V)(elem: bits width -> V -> mem -> Prop){p: PointsToPredicate V elem}
 (sz: Z){s: PredicateSize elem sz}:
  PointsToArray a vs (array elem (bits.of_Z width sz) a vs) := {}.

Section TestNotations.
  Context {width: Z}.
  Local Notation word := (bits width).
  Context {mem: map.map word Byte.byte}.
  Local Open Scope oo_scope.

  Goal forall (P Q: mem -> Prop), P * Q = sep P Q. intros. srefl. Abort.
  Goal forall (P Q: mem -> Prop), Lift1Prop.iff1 (P * Q) (sep P Q).
    intros. reflexivity.
  Abort.

  Goal forall (P Q R: mem -> Prop), P * Q * R = sep (sep P Q) R. intros. srefl. Abort.

  Goal forall (a1 a2 ofs sz v1 v2: word) (R: mem -> Prop) (m: mem), (R * R) m. Abort.
  Goal forall (a1 a2 ofs sz v1 v2: word) (R: mem -> Prop) (m: mem), (a1 ~> v1) m. Abort.
  Goal forall (a1 a2 ofs sz v1 v2: word) (R: mem -> Prop) (m: mem),
      (R * a1 ~> v1) m.
  Abort.
  Goal forall (a1 a2 ofs sz v1 v2: word) (R: mem -> Prop) (m: mem),
      ((a1 ~> v1) * R) m.
  Abort.
  Goal forall (a1 a2 ofs sz v1 v2: word) (R: mem -> Prop) (m: mem),
      (a1 ~> v1 * a2 ~> v2 * R) m.
    intros.
  Abort.
  Goal forall (a1 a2 ofs sz v1 v2: word) (R: mem -> Prop) (m: mem),
      ((a1 + ofs * sz) ~> v1 * a2 ~> v2 * R) m.
    intros.
  Abort.

  Goal forall (a1 a2 ofs sz: word) (vs1 vs2: list word) (R: mem -> Prop) (m: mem),
      ((a1 + ofs * sz) --> vs1 * a2 --> vs2 * R) m.
    intros.
  Abort.

  Goal forall (a1 a2 ofs sz: word) (vs1 vs2: list word) (R: mem -> Prop) (m: mem),
      ((a1 + ofs * sz) --> vs1 * a2 --> vs2[3 := (bits.of_Z width 1)] * R) m.
    intros.
  Abort.
End TestNotations.
