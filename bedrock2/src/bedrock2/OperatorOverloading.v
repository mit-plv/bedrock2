Require Import Coq.ZArith.ZArith.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
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

Class PointsTo{width: Z}{word: word.word width}{mem: map.map word Byte.byte}{V: Type}
      (addr: word)(val: V)(pred: mem -> Prop) := {}.
Global Hint Mode PointsTo + + + + + + - : typeclass_instances.

(* Precedence: `*` is at level 40, and we want to bind stronger than `*`, and moreover,
   `^` is at level 30, and for consistency, we also want to bind stronger than `^`,
   so we choose 25. *)
Notation "a ~> v" := (infer! PointsTo a v)
  (at level 25, only parsing) : oo_scope.

Class PointsToPredicate{width}{word: word.word width}{mem: map.map word Byte.byte}
      (V: Type)(pred: word -> V -> mem -> Prop) := {}.
Global Hint Mode PointsToPredicate + + + + - : typeclass_instances.

(* separate typeclass because some predicates don't have a constant size *)
Class PredicateSize{width}{word: word.word width}{mem: map.map word Byte.byte}{V: Type}
      (pred: word -> V -> mem -> Prop){p: PointsToPredicate V pred}(sz: Z) := {}.
Global Hint Mode PredicateSize + + + + - - - : typeclass_instances.

#[export] Instance PointsToPredicate_to_PointsTo
 {width}{word: word.word width}{mem: map.map word Byte.byte}{V: Type}
 (pred: word -> V -> mem -> Prop){p: PointsToPredicate V pred}
 (a: word)(v: V): PointsTo a v (pred a v) := {}.

#[export] Instance PointsToScalarPredicate
 {width}{word: word.word width}{mem: map.map word Byte.byte}:
  PointsToPredicate word scalar := {}.
Notation "a ~> v" := (scalar a v)
  (at level 25, format "'[  ' a  ~>  '/' v ']'", only printing) : oo_scope.
#[export] Instance Scalar32Size{word: word.word 32}{mem: map.map word Byte.byte}:
  PredicateSize (scalar (word := word)) 4 | 5 := {}.
#[export] Instance Scalar64Size{word: word.word 64}{mem: map.map word Byte.byte}:
  PredicateSize (scalar (word := word)) 8 | 5 := {}.
#[export] Instance ScalarGenericSize
 {width: Z}{word: word.word width}{mem: map.map word Byte.byte}:
  PredicateSize (scalar (word := word)) (Memory.bytes_per_word width) | 6 := {}.

#[export] Instance PointsToBytePredicate
 {width}{word: word.word width}{mem: map.map word Byte.byte}:
  PointsToPredicate Byte.byte (ptsto (map := mem)) := {}.
Notation "a ~> v" := (ptsto a v) (only printing) : oo_scope.
#[export] Instance PtstoSize{width: Z}{word: word.word width}{mem: map.map word Byte.byte}:
  PredicateSize (ptsto (map := mem)) 1 := {}.


Require Import bedrock2.Array.

Class PointsToArray{width}{word: word.word width}{mem: map.map word Byte.byte}{V: Type}
      (a: word)(vs: list V)(pred: mem -> Prop) := {}.
Notation "a --> vs" := (infer! PointsToArray a vs)
  (at level 25, only parsing) : oo_scope.
Notation "a --> vs" := (array _ _ a vs)
  (at level 25, format "'[  ' a  -->  '/' vs ']'", only printing) : oo_scope.

#[export] Instance DerivePointsToArray
 {width: Z}{word: word.word width}{mem: map.map word Byte.byte}{V: Type}
 (a: word)(vs: list V)(elem: word -> V -> mem -> Prop){p: PointsToPredicate V elem}
 (sz: Z){s: PredicateSize elem sz}:
  PointsToArray a vs (array elem (word.of_Z sz) a vs) := {}.

Section TestNotations.
  Context {width: Z} {word: word.word width} {mem: map.map word Byte.byte}.
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
      ((a1 + ofs * sz) --> vs1 * a2 --> vs2[3 := word.of_Z (word := word) 1] * R) m.
    intros.
  Abort.
End TestNotations.
