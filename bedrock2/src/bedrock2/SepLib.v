Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Datatypes.ZList. Import ZList.List.ZIndexNotations.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Array bedrock2.Scalars.

(* PredTp equals `Z -> mem -> Prop` if the predicate takes any number of values
   and its size depends on these values.
   PredTp equals `V1 -> ... -> Vn -> Z -> mem -> Prop` for some `V1..Vn` if the
   predicate takes `n` values, but its size does not depend on these values. *)
Definition PredicateSize{PredTp: Type}(pred: PredTp) := Z.
Existing Class PredicateSize.

(* Derives the size of a value-independent predicate applied to a value *)
#[export] Hint Extern 4 (PredicateSize (?pred ?v)) =>
  lazymatch constr:(_: PredicateSize pred) with
  | ?sz => exact sz
  end
: typeclass_instances.

Definition array{width}{BW: Bitwidth width}{word: word width}
  {mem: map.map word Byte.byte}{T: Type}
  (elem: T -> word -> mem -> Prop){elemSize: PredicateSize elem}
  (n: Z)(vs: list T)(addr: word): mem -> Prop :=
  sep (emp (len vs = n))
      (array (fun a v => elem v a) (word.of_Z elemSize) addr vs).

(* Note: We don't pass a list ?vs to the pattern, because the length is already given by n *)
#[export] Hint Extern 1
  (PredicateSize (@array ?width ?BW ?word ?mem ?T ?elem ?elemSize ?n)) =>
  exact (n * elemSize) : typeclass_instances.


(* Type aliases that can inform proof automation, typeclass search,
   as well as humans on intended usage: *)
Definition uint_t(nbits: Z) := Z.
Definition array_t(tp: Type)(nElems: Z) := list tp.

Global Hint Opaque uint_t array_t : typeclass_instances.


Definition nbits_to_nbytes(nbits: Z): Z := (Z.max 0 nbits + 7) / 8.

Lemma nbits_to_nbytes_nonneg: forall nbits, 0 <= nbits_to_nbytes nbits.
Proof. intros. unfold nbits_to_nbytes. Z.to_euclidean_division_equations. lia. Qed.

Lemma nbits_to_nbytes_8: forall n, 0 <= n -> nbits_to_nbytes (8 * n) = n.
Proof.
  intros. unfold nbits_to_nbytes. Z.to_euclidean_division_equations. lia.
Qed.


Definition uint{width}{BW: Bitwidth width}{word: word width}{mem: map.map word Byte.byte}
  (nbits: Z)(v: Z)(addr: word): mem -> Prop :=
  sep (emp (0 <= v < 2 ^ nbits))
      (littleendian (Z.to_nat (nbits_to_nbytes nbits)) addr v).

#[export] Hint Extern 1 (PredicateSize (uint ?nbits)) =>
  let sz := lazymatch isZcst nbits with
            | true => eval cbv in (nbits_to_nbytes nbits)
            | false => constr:(nbits_to_nbytes nbits)
            end in
  exact sz
: typeclass_instances.
