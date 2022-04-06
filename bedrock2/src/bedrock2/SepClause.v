Require Export Coq.ZArith.ZArith.
Require Export coqutil.Byte.
Require Export coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.OfListWord.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require Export bedrock2.Map.Separation bedrock2.Map.SeparationLogic.

(* Try to treat this type as abstractly as possible, as we might change the
   argument order from `word -> V -> mem -> Prop` to `V -> word -> mem -> Prop`,
   or make it a record or typeclass with additional size info. *)
Definition sep_predicate{width: Z}{word: word width}(mem: map.map word byte)(V: Type) :=
  word -> V -> mem -> Prop.

(* TODO deprecate this scope and notation *)
Declare Scope sepcl_scope.
(* Precedence: `*` is at level 40, and we want to bind stronger than `*`, and moreover,
   `^` is at level 30, and for consistency, we also want to bind stronger than `^`,
   so we choose 25. To avoid conflict with type annotation, we put v at level 99.
   Order: Mimics hypothesis with a body, eg in `x := 1 : Z`, the order is
   "label, value, type". *)
Notation "a :-> v : p" := (p a v) (at level 25, v at level 99, only parsing) : sepcl_scope.
Open Scope sepcl_scope.
