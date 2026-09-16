Require Import coqutil.Word.Bitwidth.

Declare Scope word_scope.

Infix "^+" := Zmod.add  (at level 50, left associativity) : word_scope.
Infix "^-" := Zmod.sub  (at level 50, left associativity) : word_scope.
Infix "^*" := Zmod.mul  (at level 40, left associativity) : word_scope.
Infix "^<<" := Zmod.slu  (at level 37, left associativity) : word_scope.
Infix "^>>" := Zmod.sru  (at level 37, left associativity) : word_scope.

(* The width of a conversion is a hole of class type: filled by unification when
   the context determines it, otherwise resolved to the width of the Bitwidth
   instance in scope. *)
Definition WordWidth := Z.
Existing Class WordWidth.
Ltac word_width_of_bitwidth :=
  let BW := constr:(_ : Bitwidth _) in
  lazymatch type of BW with Bitwidth ?w => exact w end.
Global Hint Extern 0 WordWidth => word_width_of_bitwidth : typeclass_instances.

(* squeeze a Z into a word (beat it with a / to make it smaller) *)
Notation "/[ x ]" := (bits.of_Z (_ :> WordWidth) x) (only parsing) : word_scope.
Notation "/[ x ]" := (Zmod.of_Z _ x) (only printing, format "/[ x ]") : word_scope.
(* \ is the open (removed) lid of the modulo box imposed by words, *)
Notation "\[ x ]" := (@Zmod.unsigned (2 ^ (_ :> WordWidth)) x) (only parsing) : word_scope.
Notation "\[ x ]" := (Zmod.unsigned x) (only printing, format "\[ x ]") : word_scope.
