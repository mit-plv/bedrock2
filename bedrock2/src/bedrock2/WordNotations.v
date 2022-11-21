Require Import coqutil.Word.Interface.

Declare Scope word_scope.

Infix "^+" := word.add  (at level 50, left associativity) : word_scope.
Infix "^-" := word.sub  (at level 50, left associativity) : word_scope.
Infix "^*" := word.mul  (at level 40, left associativity) : word_scope.
Infix "^<<" := word.slu  (at level 37, left associativity) : word_scope.
Infix "^>>" := word.sru  (at level 37, left associativity) : word_scope.

(* squeeze a Z into a word (beat it with a / to make it smaller) *)
Notation "/[ x ]" := (word.of_Z x) (format "/[ x ]") : word_scope.
(* \ is the open (removed) lid of the modulo box imposed by words, *)
Notation "\[ x ]" := (word.unsigned x) (format "\[ x ]") : word_scope.
