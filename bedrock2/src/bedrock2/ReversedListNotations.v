Require Coq.Lists.List.

Notation "xs ;+ x" := (cons x xs)
  (at level 59, format "xs  ;+  x", left associativity) : list_scope.
Notation "xs ;++ ys" := (app ys xs)
  (at level 59, format "xs  ;++  ys", left associativity) : list_scope.
