Require Import bedrock2.Syntax.

(* A variant of load whose effects on the symbolic state (such as splitting
   arrays and casting from one sep predicate to another) are not persisted *)
Definition deref := expr.load.
