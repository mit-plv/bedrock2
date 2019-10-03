Require Import Coq.Lists.List.
Require Import compiler.util.Common.
Require Import compiler.NameGen.

Local Open Scope string_scope.

Axiom TODO_someone: False.

Instance StringNameGen: NameGen string string. refine ({|
  freshNameGenState := fun l => "_x"; (* TODO this might clash with names in l *)
  genFresh s := (s, append s "'");
  allFreshVars s := fun x => (String.length s <= String.length x)
|}).
- case TODO_someone.
- case TODO_someone.
Defined.
