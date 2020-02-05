Require Import Coq.Lists.List.
Require Import compiler.util.Common.
Require Import compiler.NameGen.

Local Open Scope string_scope.

Local Axiom TODO_someone_freshnames: False.

Instance StringNameGen: NameGen string string. refine ({|
  freshNameGenState := fun l => "_x"; (* TODO this might clash with names in l *)
  genFresh s := (s, append s "'");
  allFreshVars s := fun x => (String.length s <= String.length x)
|}).
- case TODO_someone_freshnames.
- case TODO_someone_freshnames.
Defined.
