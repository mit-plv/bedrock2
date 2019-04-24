Require Import Coq.Lists.List.
Require Import compiler.util.Common.
Require Import compiler.NameGen.

Local Set Refine Instance Mode.
Local Open Scope string_scope.

Axiom TODO: False.

Instance StringNameGen: NameGen string string := {
  freshNameGenState := fun l => "_x"; (* TODO this might clash with names in l *)
  genFresh s := (s, append s "'");
  allFreshVars s := fun x => (String.length s <= String.length x)
}.
- case TODO.
- case TODO.
Defined.
