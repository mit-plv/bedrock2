Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.Syntax Coq.Strings.String.
Require Import bedrock2.Array.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition stackalloc_example :=
  cmd.stackalloc "x" (2 ^ 63) (cmd.stackalloc "y" (2 ^ 63 + 8) cmd.skip).

From bedrock2 Require Import Semantics BasicC64Semantics.

Lemma empty_post: forall fs t m l mc,
    exec fs stackalloc_example t m l mc (fun _ _ _ _ => False).
Proof.
  intros.
  unfold stackalloc_example.
  econstructor. 1: reflexivity.
  intros.
  econstructor. 1: reflexivity.
  intros. econstructor.
  do 2 eexists.
  split; [eassumption|].
  split; [eassumption|].
  do 2 eexists.
  split. 1: exact H.
  split; [eassumption|].
  (* mStack is disjoint from mStack0, but together they are bigger than
     the whole address space, so contradiction *)
Admitted.
