Require Import Coq.ZArith.BinInt Coq.omega.Omega.
Require Import bedrock2.Semantics bedrock2.BasicC64Semantics.

Set Printing All.
Set Printing Universes.

Goal width = 0 -> width = 0.
  intros H.
  (*   H : @eq Z (@width parameters@{bedrock2.Universes.343}) Z0 *)
  (* Goal: @eq Z (@width parameters@{bedrock2.Universes.343}) Z0 *)
  assert_succeeds (enough True; [omega|]).

  change tt with tt in H.
  (* H : @eq Z *)
  (*       (@width@{Set Set Set Set bedrock2.Universes.343 Set Set Set Set Set *)
  (*        Set bedrock2.Universes.343} parameters@{bedrock2.Universes.343}) Z0 *)
  (* Goal: @eq Z (@width parameters@{bedrock2.Universes.343}) Z0 *)
  assert_succeeds (enough True; [omega|]).
  (* Tactic failure: <tactic closure> fails. *)
  Omega.omega.
  (* Error: Omega can't solve this system *)
Qed.