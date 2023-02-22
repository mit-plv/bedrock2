Require Import Ltac2.Ltac2. Set Default Proof Mode "Classic".

(* TODO most of this could/should be upstreamed to Coq *)

Module Char.
  Ltac2 equal(c1: char)(c2: char) := Int.equal (Char.to_int c1) (Char.to_int c2).
End Char.

Module String.
  Local Ltac2 rec starts_with_iter(i: int)(prefix: string)(s: string) :=
    if Int.le (String.length prefix) i then true
    else if Int.le (String.length s) i then false
         else if Char.equal (String.get prefix i) (String.get s i)
              then starts_with_iter (Int.add i 1) prefix s
              else false.

  Ltac2 starts_with(prefix: string)(s: string) := starts_with_iter 0 prefix s.
End String.

Module Ident.
  Ltac2 starts_with(prefix: ident)(i: ident) :=
    String.starts_with (Ident.to_string prefix) (Ident.to_string i).
End Ident.

Ltac _ident_starts_with := ltac2:(prefix i |-
  if Ident.starts_with (Option.get (Ltac1.to_ident prefix)) (Option.get (Ltac1.to_ident i))
  then ()
  else Control.backtrack_tactic_failure "ident does not start with given prefix").

Tactic Notation "ident_starts_with" ident(prefix) ident(i) :=
  _ident_starts_with prefix i.

Goal True.
  assert_succeeds (idtac; ident_starts_with __a __ab).
  assert_succeeds (idtac; ident_starts_with x123 x123).
  assert_fails (idtac; ident_starts_with __ax __ab).
  assert_fails (idtac; ident_starts_with a b).
  assert_fails (idtac; ident_starts_with looong lo).
Abort.
