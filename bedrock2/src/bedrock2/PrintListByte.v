Require Import coqutil.Tactics.ident_of_string Coq.Strings.String.
From Ltac2 Require Import Ltac2 Printf Option Ltac1.

Ltac2 print_list_byte (bs : constr) := printf "%s" (string_of_constr_string constr:(string_of_list_byte $bs)).
Ltac print_list_byte := ltac2:(bs |- print_list_byte (Option.get (Ltac1.to_constr bs))).

Ltac2 Notation "print_bytes" bs(constr) := print_list_byte bs.
Tactic Notation "print_bytes" constr(bs) := print_list_byte bs.

From Coq Require Import List.
Definition allBytes: list Byte.byte :=
  map (fun nn => match Byte.of_N (BinNat.N.of_nat nn) with
                 | Some b => b
                 | None => Byte.x00 (* won't happen *)
                 end)
      (seq 0 256).

(*
Import ListNotations.
Goal True.
  Time print_bytes ([Byte.x41] ++ List.repeat Byte.x20 10000 ++ [Byte.x41]). (*0.5s*)
Abort.
*)
