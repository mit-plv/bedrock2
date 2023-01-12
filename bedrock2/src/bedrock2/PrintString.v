Require Import coqutil.Tactics.ident_of_string Coq.Strings.String.
From Ltac2 Require Import Ltac2 Printf Option Ltac1.

Ltac2 print_string s := printf "%s" (string_of_constr_string s).
Ltac print_string := ltac2:( s |- print_string (Option.get (Ltac1.to_constr s))).

Ltac2 Notation "print_string" s(constr) := print_string s.
Tactic Notation "print_string" constr(s) := print_string s.
