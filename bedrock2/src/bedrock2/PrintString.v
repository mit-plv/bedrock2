Require Import bedrock2.PrintListByte Coq.Strings.String.

Ltac2 print_string s := print_bytes (list_byte_of_string $s).
Ltac print_string s := print_list_byte (list_byte_of_string s).

Ltac2 Notation "print_string" s(constr) := print_string s.
Tactic Notation "print_string" constr(s) := print_string s.
