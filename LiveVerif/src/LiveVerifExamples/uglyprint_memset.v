Require Import Coq.Strings.String. Local Open Scope string_scope.
Require Import LiveVerifExamples.memset.
Require Import bedrock2.ToCString.
Require Import bedrock2.PrintListByte.

Definition memset_ast := Eval cbv in fst Memset.

Print memset_ast.

Definition memset_c_string := Eval vm_compute in
    (c_module (cons ("Memset", memset_ast) nil)).

(* this is almost what we want, except that the result is preceded by
   `memset_c_string = ` and enclosed in double quotes, and double quotes are duplicated
Print memset_c_string. *)

(* To fix the two above problems, we resort to some Ltac2 hacks: *)

Definition string_bytes := Eval vm_compute in list_byte_of_string memset_c_string.

Goal True.
  print_bytes string_bytes.
Abort.
