Require Import Coq.Strings.String.
Require Import Coq.Strings.Ascii.
Require Import Ltac2.Ltac2.
Require Ltac2.Option.

Ltac2 bool_to_int(c: constr) :=
  lazy_match! c with
  | true => 1
  | false => 0
  end.

Ltac2 rec bool_list_to_int(l: constr list) :=
  match l with
  | [] => 0
  | b :: bs => Int.add (bool_to_int b) (Int.mul 2 (bool_list_to_int bs))
  end.

Ltac2 ascii_to_int(c: constr) :=
  lazy_match! c with
  | Ascii ?b0 ?b1 ?b2 ?b3 ?b4 ?b5 ?b6 ?b7 => bool_list_to_int [b0; b1; b2; b3; b4; b5; b6; b7]
  end.

Ltac2 rec string_length(s: constr) :=
  lazy_match! s with
  | EmptyString => 0
  | String _ ?rest => Int.add 1 (string_length rest)
  end.

Ltac2 rec set_string_chars(start: int)(src: constr)(dest: string) :=
  lazy_match! src with
  | EmptyString => ()
  | String ?c ?rest =>
    String.set dest start (Char.of_int (ascii_to_int c));
    set_string_chars (Int.add start 1) rest dest
  end.

Ltac2 string_to_ltac2(s: constr) :=
  let buf := String.make (string_length s) (Char.of_int 0) in
  set_string_chars 0 s buf;
  buf.

Ltac2 string_to_ident(s: constr) := Option.get (Ident.of_string (string_to_ltac2 s)).

(* Test
Open Scope string_scope.
Ltac2 Eval string_to_ltac2 constr:("hello world").
Ltac2 Eval string_to_ident constr:("my_var_name").
*)
