From Coq Require Import String.
Require Import Ltac2.Ltac2.

(* Converts the lower i + 1 bits of an Ltac2 integer into a bool list
  (lower bits to the left) where 0 is false and 1 is true *)
Ltac2 rec int_to_bits_rec(val: int)(i: int) :=
  if Int.lt i 0 then [] else
    (Int.equal (Int.land (Int.lsr val i) 1) 1)
      :: int_to_bits_rec val (Int.sub i 1).

Ltac2 char_to_bits(c: char) :=
  int_to_bits_rec (Char.to_int c) 7.

Ltac2 bool_to_coq(b: bool) :=
  if b then constr:(true) else constr:(false).

Ltac2 mkApp(f: constr)(args: constr array) :=
  Constr.Unsafe.make (Constr.Unsafe.App f args).

Ltac2 char_to_ascii(c: char) :=
  mkApp constr:(Ascii.Ascii)
        (Array.of_list (List.rev (List.map bool_to_coq (char_to_bits c)))).

Ltac2 rec string_to_coq_rec(s: string)(i: int)(acc: constr) :=
  if Int.lt i 0 then acc else
    let c := char_to_ascii (String.get s i) in
    string_to_coq_rec s (Int.sub i 1) constr:(String.String $c $acc).

Ltac2 string_to_coq(s: string) :=
  string_to_coq_rec s (Int.sub (String.length s) 1) constr:(String.EmptyString).

Ltac2 ident_to_coq(i: ident) := string_to_coq (Ident.to_string i).

Ltac2 Type exn ::= [ Not_a_Var (constr) ].

Ltac2 varconstr_to_coq(c: constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var i => ident_to_coq i
  | _ => Control.throw (Not_a_Var c)
  end.

(* Test:
   Ltac2 Eval string_to_coq "hello world".
   Goal forall a: nat, a = a. intros.
   Ltac2 Eval varconstr_to_coq constr:(a).
*)

Ltac2 exact_varconstr_as_string(c: constr) :=
  let s := varconstr_to_coq c in exact $s.

Ltac exact_varconstr_as_string :=
  ltac2:(c |- exact_varconstr_as_string (Option.get (Ltac1.to_constr c))).

Inductive PassStringFromLtac2ToLtac1 := mkPassStringFromLtac2ToLtac1 (s: string).

Ltac2 pose_varconstr_as_wrapped_string(c: constr) :=
  let s := varconstr_to_coq c in pose (mkPassStringFromLtac2ToLtac1 $s).

Ltac pose_varconstr_as_wrapped_string :=
  ltac2:(s |- pose_varconstr_as_wrapped_string (Option.get (Ltac1.to_constr s))).

Ltac varconstr_to_string c :=
  let __ := match constr:(Set) with
            | _ => pose_varconstr_as_wrapped_string c
            end in
  match goal with
  | x := mkPassStringFromLtac2ToLtac1 ?s |- _ =>
    let __ := match constr:(Set) with _ => clear x end in s
  end.

Local Open Scope string_scope.
Set Default Proof Mode "Classic".
Goal forall my_var: nat, my_var = my_var.
  intros.
  match goal with
  | |- _ = ?x => let r := varconstr_to_string x in pose r
  end.
  match goal with
  | H: nat |- _ => let r := varconstr_to_string H in pose r
  end.
Abort.

Inductive Ltac2IdentToPass := mkLtac2IdentToPass.

(* Trick from https://pit-claudel.fr/clement/papers/koika-dsls-CoqPL21.pdf *)
Ltac serialize_ident_in_context :=
  ltac2:(match! goal with
         | [ h: Ltac2IdentToPass |- _  ] =>
           let s := ident_to_coq h in exact $s
         end).

Notation ident_to_string a :=
  (match mkLtac2IdentToPass return string with
   | a => ltac:(serialize_ident_in_context)
   end) (only parsing).
