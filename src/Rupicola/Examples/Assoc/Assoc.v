Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax. Import Syntax.Coercions.
Require Import bedrock2.NotationsCustomEntry.
(* Require bedrock2.WeakestPrecondition. *)

Local Open Scope Z_scope.
Local Open Scope string_scope.
Import ListNotations.

Module Bedrock2.
  Definition func : Type :=
    string * (list string * list string * cmd).

  Axiom word_size : Z.
  Definition pair_size : Z := 4 (* key *) + word_size (* pointer *).

  Notation pairs := ("pairs" : string).
  Notation len := ("len" : string).
  Notation k := ("k" : string).

  Notation found := ("found" : string).
  Notation out := ("out" : string).

  Notation pairs_end := ("pairs_end" : string).
  Notation key := ("key" : string).

  Definition assoc_found : func :=
    ("assoc",
     ([pairs; len; k],
      [found; out],
      bedrock_func_body:(
       found = $0;
       pairs_end = (pairs + pair_size * len);
       while ((pairs < pairs_end) & (found == $0)) {{
         key = (load4(pairs));
         if (key == k) {{
           store(out, pairs);
           found = $1
         }};
         pairs = (pairs + pair_size)
       }}))).

  Definition assoc_skip : func :=
    ("assoc",
     ([pairs; len; k],
      [found; out],
      bedrock_func_body:(
       pairs_end = (pairs + pair_size * len);
       while (pairs < pairs_end) {{
         key = (load4(pairs));
         if (key == k) {{
           store(out, pairs);
           pairs = (pairs_end)
         }} else {{
           pairs = (pairs + pair_size)
         }}
       }};
       found = ((pairs == pairs_end) ^ $1)))).
End Bedrock2.

Module Gallina.
  Axiom key : Type.
  Axiom value : Type.
  Axiom k_eqb : key -> key -> bool.

  Record pair := { k: key; v: value }.

  Definition assoc (pairs: list pair) (needle: key) : option pair :=
    List.find (fun (p: pair) => k_eqb p.(k) needle) pairs.
End Gallina.
