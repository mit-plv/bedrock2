Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import bedrock2.Syntax.
Require Import bedrock2.BasicCSyntax.
Require Import bedrock2.NotationsCustomEntry.
(* Require bedrock2.WeakestPrecondition. *)

Local Open Scope Z_scope.
Local Open Scope string_scope.
Import ListNotations.

Module Bedrock2.
  Local Existing Instance bedrock2.BasicCSyntax.StringNames_params.

  Definition bedrock_func : Type :=
    funname * (list varname * list varname * cmd).

  Local Coercion literal (z : Z) : Syntax.expr := expr.literal z.
  Local Coercion var (x : string) : Syntax.expr := expr.var x.
  Local Coercion name_of_func (f : bedrock_func) := fst f.

  Axiom word_size : Z.
  Definition pair_size : Z := 4 (* key *) + word_size (* pointer *).

  Notation pairs := ("pairs" : varname).
  Notation len := ("len" : varname).
  Notation k := ("k" : varname).

  Notation found := ("found" : varname).
  Notation out := ("out" : varname).

  Notation pairs_end := ("pairs_end" : varname).
  Notation key := ("key" : varname).

  Definition assoc_found : bedrock_func :=
    ("assoc",
     ([pairs; len; k],
      [found; out],
      bedrock_func_body:(
       found = (constr:(0));
       pairs_end = (pairs + pair_size * len);
       while ((pairs < pairs_end) & (found == constr:(0))) {{
         key = (load4(pairs));
         if (key == k) {{
           store(out, pairs);
           found = (constr:(1))
         }};
         (* FIXME: How does pointer addition work in Bedrock2? *)
         pairs = (pairs + pair_size)
       }}))).

  Definition assoc_skip : bedrock_func :=
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
           (* FIXME: How does pointer addition work in Bedrock2? *)
           pairs = (pairs + pair_size)
         }}
       }};
       (* FIXME: negation? *)
       found = ((pairs == pairs_end) ^ constr:(0))))).
End Bedrock2.

Module Gallina.
  Axiom key : Type.
  Axiom value : Type.
  Axiom k_eqb : key -> key -> bool.

  Record pair := { k: key; v: value }.

  Definition assoc (pairs: list pair) (needle: key) : option pair :=
    List.find (fun (p: pair) => k_eqb p.(k) needle) pairs.
End Gallina.
