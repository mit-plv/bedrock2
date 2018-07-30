Require Import bedrock2.Syntax bedrock2.Structs bedrock2.NotationsInConstr.

Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Section StructAccess.
  Context {p : Syntax.parameters} {bp : BasicALU.operations}.

  Definition item : type := inr (Struct (
    ("a", inl 1)::
    ("b", inl 2)::
    nil)).

  Context (dst src : expr).

  Example example_expr : expr :=
    &field "b" of item at (dst as item *> "b" as item *> "a").

  Example example_cmd : cmd :=
    field "b" of item at (dst as item *> "b" as item *> "a") = *(uint8_t*) src;
   /*skip*/.
End StructAccess.