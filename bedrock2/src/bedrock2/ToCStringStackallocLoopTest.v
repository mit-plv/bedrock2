Require Import bedrock2.Syntax bedrock2.NotationsCustomEntry bedrock2.ToCString.
Import Syntax.Coercions BinInt String List.ListNotations.
Local Open Scope string_scope. Local Open Scope Z_scope. Local Open Scope list_scope.

Definition main : Syntax.func :=
  ("main", ([], ["r"], bedrock_func_body:(
    i = $0; while (i < $(2^20)) {
      stackalloc 2^10 as t;
      store1(t+i>>$10, i);
      i = i+$1
    };
    r = $0
))).

Definition main_cbytes := Eval vm_compute in
  String.list_byte_of_string (ToCString.c_module [main]).
