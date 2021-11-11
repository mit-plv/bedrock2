Require Import bedrock2.ToCString bedrock2.Bytedump String.
Local Open Scope string_scope. Local Open Scope bytedump_scope.

Require Rupicola.Examples.Utf8.Utf8.
Goal True.
  let bs := eval vm_compute in
    (byte_list_of_string (c_module
      (cons ("dummy_main", (nil, nil, Syntax.cmd.skip))
      (cons Utf8.utf8_decode_impl
      nil)))) in
  idtac bs.
Abort.
