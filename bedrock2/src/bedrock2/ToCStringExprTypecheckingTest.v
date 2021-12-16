Require Import Ltac2.Ltac2.
Require Import Coq.ZArith.BinInt Coq.Strings.String.
Require Import bedrock2.Syntax bedrock2.ToCString. Import Syntax.Coercions.
Local Open Scope Z_scope. Local Open Scope string_scope.

Definition bopnames : list bopname := ltac2:(
  let rec gen i := Control.plus
    (fun _ => apply @cons > [constructor i | gen (Int.add 1 i) ])
    (fun _ => apply @nil) in
  gen 1).
 
Definition test := Eval vm_compute in list_byte_of_string (
  prelude ++ LF ++
  "int main() {" ++ LF ++
  concat LF (List.map (fun b =>
  "  _Generic(" ++ c_expr (expr.op b 42 7) ++ ", uintptr_t: 0);") bopnames) ++ LF ++
  "}" ++ LF).
