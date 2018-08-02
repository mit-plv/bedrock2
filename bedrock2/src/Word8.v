Require Import bedrock2.Byte.
Require Import bbv.Word.

Definition of_byte (b : byte) : word 8 :=
  let '(b0, b1, b2, b3, b4, b5, b6, b7) := to_bits b in
  WS b7 (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO))))))).
(*
Definition to_byte (w : word 8) : byte :=
  let 'WS b7 (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO))))))) := w in
  of_bits (b0, b1, b2, b3, b4, b5, b6, b7).
(* Error: Non exhaustive pattern-matching: no clause found for pattern WS _ WO *)
*)