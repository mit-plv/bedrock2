Require Import Coq.ZArith.ZArith.
Require Import bedrock2.Byte.
Require Import bbv.Word.

Definition of_byte (b : byte) : word 8 :=
  let '(b0, b1, b2, b3, b4, b5, b6, b7) := to_bits b in
  WS b7 (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO))))))).

Definition Z_to_byte (x : Z) : byte :=
  let b0 := Z.testbit x 0 in
  let b1 := Z.testbit x 1 in
  let b2 := Z.testbit x 2 in
  let b3 := Z.testbit x 3 in
  let b4 := Z.testbit x 4 in
  let b5 := Z.testbit x 5 in
  let b6 := Z.testbit x 6 in
  let b7 := Z.testbit x 7 in
  of_bits (b0, b1, b2, b3, b4, b5, b6, b7).

(*
Definition to_byte (w : word 8) : byte :=
  let 'WS b7 (WS b6 (WS b5 (WS b4 (WS b3 (WS b2 (WS b1 (WS b0 WO))))))) := w in
  of_bits (b0, b1, b2, b3, b4, b5, b6, b7).
(* Error: Non exhaustive pattern-matching: no clause found for pattern WS _ WO *)
*)