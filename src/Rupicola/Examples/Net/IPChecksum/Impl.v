Require Import
        Rupicola.Lib.Api
        Rupicola.Lib.Arrays
        Rupicola.Lib.Loops
        Rupicola.Lib.WordNotations.
Require Import
        bedrock2.BasicC32Semantics.

Coercion co_word_of_Z := word.of_Z (word := word).
Coercion co_word_of_byte (b: byte) : word := word_of_byte b.

Definition ip_checksum_upd (chk16: word) (b0 b1: byte) :=
  let/n w16 := b0 |w (b1 <<w 8) in
  let/n chk17 := chk16 +w w16 in
  let/n chk16 := (chk17 &w 0xffff) +w (chk17 >>w 16) in
  chk16.

(* TODO: make a variant that accumulate carries until the end *)
Definition ip_checksum_impl (bs: list byte) : word :=
  let/n chk16 := 0xffff in

  (* Main loop *)
  let/n chk16 :=
    ranged_for_all_nd
      0 (Z.of_nat (List.length bs) / 2)
      (fun chk16 idx =>
         let/n b0 := ListArray.get bs (2 * idx) in
         let/n b1 := ListArray.get bs (2 * idx + 1) in
         let/n chk16 := ip_checksum_upd chk16 b0 b1 in
         chk16) chk16 in

  (* Final iteration *)
  let/n chk16 := if Z.odd (Z.of_nat (List.length bs)) then
                  let/n b0 := ListArray.get bs (Z.of_nat (List.length bs) - 1) in
                  let/n chk16 := ip_checksum_upd chk16 b0 (Byte.x00) in
                  chk16
                else chk16 in

  let/n chk16 := (~w chk16) &w 0xffff in
  chk16.
