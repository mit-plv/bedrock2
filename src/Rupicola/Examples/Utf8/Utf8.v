(*! Branchless utf-8 decoder, from https://github.com/skeeto/branchless-utf8 !*)
Require Import
        Rupicola.Lib.Api
        Rupicola.Lib.Arrays
        Rupicola.Lib.InlineTables
        Rupicola.Lib.WordNotations
        Rupicola.Examples.Utf8.Utils.

Definition masks :=
  Eval cbv in List.map byte.of_Z [0x00; 0x7f; 0x1f; 0x0f; 0x07].
Definition mins :=
  Eval cbv in List.map byte.of_Z [4194304; 0; 128; 2048; 65536].
Definition shiftc :=
  Eval cbv in List.map byte.of_Z [0; 18; 12; 6; 0].
Definition shifte :=
  Eval cbv in List.map byte.of_Z [0; 6; 4; 2; 0].

Notation f x := (@F 5 x).
Definition lengths : list (Fin.t 5) :=
  Eval cbv in
    [f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1; f 1;
     f 0; f 0; f 0; f 0; f 0; f 0; f 0; f 0; f 2; f 2; f 2; f 2; f 3; f 3; f 4; f 0].

Definition utf8_decode (ptr: word) (bs: list byte) : word * word * word :=
  let/n b0 := ListArray.get bs 0 in
  let/n len := InlineTable.get lengths (b0 >>w 3) in

  let/n ptr := ptr +w len +w (len ==w 0) in

  let/n mask := InlineTable.get masks len in
  let/n c := (b0 &w mask) <<w 18 in
  let/n b1 := ListArray.get bs 1 in
  let/n c := c |w (b1 &w 0x3f) <<w 12 in
  let/n b2 := ListArray.get bs 2 in
  let/n c := c |w (b2 &w 0x3f) <<w 6 in
  let/n b3 := ListArray.get bs 3 in
  let/n c := c |w (b3 &w 0x3f) <<w 0 in

  let/n shiftc := InlineTable.get shiftc len in
  let/n c := c >>w shiftc in

  let/n min := InlineTable.get mins len in
  let/n e := (c <w min) <<w 6 in
  let/n e := e |w ((c >>w 11) ==w 0x1b) <<w 7 in
  let/n e := e |w (0x10FFFF <w c) <<w 8 in
  let/n e := e |w (b1 &w 0xc0) >>w 2 in
  let/n e := e |w (b2 &w 0xc0) >>w 4 in
  let/n e := e |w (b3       ) >>w 6 in
  let/n e := e ^w 0x2a in

  let/n shifte := InlineTable.get shifte len in
  let/n e := e >>w shifte in

  (c, e, ptr).

Instance spec_of_utf8_decode : spec_of "utf8_decode" :=
  fnspec! "utf8_decode" data_ptr / (data : list byte) R ~> c e ptr,
    { requires tr mem :=
        Z.of_nat (length data) >= 4 /\
        (listarray_value AccessByte data_ptr data * R)%sep mem;
      ensures tr' mem' :=
        tr' = tr /\
        (c, e, ptr) = utf8_decode data_ptr data /\
        (listarray_value AccessByte data_ptr data * R)%sep mem' }.

Import UnsizedListArrayCompiler.

Hint Rewrite @word_of_byte_of_fin : compiler_side_conditions.
#[local] Hint Resolve Fin_to_nat_lt : compiler_side_conditions.
#[local] Hint Extern 1 => simple apply word_of_byte_sru_lt : compiler_side_conditions.
#[local] Hint Extern 10 => cbn; lia : compiler_side_conditions.

Derive utf8_decode_br2fn SuchThat
       (defn! "utf8_decode" ("data") ~> "c", "e", "ptr"
         { utf8_decode_br2fn },
         implements utf8_decode)
       As utf8_decode_br2fn_ok.
Proof.
  Time compile.
Time Qed.

Definition utf8_decode_cbytes := Eval vm_compute in
  list_byte_of_string (ToCString.c_module
    [("dummy_main_to_make_impl_get_inlined", ([], [], cmd.skip));
     utf8_decode_br2fn]).
