(*! IP Checksum, from https://www.rfc-editor.org/rfc/rfc1071 !*)
Require Import ZArith.
From coqutil Require Import
     Datatypes.List
     Byte
     Word.LittleEndianList.

Open Scope Z_scope.

Definition onec_add16 (z1 z2: Z) :=
  let sum := z1 + z2 in
  (Z.land sum 0xffff + (Z.shiftr sum 16)).

Definition ip_checksum (bs: list byte) :=
  let chk := List.fold_left onec_add16 (List.map le_combine (chunk 2 bs)) 0xffff in
  Z.land (Z.lnot chk) 0xffff.
