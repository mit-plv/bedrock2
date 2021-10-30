(* Rewritten versions of poly1305 and chacha20 that you can compile with Rupicola *)
Require Import Rupicola.Examples.ChaCha20Poly1305.Spec.

Definition poly1305 (p:=2^130-5) (k : list byte) (m : list byte) : list byte :=
  let/n f16, l16 := split 16 k in
  let/n scratch := make_buffer felem_size in
  let/n scratch := buf_append scratch f16 in
  let/n f16, lone_byte_and_felem_spare_space := split_buffer scratch in
  let/n f16 := as_word_list f16 in
  let/n f16 := List.map (fun w =>
                        let/n w := word.and w 0x0ffffffc in
                        w)
                     f16 in
  let/n f16 := as_byte_list f16 in
  let/n scratch := reassemble_buffer f16 lone_byte_and_felem_spare_space in
  let/n scratch := buffer_push scratch 0 in
  let/n scratch := buffer_as_array scratch in
  let/n scratch := as_felem_inplace scratch in (* B2 primitive reads first 17 bytes of longer array *)
  let/n a := stack (felem_init_zero ()) in
  let/n nchunks := Nat.div_up m_length 16 in
  let/n a := List.iter  (fun idx a ck =>
                       let/n nscratch := make_buffer felem_size in
                       let/n ck_start := idx * 16 in
                       let/n ck_end := min (ck_start + 16) m_length in
                       let/n before, ck, after := slice m ck_start ck_end in
                       let/n nscratch := buf_append nscratch ck in (* len = 16 *)
                       let/n m := reassemble before ck after in
                       let/n nscratch := buf_push nscratch x01 in (* len = 17 *)
                       let/n nscratch := as_felem_inplace nscratch in
                       let/n a := felem.add a nscratch in
                       let/n a := felem.mul a scratch in
                       a)
                    a in
  let/n output := felem_as_bytes a in
  let/n output := andres_uint128_add output l16 in (* FIXME reassemble inputs *)
  output.
