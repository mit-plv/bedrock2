(* Rewritten versions of poly1305 and chacha20 that you could compile with Rupicola *)

Require Coq.Init.Byte Coq.Strings.String. Import Init.Byte(byte(..)) String.
Require Import coqutil.Datatypes.List. Import Lists.List List.ListNotations.
Require Import Coq.ZArith.BinInt. Import Zdiv. Local Open Scope Z_scope.
Require Import coqutil.Byte coqutil.Word.LittleEndianList.

(* reference: https://datatracker.ietf.org/doc/html/rfc8439 *)

let r := List.map (as_word_list (firstn 16 k)) (fun x => x `and` 0x0ffffffc) in

l: list byte

H: locals[x] = xp
lw := (as_word_list l)
Hmem: (array Word lw xp * R) mem
==================
{| locals, mem, tr |} b { POST (k lw) }

apply compile_as_word_list

H: local[x] = xp
Hmem: (array Byte l xp * R) mem
Hlen: len xp mod 4 = 0
==================
{| locals, mem, tr |} b { POST (let x := as_word_list l in k x) }

felem_size


Definition poly1305 (p:=2^130-5) (k : list byte) (m : list byte) : list byte :=
  let f16, l16 := split 16 k in
  let scratch := make_buffer felem_size in
  let scratch := buf_append scratch f16 in
  let f16, lone_byte_and_felem_spare_space := split_buffer scratch in
  let f16 := as_word_list f16 in
  let f16 := List.map (fun w =>
                        let w := word.and w 0x0ffffffc in
                        w)
                     f16 in
  let f16 := as_byte_list f16 in
  let scratch := reassemble_buffer f16 lone_byte_and_felem_spare_space in
  let scratch := buffer_push scratch 0 in
  let scratch := buffer_as_array scratch in
  let scratch := as_felem_inplace scratch in (* B2 primitive reads first 17 bytes of longer array *)
  let mchunks := as_small_arrays 16 m in (* FIXME this shouldn't need to be a multiple of the length *)
  let a := stack (felem_init_zero ()) in
  let a := fold_left (fun idx a ck =>
                       let nscratch := make_buffer felem_size in
                       let nscratch := buf_append nscratch ck in (* len = 16 *)
                       let nscratch := buf_push nscratch x01 in (* len = 17 *)
                       let nscratch := as_felem_inplace nscratch in
                       let a := felem.add a nscratch in
                       let a := felem.mul a scratch in
                       a)
                    mchunks a in
  let output := felem_as_bytes a in
  let output := andres_uint128_add output l16 in (* FIXME reassemble inputs *)
  output.

Definition poly1305_uneven_length (p:=2^130-5) (k : list byte) (m : list byte) : list byte :=
  let f16, l16 := split 16 k in
  let scratch := make_buffer felem_size in
  let scratch := buf_append scratch f16 in
  let f16, lone_byte_and_felem_spare_space := split_buffer scratch in
  let f16 := as_word_list f16 in
  let f16 := List.map (fun w =>
                        let w := word.and w 0x0ffffffc in
                        w)
                     f16 in
  let f16 := as_byte_list f16 in
  let scratch := reassemble_buffer f16 lone_byte_and_felem_spare_space in
  let scratch := buffer_push scratch 0 in
  let scratch := buffer_as_array scratch in
  let scratch := as_felem_inplace scratch in (* B2 primitive reads first 17 bytes of longer array *)
  let a := stack (felem_init_zero ()) in
  let nchunks := Nat.div_up m_length 16 in
  let a := List.iter  (fun idx a ck =>
                       let nscratch := make_buffer felem_size in
                       let ck_start := idx * 16 in
                       let ck_end := min (ck_start + 16) m_length in
                       let before, ck, after := slice m ck_start ck_end in
                       let nscratch := buf_append nscratch ck in (* len = 16 *)
                       let m := reassemble before ck after in
                       let nscratch := buf_push nscratch x01 in (* len = 17 *)
                       let nscratch := as_felem_inplace nscratch in
                       let a := felem.add a nscratch in
                       let a := felem.mul a scratch in
                       a)
                    a in
  let output := felem_as_bytes a in
  let output := andres_uint128_add output l16 in (* FIXME reassemble inputs *)
  output.

Definition poly1305 (p:=2^130-5) (k : list byte) (m : list byte) : list byte :=
  let r := Z.land (le_combine (firstn 16 k)) 0x0ffffffc0ffffffc0ffffffc0fffffff in
  let t := fold_left (fun a n => (a+le_combine(n++[x01]))*r mod p) (chunk 16 m) 0 in
  le_split 16 (t + le_combine (skipn 16 k)).

Local Notation "a + b" := (Z.land (a+b) (Z.ones 32)).
Local Notation "a ^ b" := (Z.lxor a b).
Local Notation "a <<< b" := (Z.shiftl a b + Z.shiftr a (32-b))
  (at level 30).

Definition quarter '(a, b, c, d) :=
  let a := a + b in  let d := d ^ a in  let d := d <<< 16 in
  let c := c + d in  let b := b ^ c in  let b := b <<< 12 in
  let a := a + b in  let d := d ^ a in  let d := d <<< 8 in
  let c := c + d in  let b := b ^ c in  let b := b <<< 7 in
  (a, b, c, d).

Definition quarterround x y z t (st : list Z) :=
  let/n stx := ArrayList.get x st 0 in
  let/n sty := ArrayList.get y st 0 in
  let/n stz := ArrayList.get z st 0 in
  let/n stt := ArrayList.get t st 0 in
  let/n stx, sty, stz, stt := quarter (stx, sty, stz, stt) in
  let/n st := ArrayList.put x st stx in
  let/n st := ArrayList.put y st sty in
  let/n st := ArrayList.put z st stz in
  let/n st := ArrayList.put t st stt in
  st.

Definition quarterround x y z t (st : list Z) :=
  let '(a,b,c,d) := quarter (nth x st 0, nth y st 0, nth z st 0, nth t st 0) in
  upd (upd (upd (upd st x a) y b) z c) t d.

init := list_byte_of_string "expand 32-byte k"

Definition chacha20_block (*256bit*)key (*32bit+96bit*)nonce (*512 bits*)st :=
  let st := buffer_push init1 in
  let st := buffer_push init2 in
  let st := buffer_push init3 in
  let st := buffer_push init4 in (* the inits are the chunks of "expand …" *)
  let key := as_word_list key in
  let st := buffer_append st key in
  let key := as_byte_list st key in
  let nonce := as_word_list nonce in
  let st := buffer_append st nonce in
  let key := as_byte_list st nonce in
  let st := buffer_as_array st in
  let ss := make_buffer_word 16 in
  let ss := buf_append st ss in
  let ss := buffer_as_array ss in
  let ss := downto 10 0 (fun ss =>
    let ss := quarterround  0  4  8 12  ss in
    let ss := quarterround  1  5  9 13  ss in
    let ss := quarterround  2  6 10 14  ss in
    let ss := quarterround  3  7 11 15  ss in
    let ss := quarterround  0  5 10 15  ss in
    let ss := quarterround  1  6 11 12  ss in
    let ss := quarterround  2  7  8 13  ss in
    let ss := quarterround  3  4  9 14  ss in
    ss) ss in
  let st := List.iter 16 (fun i st =>
                           let st_i := Array.get st i in
                           let ss_i := Array.get ss i in
                           let st_i := word.add st_i ss_i in
                           let st := Array.put st i st_i in
                           st) st in
  let st := as_list_byte st in
  st.

Definition chacha20_block (*256bit*)key (*32bit+96bit*)nonce :=
  let st := (*512bit*)
    map le_combine (chunk 4 (list_byte_of_string"expand 32-byte k"))
    ++ map le_combine (chunk 4 key)
    ++ map le_combine (chunk 4 nonce) in
  let ss := Nat.iter 10 (fun ss =>
    let ss := quarterround  0  4  8 12  ss in
    let ss := quarterround  1  5  9 13  ss in
    let ss := quarterround  2  6 10 14  ss in
    let ss := quarterround  3  7 11 15  ss in
    let ss := quarterround  0  5 10 15  ss in
    let ss := quarterround  1  6 11 12  ss in
    let ss := quarterround  2  7  8 13  ss in
    let ss := quarterround  3  4  9 14  ss in
    ss) st in
  let st := map (fun '(s, t) => s + t) (combine ss st) in
  flat_map (le_split 4) st.

Definition chacha20_encrypt key start nonce plaintext :=
  let chunks := as_small_arrays 16 plaintex in (* FIXME this shouldn't need to be a multiple of the length *)
  let chunks := List.iter nchunks (fun idx chunks => (* FIXME nchunks *)
    let before, ck, after := partition_array chunks i in
    let counter := word.add start idx in
    let scratch := make_buffer_word 4 in
    let nonce := as_list_byte nonce in
    let scratch := buffer_push scratch counter in
    let scratch := buffer_append scratch nonce in (* FIXME? You can save a scratch buffer by doing the nonce concatenation of chacha20 here instead *)
    let st := make_buffer_word 16 in
    let st := chacha20_block key scratch st in
    let ck := List.iter 16 (fun idx => (* FIXME should this be rewritten as mapi *)
                           let st_i := Array.get st i in
                           let ss_i := Array.get ck i in
                           let ck_i := word.xor st_i ck_i in
                           let ck := Array.put ck i ck_i in
                           ck)
                       ck in
    let chunks := unpartition_array before chunk after in
    chunks) in
  let ciphertext := of_small_arrays chunks in
  ciphertext.

Definition chacha20_encrypt_uneven_length key start nonce plaintext :=
  let plaintext := List.iter (Nat.div_up plaintext_len 16) (fun idx plaintext => (* FIXME nplaintext *)
    let counter := word.add start idx in
    let scratch := make_buffer_word 4 in
    let nonce := as_list_byte nonce in
    let scratch := buffer_push scratch counter in
    let scratch := buffer_append scratch nonce in (* FIXME? You can save a scratch buffer by doing the nonce concatenation of chacha20 here instead *)
    let st := make_buffer_word 16 in
    let st := chacha20_block key scratch st in
    let st := as_list_bytes st in
    let chunk_start := idx * chunk_sz in
    let chunk_end := min (chunk_start + chunk_sz) plaintext_length in
    (* let before, ck, after := slice_out_array plaintext chunk_start chunk_end in *)
    let plaintext := List.iter chunk_start chunk_end
                       (fun idx => (* FIXME should this be rewritten as mapi *)
                           let st_i := Array.get st (i - chunk_start) in
                           let ss_i := Array.get plaintext i in
                           let plaintext_i := byte.xor st_i plaintext_i in
                           let plaintext := Array.put plaintext i plaintext_i in
                           plaintext)
                       plaintext in
    plaintext) in
  plaintext.


Definition chacha20_encrypt key start nonce plaintext :=
  flat_map (fun '(counter, ck) =>
    zip byte.xor (chacha20_block key (le_split 4 (Z.of_nat counter) ++ nonce)) ck)
  (enumerate start (chunk 64 plaintext)).

Definition chacha20poly1305_aead_encrypt aad key iv constant plaintext :=
  let pad16 xs := repeat x00 (Nat.div_up (length xs) 16 * 16 - length xs) in
  let nonce := constant ++ iv in
  let otk := firstn 32 (chacha20_block key (le_split 4 0 ++ nonce)) in
  let ciphertext := chacha20_encrypt key 1 nonce plaintext in
  let mac_data := aad ++ pad16 aad in
  let mac_data := mac_data ++ ciphertext ++ pad16 ciphertext in
  let mac_data := mac_data ++ le_split 8 (Z.of_nat (length aad)) in
  let mac_data := mac_data ++ le_split 8 (Z.of_nat (length ciphertext)) in
  let tag := poly1305 otk mac_data in
  (ciphertext, tag).
