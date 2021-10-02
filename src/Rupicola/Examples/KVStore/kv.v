From Coq Require Import List ZArith String.

Inductive KVstore_op := GET | PUT.

Local Set Warnings "-ambiguous-paths".

Definition byte := Byte.byte.

Definition Bytes := list byte.
Definition bytes_of_string s : Bytes := String.list_byte_of_string s.
Coercion bytes_of_string : string >-> Bytes.

Axiom size_t : Type.
Axiom nat_of_size_t : size_t -> nat.
Coercion nat_of_size_t : size_t >-> nat.
Axiom size_t_of_nat : nat -> size_t.
Coercion size_t_of_nat : nat >-> size_t.
Axiom size_t_lt : size_t -> size_t -> bool.
Axiom size_t_eqb : size_t -> size_t -> bool.
Definition size_t_neqb x y := negb (size_t_eqb x y).

Axiom uint32_t : Type.
Axiom nat_of_uint32_t : uint32_t -> nat.
Coercion nat_of_uint32_t : uint32_t >-> nat.
Axiom uint32_t_of_nat : nat -> uint32_t.
Coercion uint32_t_of_nat : nat >-> uint32_t.
Axiom uint32_t_of_bytes : Bytes -> uint32_t.
Axiom bytes_of_uint32_t : uint32_t -> Bytes.
Axiom uint32_t_lt : uint32_t -> uint32_t -> bool.
Axiom uint32_t_eqb : uint32_t -> uint32_t -> bool.
Definition uint32_t_neqb x y := negb (uint32_t_eqb x y).

Axiom int32_t : Type.
Axiom Z_of_int32_t : int32_t -> Z.
Coercion Z_of_int32_t : int32_t >-> Z.
Axiom int32_t_of_Z : Z -> int32_t.
Coercion int32_t_of_Z : Z >-> int32_t.
Axiom int32_t_of_bytes : Bytes -> int32_t.
Axiom bytes_of_int32_t : int32_t -> Bytes.
Axiom int32_t_lt : int32_t -> int32_t -> bool.
Axiom int32_t_eqb : int32_t -> int32_t -> bool.
Definition int32_t_neqb x y := negb (int32_t_eqb x y).

Declare Scope sz.
Delimit Scope sz with sz.
Infix "<" := size_t_lt : sz.
Infix "==" := size_t_eqb (at level 70) : sz.
Infix "!=" := size_t_neqb (at level 70) : sz.

Declare Scope ui32.
Delimit Scope ui32 with ui32.
Infix "<" := uint32_t_lt : ui32.
Infix "==" := uint32_t_eqb (at level 70) : ui32.
Infix "!=" := uint32_t_neqb (at level 70) : ui32.

Declare Scope i32.
Delimit Scope i32 with i32.
Infix "<" := int32_t_lt : i32.
Infix "==" := int32_t_eqb (at level 70) : i32.
Infix "!=" := int32_t_neqb (at level 70) : i32.

Definition Key := uint32_t.
Definition Value := uint32_t.

Record KVstore_get_pkt :=
  { kvget_key: Key }.

Record KVstore_put_pkt :=
  { kvput_key: Key;
    kvput_value: Value }.

Record KVstore_pkt :=
  { kvpkt_op: KVstore_op;
    kvpkt_data:
      match kvpkt_op with
      | GET => KVstore_get_pkt
      | PUT => KVstore_put_pkt
      end }.

Record Buffer :=
  { buf_sz: size_t;
    buf_data: Bytes }.

(* buf_data_sz: List.length buf_data <= nat_of_size_t buf_sz *)

Open Scope string_scope.

Import ListNotations.

Fixpoint replace_nth {A} (n: nat) (l: list A) (a: A) :=
  match l, n with
  | [], _ => []
  | _ :: t, 0 => a :: t
  | h :: t, S n => h :: replace_nth n t a
  end.

Fixpoint take {A} (l: list A) (len: nat) (placeholder: A) : list A :=
  match len with
  | 0 => []
  | S len => (List.hd placeholder l) :: take (List.tl l) len placeholder
  end.

Fixpoint slice {A} (l: list A) (off: nat) (len: nat) (placeholder: A) : list A :=
  match off with
  | 0 => take l len placeholder
  | S off => slice (List.tl l) off len placeholder
  end.

Fixpoint blit0 {A} (dst src: list A) : list A :=
  match src with
  | [] => dst
  | hd :: src => hd :: blit0 (List.tl dst) src
  end.

Fixpoint blit {A} (dst: list A) (off: nat) (src: list A) (placeholder: A) : list A :=
  match off with
  | 0 => blit0 dst src
  | S off => (List.hd placeholder dst) :: blit (List.tl dst) off src placeholder
  end.

Definition bytes_write (l: Bytes) (n: size_t) (b: byte) :=
  replace_nth n l b.

Definition bytes_read (l: Bytes) (n: size_t) :=
  nth n l Byte.x00.             (* FIXME inhabited typeclass *)

Definition bytes_borrow (l: Bytes) (off: size_t) (len: size_t) : Bytes :=
  slice l off len Byte.x00.

Definition bytes_unborrow (l: Bytes) (off: size_t) (bs: Bytes) : Bytes :=
  blit l off bs Byte.x00.

Definition bytes_read_uint32 (bs: Bytes) (off: size_t) :=
  uint32_t_of_bytes (slice bs off 4 Byte.x00).

Definition bytes_write_uint32 (bs: Bytes) (off: size_t) (u: uint32_t) :=
  blit bs off (bytes_of_uint32_t u) Byte.x00.

Record box {A: Type} :=
  { box_val: A }.
Arguments box A : clear implicits.

Definition array_borrow_nth {A} (l: list A) (n: size_t) (placeholder: A) : A :=
  nth n l placeholder.

Definition array_unborrow_nth {A} (l: list A) (n: size_t) (a: A) :=
  replace_nth n l a.

Definition strlen s : size_t :=
  String.length s.

(* FIXME: should be a uniform annotation “borrow” coupled with a data access *)
Definition buf_borrow_data (b: Buffer) :=
  b.(buf_data).

Definition buf_unborrow_data (b: Buffer) (bs: Bytes) :=
  {| buf_sz := b.(buf_sz); buf_data := bs |}.

Require Import Arith PeanoNat.

Require Import Coq.Program.Wf.
Require Import Psatz.

Program Fixpoint ranged_for_nat {A}
        (from to step: nat)
        (body: forall (idx: size_t) (acc: A), (bool * A))
        (a0: A) {measure (to - from)} :=
  if le_gt_dec to from then a0
  else let (continue, a0) := body from a0 in
       if continue then
         ranged_for_nat (from + S (pred step)) to step body a0
       else a0.
Next Obligation.
  lia.
Defined.

Definition ranged_for {A}
           (from to step: size_t)
           (body: forall (idx: size_t) (acc: A), (bool * A))
           (a0: A) :=
  ranged_for_nat from to step body a0.

Definition ranged_for_c {A}
           (from to step: size_t)
           (body: forall (idx: size_t) (acc: A), A)
           (a0: A) :=
  ranged_for_nat from to step (fun idx acc => (true, body idx acc)) a0.

Definition memcpy
           (dst: Bytes) (dst_start: size_t)
           (src: Bytes) (src_start: size_t)
           (len: size_t) :=
  let dst := ranged_for_c 0 len 1 (fun idx dst =>
                                    let src_off := src_start + idx in
                                    let dst_off := dst_start + idx in
                                    let b := bytes_read src src_off in
                                    bytes_write dst dst_off b)
                       dst in
  dst.

From Coq Require Import Bool.

Definition byte_cmp (b1 b2: byte) : int32_t :=
  let n1 := Byte.to_N b1 in
  let n2 := Byte.to_N b2 in
  match N.compare n1 n2 with
  | Eq => 0
  | Lt => -1
  | Gt => 1
  end%Z.

Definition memcmp (* FIXME: do short-circuiting version *)
           (dst: Bytes) (dst_start: size_t)
           (src: Bytes) (src_start: size_t)
           (len: size_t) : int32_t :=
  let cmp := ranged_for 0 len 1 (fun idx _ =>
                                  let src_off := src_start + idx in
                                  let dst_off := dst_start + idx in
                                  let src_b := bytes_read src src_off in
                                  let dst_b := bytes_read dst dst_off in
                                  let cmp := byte_cmp src_b dst_b in
                                  let continue := (cmp != 0)%Z%i32 in
                                  (continue, cmp))
                       0%Z in
  cmp.

Definition buf_memcpy
           (dst: Buffer) (dst_start: size_t)
           (src: Bytes) (src_start: size_t)
           (len: size_t) :=
  let dst_data := buf_borrow_data dst in
  let dst_data := memcpy dst_data dst_start src src_start len in
  let buf := buf_unborrow_data dst dst_data in
  buf.

Definition buf_write (dst: Buffer) (off: size_t) (c: byte) :=
  let data := buf_borrow_data dst in
  let data := bytes_write data off c in
  let buf := buf_unborrow_data dst data in
  buf.

Definition buf_set_sz (buf: Buffer) (sz: size_t) :=
  {| buf_data := buf.(buf_data); buf_sz := sz |}.

Definition writeout (output: Buffer) (header: string)
           (data: Bytes) (data_len: size_t) : Buffer :=
  let output_len := output.(buf_sz) in
  if (data_len < output_len)%sz then
    let header_len := strlen header in
    let output := buf_memcpy output 0 header 0 header_len in
    let output := buf_memcpy output header_len data 0 data_len in
    let output := buf_set_sz output (output_len + 1) in
    let output := buf_write output output_len Byte.x0a in
    output
  else output.

Definition OK := "OK ".
Definition ERR := "ERR ".
Definition INPUT_TOO_SHORT := "input too short".
Definition UNRECOGNIZED_OPERATION := "unrecognized operation".
Definition NOT_FOUND := "not found".
Definition STORE_FULL := "store full".

Definition err (buf: Buffer) (s: string) : Buffer :=
  let buf := writeout buf ERR s (strlen s) in
  buf.

Fixpoint list_const {A} (len: nat) (a0: A) : list A :=
  match len with
  | 0 => []
  | S len => a0 :: list_const len a0
  end.

Definition alloca (sz: size_t) : Bytes :=
  list_const sz Byte.x00.

Definition ok (buf: Buffer) (v: Value) : Buffer :=
  let bytes := alloca 4 in
  let bytes := bytes_write_uint32 bytes 0 v in
  let buf := writeout buf ERR bytes 4 in
  buf.

Record KV :=
  { kv_key: Key;
    kv_value: Value }.

Definition kv_set_key (kv: KV) (k: Key) :=
  {| kv_key := k; kv_value := kv.(kv_value) |}.
Definition kv_set_value (kv: KV) (v: Value) :=
  {| kv_key := kv.(kv_key); kv_value := v |}.

Record KVstore :=
  { kvs_sz: size_t;
    kvs_capacity: size_t;
    kvs_data: list KV }.

(* FIXME make an inhabited typeclass to avoid having to specify these placeholders *)
Definition kv_placeholder :=
  {| kv_key := 0; kv_value := 0 |}.

(* FIXME: should be a uniform annotation “borrow” coupled with a data access *)
Definition kvs_borrow_data (kvs: KVstore) :=
  kvs.(kvs_data).

(* FIXME borrow/unborrow could be handled uniformly as lenses *)
Definition kvs_unborrow_data (kvs: KVstore) (data: list KV) :=
  {| kvs_sz := kvs.(kvs_sz);
     kvs_capacity := kvs.(kvs_capacity);
     kvs_data := data |}.

Definition kvs_set_sz (kvs: KVstore) (sz: size_t) :=
  {| kvs_sz := sz;
     kvs_capacity := kvs.(kvs_capacity);
     kvs_data := kvs.(kvs_data) |}.

Definition kv_step (state: KVstore) (input: Buffer) (output: Buffer) : KVstore * Buffer :=
  let input_sz := input.(buf_sz) in
  if (input_sz < 3)%sz then
    let output := err output INPUT_TOO_SHORT in
    (state, output)
  else
    let input_data := buf_borrow_data input in
    let op := bytes_borrow input_data 0 3 in
    if (memcmp op 0 "GET" 0 3 == 0%Z)%i32 then
      (if (input_sz < 8)%sz then
         let output := err output INPUT_TOO_SHORT in
         (state, output)
       else
         (* The loop returns an index instead of a value because that makes
            borrowing the value at that index easier; FIXME think of a way to do
            the borrowing as part of the loop *)
         let key0 := bytes_read_uint32 input_data 4 in
         let sz := state.(kvs_sz) in
         let kvs_data := kvs_borrow_data state in
         let found_idx :=
             ranged_for 0 sz 1
                        (fun idx found_idx =>
                           let kv := array_borrow_nth kvs_data idx kv_placeholder in
                           let key := kv.(kv_key) in
                           let kvs_data := array_unborrow_nth kvs_data found_idx kv in
                           let found_idx := if (key == key0)%ui32 then idx else found_idx in
                           let continue := (found_idx == sz)%sz in
                           (continue, found_idx))
                        sz in
         (* FIXME How do we handle conditional mutation?
            E.g. how would it look if we did the unborrowing after the if? *)
         if (found_idx < sz)%sz then
           let kv := array_borrow_nth kvs_data found_idx kv_placeholder in
           let value := kv.(kv_value) in
           let output := ok output value in
           let kvs_data := array_unborrow_nth kvs_data found_idx kv in
           let state := kvs_unborrow_data state kvs_data in
           (state, output)
         else
           let output := err output NOT_FOUND in
           let state := kvs_unborrow_data state kvs_data in
           (state, output))
    else if (memcmp op 0 "PUT" 0 3 == 0%Z)%i32 then
           (if (input_sz < 12)%sz then
              let output := err output INPUT_TOO_SHORT in
              (state, output)
            else
              let sz := state.(kvs_sz) in
              let capacity := state.(kvs_capacity) in
              if (sz < capacity)%sz then
                let kvs_data := kvs_borrow_data state in
                let key := bytes_read_uint32 input_data 4 in
                let value := bytes_read_uint32 input_data 8 in
                let kv := array_borrow_nth kvs_data sz kv_placeholder in
                let kv := kv_set_key kv key in
                let kv := kv_set_value kv value in
                let kvs_data := array_unborrow_nth kvs_data sz kv in
                let sz := sz + 1 in
                let state := kvs_set_sz state sz in
                let state := kvs_unborrow_data state kvs_data in
                let output := ok output value in
                (state, output)
              else
                let output := err output STORE_FULL in
                (state, output))
         else
           let output := err output UNRECOGNIZED_OPERATION in
           (state, output).
