Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.

Local Coercion tuple.to_list: tuple >-> list.

(* n-bit big-endian value, implicitly enforcing bounds on v *)
Definition be(n: nat)(v: Z)(bs: list byte): Prop :=
  List.length bs = n /\ le_combine (List.rev bs) = v.

Definition be_alt(n: nat)(v: Z)(bs: tuple byte n): Prop :=
  le_combine (List.rev bs) = v.

Record ethernet_header_t := {
  src_mac: tuple byte 6;
  dst_mac: tuple byte 6;
  ethertype: Z;
}.

Definition ethernet_flip_src_dst: ethernet_header_t -> ethernet_header_t :=
  fun '(Build_ethernet_header_t src dst tp) =>
       (Build_ethernet_header_t dst src tp).

Definition ethernet_header(h: ethernet_header_t)(bs: list byte): Prop :=
  exists tp, bs = src_mac h ++ dst_mac h ++ tp /\ be 2 (ethertype h) tp.

Record ip_header_t := {
  ih_const: tuple byte 2;
  ip_length: Z;
  ip_idff: tuple byte 2;
  ip_proto: byte;
  ip_chksum: tuple byte 2;
  ip_src: tuple byte 4;
  ip_dst: tuple byte 4;
}.

Definition set_ip_checksum chksum : ip_header_t -> ip_header_t :=
  fun '(Build_ip_header_t c l i p _ s d) =>
       (Build_ip_header_t c l i p (tuple.of_list (le_split 2 chksum)) s d).

Definition clear_ip_checksum: ip_header_t -> ip_header_t := set_ip_checksum 0.

Definition encode_ip_header(h: ip_header_t): list byte :=
  ih_const h ++ le_split 2 (ip_length h) ++ ip_idff h ++ [ip_proto h] ++ ip_chksum h ++
  ip_src h ++ ip_dst h.

Definition ip_header(h: ip_header_t)(bs: list byte): Prop :=
  bs = encode_ip_header h /\ 0 <= ip_length h < 2^16.

Record udp_header_t := {
  src_port: tuple byte 2;
  dst_port: tuple byte 2;
  udp_length: Z;
  udp_checksum: Z;
}.

Definition udp_header(h: udp_header_t)(bs: list byte): Prop :=
  exists len chk, bs = src_port h ++ dst_port h ++ len ++ chk /\
                  be 2 (udp_length h) len /\
                  be 2 (udp_checksum h) chk.

Require bedrock2.TracePredicate.

(* TODO move to TracePredicate, which already does stateful stuff *)
Section StatefulTracePredicate.
  Context {state OP: Type}.
  Local Notation Predicate := (state -> list OP -> state -> Prop).

  Definition stateful_pure(p: list OP -> Prop): Predicate :=
    fun s t s' => s = s' /\ p t.

  (* TODO this naming scheme is a bit ridiiiiculous :P *)
  Definition stateful_puure(p: Prop): Predicate :=
    stateful_pure (TracePredicate.constraint p).

  Definition stateful_seq(P1 P2: Predicate): Predicate :=
    fun s t s'' => exists s' t1 t2,
        t = List.app t2 t1 /\ (* new events are added at head of list *)
        P1 s t1 s' /\ P2 s' t2 s''.

  Definition stateful_choice(P1 P2: Predicate): Predicate :=
    fun s t s' => P1 s t s' \/ P2 s t s'.

  Definition stateful_ex[T: Type](P: T -> Predicate): Predicate :=
    fun s t s' => exists x, P x s t s'.

  Definition stateful_read(P: state -> Predicate): Predicate :=
    fun s t s' => P s s t s'.

  Definition stateful_update(R: state -> state -> Prop): Predicate :=
    fun s t s' => t = nil /\ R s s'.

  Definition stateful_nop: Predicate := stateful_update eq.
End StatefulTracePredicate.

Module StatefulTracePredicateNotations.
  (*Notation "P ^*" := (kleene P) (at level 50).*)
  (*Notation "P ^+" := (concat P (kleene P)) (at level 50).*)
  Infix "+++" := stateful_seq (at level 60).
  Infix "|||" := stateful_choice (at level 70).
  Notation "'EX' x .. y , p" := (stateful_ex (fun x => .. (stateful_ex (fun y => p)) ..))
    (at level 200, x binder, right associativity,
     format "'[' 'EX'  '/  ' x  ..  y ,  '/  ' p ']'").
End StatefulTracePredicateNotations.

Require Import coqutil.Word.Interface.

Module Examples. Section __.
  Context (ip_checksum_spec: list byte -> Z).

  Definition ip_checksum_ok(h: ip_header_t): Prop :=
    ip_checksum_spec (encode_ip_header (clear_ip_checksum h)) = le_combine (ip_chksum h).

  Record garagedoor_packet_t := {
    garagedoor_ethernet_header :> ethernet_header_t;
    garagedoor_ip_header :> ip_header_t;
    garagedoor_udp_header :> udp_header_t;
    garagedoor_header: tuple byte 2;
    garagedoor_payload: list byte;
  }.

  Definition garagedoor_packet(p: garagedoor_packet_t)(bs: list byte): Prop :=
    exists eth ip udp,
      bs = eth ++ ip ++ udp ++ garagedoor_header p ++ garagedoor_payload p /\
      ethernet_header p eth /\
      ip_header p ip /\
      ip_checksum_ok p /\
      udp_header p udp.

  Record state := {
    prng_state: list byte;
    x25519_ephemeral_secret: list byte
  }.

  Import StatefulTracePredicateNotations.
  Import Coq.Strings.String. Local Open Scope string_scope. Local Open Scope list_scope.
  Local Open Scope bool_scope.

  Context {word: word.word 32}.

  Context (GPIO_DATA_ADDR: word).

  Definition OP: Type := String.string * word * word.

  Context (chacha20_block: list byte -> list byte -> list byte).

  Context (lan9250_recv: list byte -> list OP -> Prop).
  Context (lan9250_send: list byte -> list OP -> Prop).

  Context (poll_timeout: list OP -> Prop).
  Context (poll_no_packet: list OP -> Prop).
  Context (poll_invalid_packet: list OP -> Prop).

  Context (CurvePoint: Type).
  Context (x25519_spec: list byte -> CurvePoint -> list byte).
  Context (Curve25519_M_B: CurvePoint).
  Context (garageowner_P: CurvePoint) (garageowner: list byte).

  (* TODO separate the different protocol layers & concerns more *)

  (* TODO instead of just copying fields from request, we should validate them,
     and specify in clear which values we send back *)
  Definition make_challenge(sk: list byte)(req: garagedoor_packet_t): garagedoor_packet_t :=
    let ih0 := {|
      ih_const := ih_const req;
      ip_length := 62;
      ip_idff := ip_idff req;
      ip_proto := ip_proto req;
      ip_chksum := tuple.of_list (le_split 2 0);
      ip_src := ip_dst req;
      ip_dst := ip_src req;
    |} in {|
      garagedoor_ethernet_header := ethernet_flip_src_dst (garagedoor_ethernet_header req);
      garagedoor_ip_header := set_ip_checksum (ip_checksum_spec (encode_ip_header ih0)) ih0;
      garagedoor_udp_header := {|
        src_port := dst_port req;
        dst_port := src_port req;
        udp_length := 42;
        udp_checksum := 0;
      |};
      garagedoor_header := garagedoor_header req;
      garagedoor_payload := x25519_spec sk Curve25519_M_B;
    |}.

  Definition handle_request_for_challenge: state -> list OP -> state -> Prop :=
    EX incoming, stateful_pure (lan9250_recv incoming) +++
    EX req, stateful_puure (garagedoor_packet req incoming) +++
    stateful_read (fun '(Build_state seed sk) => EX outgoing,
      stateful_puure (garagedoor_packet (make_challenge sk req) outgoing) +++
      stateful_pure (lan9250_send outgoing)).

  Definition send_door_bits(b0 b1: bool): list OP -> Prop :=
    let set0 := word.of_Z (Z.b2z b0) in
    let set1 := word.of_Z (Z.b2z b1) in
    TracePredicate.existsl (fun doorstate: word =>
      let action := word.or
        (word.and doorstate (word.of_Z (Z.clearbit (Z.clearbit (2^32-1) 11) 12)))
        (word.slu (word.or (word.slu set1 (word.of_Z 1)) set0) (word.of_Z 11)) in
      TracePredicate.concat
        (TracePredicate.one ("ld", GPIO_DATA_ADDR, doorstate))
        (TracePredicate.one ("st", GPIO_DATA_ADDR, action))).

  Definition refresh_ephemeral_secret: state -> list OP -> state -> Prop :=
    stateful_update (fun '(Build_state seed1 sk1) '(Build_state seed2 sk2) =>
      seed2 ++ sk2 = chacha20_block seed1 (le_split 4 0 ++ List.firstn 12 garageowner)).

  Definition handle_door_request: state -> list OP -> state -> Prop :=
    EX incoming, stateful_pure (lan9250_recv incoming) +++
    EX req, stateful_puure (garagedoor_packet req incoming) +++
    stateful_read (fun '(Build_state seed sk) =>
      let m := List.firstn 16 (garagedoor_payload req) in
      let v := x25519_spec sk garageowner_P in
      let set0 := List.list_eqb Byte.eqb m (firstn 16 v) in
      let set1 := List.list_eqb Byte.eqb m (skipn 16 v) in
      stateful_pure (send_door_bits set0 set1) +++
      if set0 || set1 then refresh_ephemeral_secret else stateful_nop).

  Definition protocol_step: state -> list OP -> state -> Prop :=
    stateful_pure poll_timeout |||
    stateful_pure poll_no_packet |||
    stateful_pure poll_invalid_packet |||
    handle_request_for_challenge |||
    handle_door_request.

End __. End Examples.
