Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.

Record ethernet_header_t := {
  src_mac: list Z;       (*  6 *)
  dst_mac: list Z;       (* 12 *)
  ethertype: Z;          (* 14 *)
}.

Record arp_packet_t := {
  arp_htype: Z;          (*  2  hardware type *)
  arp_ptype: Z;          (*  4  protocol type *)
  arp_hlen: Z;           (*  5  hardware address length (6 for MAC addresses) *)
  arp_plen: Z;           (*  6  protocol address length (4 for IPv4 addresses) *)
  arp_oper: Z;           (*  8  operation *)
  arp_sha: list Z;       (* 14  sender hardware address *)
  arp_spa: list Z;       (* 18  sender protocol address *)
  arp_tha: list Z;       (* 24  target hardware address *)
  arp_tpa: list Z;       (* 28  target protocol address *)
}.

Record ip_header_t := {
  ip_v_and_ihl: Z;       (*  1 *)
  ip_traffic_class: Z;   (*  2 *)
  ip_length: Z;          (*  4 *)
  ip_frag_id: Z;         (*  6 *)
  ip_frag_ofs: Z;        (*  8 *)
  ip_ttl: Z;             (*  9 *)
  ip_proto: Z;           (* 10 *)
  ip_chksum: Z;          (* 12 *)
  ip_src: list Z;        (* 16 *)
  ip_dst: list Z;        (* 20 *)
}.

Record udp_header_t := {
  src_port: Z;           (*  2 *)
  dst_port: Z;           (*  4 *)
  udp_length: Z;         (*  6 *)
  udp_checksum: Z;       (*  8 *)
}.

Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import bedrock2.SepLib.
Require Import bedrock2.to_from_anybytes.
Require Import bedrock2.RecordPredicates.
Require Import coqutil.Tactics.fwd.

Section BigEndian.
  Local Open Scope Z_scope.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {word_ok: word.ok word}
          {mem: map.map word Byte.byte} {mem_ok: map.ok mem}.

  Definition byte_list_pred_at(P: list Byte.byte -> Prop)(addr: word)(m: mem): Prop :=
    exists bs, map.of_disjoint_list_zip (Memory.ftprint addr (Z.of_nat (length bs))) bs
               = Some m /\ P bs.
    (* Note: this alternative definition is bad because it allows bs that are longer
       than 2^width and the map.of_list_word_at just silently overrides the elements at
       indices >=2^width with elements at indices <2^width:
    exists bs, m = map.of_list_word_at addr bs /\ P bs. *)

  Definition be_uint_bytes(nbits val: Z)(bs: list Byte.byte): Prop :=
    Z.of_nat (List.length bs) * 8 = nbits /\ LittleEndianList.le_combine (List.rev bs) = val.

  Definition be_uint(nbits val: Z): word -> mem -> Prop :=
    byte_list_pred_at (be_uint_bytes nbits val).

  Lemma purify_be_uint nbits v a: PurifySep.purify (be_uint nbits v a) (0 <= v < 2 ^ nbits).
  Proof.
    unfold PurifySep.purify, be_uint, byte_list_pred_at, be_uint_bytes.
    intros. destruct H as (bs & ? & ? & ?).
    subst. rewrite Z.mul_comm.
    rewrite <- List.rev_length. apply LittleEndianList.le_combine_bound.
  Qed.

  Lemma be_uint_contiguous: forall (nbits v: Z),
      contiguous (be_uint nbits v) (nbits_to_nbytes nbits).
  Proof.
    unfold contiguous, Lift1Prop.impl1. intros nbits v addr m H. eapply anybytes_from_alt.
    { apply nbits_to_nbytes_nonneg. }
    unfold be_uint, byte_list_pred_at, be_uint_bytes in H. fwd.
    unfold nbits_to_nbytes.
    replace ((Z.max 0 (Z.of_nat (length bs) * 8) + 7) / 8) with (Z.of_nat (length bs))
      by (Z.div_mod_to_equations; Lia.lia).
    unfold Memory.anybytes. exists bs. assumption.
  Qed.

End BigEndian.

#[export] Hint Resolve be_uint_contiguous : contiguous.
#[export] Hint Resolve purify_uint : purify.

#[export] Hint Extern 1 (PredicateSize (be_uint ?nbits)) =>
  let sz := lazymatch isZcst nbits with
            | true => eval cbv in (nbits_to_nbytes nbits)
            | false => constr:(nbits_to_nbytes nbits)
            end in
  exact sz
: typeclass_instances.

Notation "/* 'BE' */ 'uint64_t'" := (be_uint 64) (in custom c_type_as_predicate).
Notation "/* 'BE' */ 'uint32_t'" := (be_uint 32) (in custom c_type_as_predicate).
Notation "/* 'BE' */ 'uint16_t'" := (be_uint 16) (in custom c_type_as_predicate).
Notation "/* 'BE' */ 'uint8_t'" := (be_uint 8) (in custom c_type_as_predicate).

(* Note: implementation code will still need to use ntohs, ntohl, htons, htonl,
   but the /*BE*/ comment will make separation logic predicates use big-endian order. *)

Section WithMem.
  Local Open Scope Z_scope.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {word_ok: word.ok word}
          {mem: map.map word Byte.byte} {mem_ok: map.ok mem}.

  Definition ethernet_header(r: ethernet_header_t): word -> mem -> Prop := .**/
    typedef struct __attribute__ ((__packed__)) {
      uint8_t src_mac[6];
      uint8_t dst_mac[6];
      /*BE*/uint16_t ethertype;
    } ethernet_header_t;
  /**.

  Goal sizeof ethernet_header = 14. reflexivity. Succeed Qed. Abort.

  Definition arp_packet(r: arp_packet_t): word -> mem -> Prop := .**/
    typedef struct __attribute__ ((__packed__)) {
      /*BE*/uint16_t arp_htype;
      /*BE*/uint16_t arp_ptype;
      uint8_t arp_hlen;
      uint8_t arp_plen;
      /*BE*/uint16_t arp_oper;
      uint8_t arp_sha[6];
      uint8_t arp_spa[4];
      uint8_t arp_tha[6];
      uint8_t arp_tpa[4];
    } arp_packet_t;
  /**.

  Goal sizeof arp_packet = 28. reflexivity. Succeed Qed. Abort.

  Definition ip_header(r: ip_header_t): word -> mem -> Prop := .**/
    typedef struct __attribute__ ((__packed__)) {
      uint8_t ip_v_and_ihl;
      uint8_t ip_traffic_class;
      /*BE*/uint16_t ip_length;
      /*BE*/uint16_t ip_frag_id;
      /*BE*/uint16_t ip_frag_ofs;
      uint8_t ip_ttl;
      uint8_t ip_proto;
      /*BE*/uint16_t ip_chksum;
      uint8_t ip_src[4];
      uint8_t ip_dst[4];
    } ip_header_t;
  /**.

  Goal sizeof ip_header = 20. reflexivity. Succeed Qed. Abort.

  Definition udp_header(r: udp_header_t): word -> mem -> Prop := .**/
    typedef struct __attribute__ ((__packed__)) {
      /*BE*/uint16_t src_port;
      /*BE*/uint16_t dst_port;
      /*BE*/uint16_t udp_length;
      /*BE*/uint16_t udp_checksum;
    } udp_header_t;
  /**.

  Goal sizeof udp_header = 8. reflexivity. Succeed Qed. Abort.
End WithMem.
