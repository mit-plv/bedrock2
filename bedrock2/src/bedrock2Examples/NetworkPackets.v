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
  ip_version_and_len: Z; (*  1 *)
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
Require Import bedrock2.RecordPredicates.

(* Note: these predicates all lay out the values in little-endian order, but network
   packets usage big-endian order, so one still has to use ntohs, ntohl, htons, htonl *)

Section WithMem.
  Local Open Scope Z_scope.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {word_ok: word.ok word}
          {mem: map.map word Byte.byte} {mem_ok: map.ok mem}.

  Definition ethernet_header(r: ethernet_header_t): word -> mem -> Prop := .**/
    typedef struct __attribute__ ((__packed__)) {
      uint8_t src_mac[6];
      uint8_t dst_mac[6];
      uint16_t ethertype;
    } ethernet_header_t;
  /**.

  Goal sizeof ethernet_header = 14. reflexivity. Succeed Qed. Abort.

  Definition arp_packet(r: arp_packet_t): word -> mem -> Prop := .**/
    typedef struct __attribute__ ((__packed__)) {
      uint16_t arp_htype;
      uint16_t arp_ptype;
      uint8_t arp_hlen;
      uint8_t arp_plen;
      uint16_t arp_oper;
      uint8_t arp_sha[6];
      uint8_t arp_spa[4];
      uint8_t arp_tha[6];
      uint8_t arp_tpa[4];
    } arp_packet_t;
  /**.

  Goal sizeof arp_packet = 28. reflexivity. Succeed Qed. Abort.

  Definition ip_header(r: ip_header_t): word -> mem -> Prop := .**/
    typedef struct __attribute__ ((__packed__)) {
      uint8_t ip_version_and_len;
      uint8_t ip_traffic_class;
      uint16_t ip_length;
      uint16_t ip_frag_id;
      uint16_t ip_frag_ofs;
      uint8_t ip_ttl;
      uint8_t ip_proto;
      uint16_t ip_chksum;
      uint8_t ip_src[4];
      uint8_t ip_dst[4];
    } ip_header_t;
  /**.

  Goal sizeof ip_header = 20. reflexivity. Succeed Qed. Abort.

  Definition udp_header(r: udp_header_t): word -> mem -> Prop := .**/
    typedef struct __attribute__ ((__packed__)) {
      uint16_t src_port;
      uint16_t dst_port;
      uint16_t udp_length;
      uint16_t udp_checksum;
    } udp_header_t;
  /**.

  Goal sizeof udp_header = 8. reflexivity. Succeed Qed. Abort.
End WithMem.
