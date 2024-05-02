(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import bedrock2.TraceInspection.
Require Import bedrock2.NetworkPackets.
Require Import bedrock2.e1000_packet_trace.
Require Import LiveVerifExamples.mbuf.

Record headers_upto_ip_t: Set := {
  before_ip_header: ethernet_header_t;
  only_ip_header: ip_header_t;
}.

Record headers_upto_udp_t: Set := {
  before_udp_header: headers_upto_ip_t;
  only_udp_header: udp_header_t;
}.

Require Import coqutil.Map.OfListWord.

Load LiveVerif.

Definition headers_upto_ip(h: headers_upto_ip_t): word -> mem -> Prop :=
  <{ + ethernet_header (before_ip_header h)
     + ip_header (only_ip_header h) }>.

Definition headers_upto_udp(h: headers_upto_udp_t): word -> mem -> Prop :=
  <{ + headers_upto_ip (before_udp_header h)
     + udp_header (only_udp_header h) }>.

(* in the packet_trace, the excess bytes of mbufs don't appear, but in mbufs, they do *)

Definition eth_buff(h: ethernet_header_t)(n: Z)(zs: list Z): word -> mem -> Prop.
Admitted.

Axiom network: word -> mem -> Prop. (* TODO takes more params *)

(** * Alloc/free packets, bottom-up: *)

Instance spec_of_net_alloc_eth: fnspec :=                                          .**/

uintptr_t net_alloc_eth(uintptr_t nw) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * network nw
                     * R }> m;
  ensures t' m' r := t' = t /\ exists h,
       <{ * network nw
          * eth_buff h 0 nil r
          * R }> m' #**/                                                   /**.


(** * Transmit, bottom-up: *)

Definition ethernet_reply(req_h: ethernet_header_t)(resp_payload: word -> mem -> Prop)
  {resp_payload_sz: PredicateSize resp_payload}: word -> mem -> Prop :=
  <{ + ethernet_header {|
         src_mac := dst_mac req_h;
         dst_mac := src_mac req_h;
         ethertype := ethertype req_h;
       |}
     + resp_payload }>.

(* TODO net_tx_eth *)

Definition IPv4_WITH_NO_OPTIONS := Z.lor (Z.shiftl 4 4) 5.
Definition IP_TTL := 64.

Definition ip_reply(req_h: headers_upto_ip_t)(proto: Z)(resp_payload: word -> mem -> Prop)
  {resp_payload_sz: PredicateSize resp_payload}: word -> mem -> Prop :=
  ethernet_reply (before_ip_header req_h)
    <{ + ip_header {|
           ip_v_and_ihl := IPv4_WITH_NO_OPTIONS;
           ip_traffic_class := 0;
           ip_length := 20 + resp_payload_sz;
           ip_frag_id := 0;
           ip_frag_ofs := 0;
           ip_ttl := IP_TTL;
           ip_proto := proto;
           ip_chksum := 0; (* filled in by NIC -- TODO configure NIC *)
           ip_src := ip_dst (only_ip_header req_h);
           ip_dst := ip_src (only_ip_header req_h) |}
       + resp_payload }>.

(* TODO net_tx_ip *)

Definition IP_PROTO_ICMP := 1.
Definition IP_PROTO_TCP := 6.
Definition IP_PROTO_UDP := 17.

Definition udp_reply(req_h: headers_upto_udp_t)(resp_payload: word -> mem -> Prop)
  {resp_payload_sz: PredicateSize resp_payload}: word -> mem -> Prop :=
  ip_reply (before_udp_header req_h) IP_PROTO_UDP
    <{ + udp_header {|
           src_port := dst_port (only_udp_header req_h);
           dst_port := src_port (only_udp_header req_h);
           udp_length := 8 + resp_payload_sz;
           udp_checksum := 0; (* optional, 0 means unused *)
         |}
       + resp_payload }>.

Import ReversedListNotations.

(*
Instance spec_of_net_tx_udp: fnspec :=                                          .**/

void net_tx_udp(uintptr_t nw, uintptr_t b, uintptr_t n,
                uintptr_t dst_ip, uintptr_t dstPort, uintptr_t srcPort) /**#
  ghost_args := (body: word -> mem -> Prop)
                pks foo req_h (R: mem -> Prop);
  requires t m := <{ * network nw
                     * mbuf \[n] (anyval headers_upto_udp) (*<{ + anyval headers_upto_udp
                                    + body }>*) b
                     * R }> m;
  ensures t' m' := t' = t /\ foo (pks ;+ TxPacket (udp_reply req_h body))
    /\ <{ * R * R }> m' #**/                                                   /**.
*)

(** * Receive, top-down: *)

(* net_rx_udp *)

(* net_rx_ip *)

Instance spec_of_net_rx_eth: fnspec :=                                          .**/

void net_rx_eth(uintptr_t a, uintptr_t n) /**#
  ghost_args := bs (R: mem -> Prop);
  requires t m := <{ * mbuf \[n] bs a
                     * R }> m;
  (* rx may change the mbuf arbitrarily, but must return it *)
  ensures t' m' := t' = t /\ exists bs' n',
       <{ * mbuf n' bs' a
          * R }> m' #**/                                                   /**.

End LiveVerif. Comments .**/ //.
