(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import bedrock2.TraceInspection.
Require Import bedrock2.NetworkPackets.
Require Import bedrock2.e1000_packet_trace.
Require Import LiveVerifExamples.e1000.
Require Import LiveVerifExamples.mbuf.

(* preamble and start frame delimiter are already removed by the NIC *)
Definition headers_upto_ethernet_t := ethernet_header_t.

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

Definition headers_upto_ethernet: headers_upto_ethernet_t -> word -> mem -> Prop :=
  ethernet_header.

Definition headers_upto_ip(h: headers_upto_ip_t): word -> mem -> Prop :=
  <{ + headers_upto_ethernet (before_ip_header h)
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

(* Note: specialized to the case where we *reply* to some incoming packet and
   still have the buffer of the incoming packet available to copy values from,
   so we can e.g. find the MAC address there instead of having to maintain an
   IP-to-MAC database *)
Instance spec_of_net_tx_udp_reply: fnspec :=                                    .**/

void net_tx_udp(uintptr_t nw, uintptr_t req, uintptr_t resp, uintptr_t n) /**#
  ghost_args := bs pks req_h (R: mem -> Prop);
  requires t m :=
    packet_trace_rel pks t /\
    <{ * network nw
       * mbuf (headers_upto_udp req_h) req
       * mbuf (udp_reply req_h (array (uint 8) \[n] bs)) resp
       * R }> m;
  ensures t' m' :=
    packet_trace_rel (pks ;+ TxPacket (udp_reply req_h (array (uint 8) \[n] bs))) t' /\
    (* note: resp mbuf is consumed by network *)
    <{ * network nw
       * mbuf (headers_upto_udp req_h) req
       * R }> m' #**/                                                   /**.


(** * Receive, top-down: *)

(* net_rx_udp *)

(* net_rx_ip *)

Goal forall
  (callee_correct: forall (V: Type) (pred: V -> word -> mem -> Prop)
                          (* note: cannot be marked as implicit *)
                          (pred_sz: PredicateSize pred)
                          (x: V),
      Some (pred x) = None)
  (v: Z),
    Some (uint 16 v) = None.
Proof.
  intros.
  (* eapply callee_correct. does not infer PredicateSize *)
  Tactics.rapply callee_correct. (* infers PredicateSize *)
Succeed Qed. Abort.

(*
Definition ethernet_buf :=
  mbuf n <{ + headers_upto_ethernet h
            + payload }>.

Definition udp_buf :=
*)

(* Q: how to abstract over offsets/packet header sizes?
   A: just use UDP_HEADER_OFFSET constant
   OR increase mbuf pointer? but in replies, pointer would point at beginning
   of header, ie into inside of ..._reply, so NO *)

Instance spec_of_net_rx_eth: fnspec :=                                          .**/

void net_rx_eth(uintptr_t a, uintptr_t n) /**#
  ghost_args := h bs (R: mem -> Prop);
  requires t m := <{ * mbuf
                       <{ + headers_upto_ethernet h
                          + array (uint 8) (\[n] - sizeof headers_upto_ethernet) bs }> a
                     * R }> m;
  (* rx may change the mbuf arbitrarily, but must return its bytes *)
  ensures t' m' := t' = t /\
       <{ * mbuf (emp_at_addr True) a
          * R }> m' #**/                                                   /**.
(* Note: net_rx_eth is only called once the packets have already been received,
   so the trace doesn't change *)

(* Note: we can't alloc/free mbuf with an abstract predicate,
   but we can if the predicate is a concrete (array (uint 8)), or emp (and n = 0 and all
   bytes unused) *)

End LiveVerif. Comments .**/ //.
