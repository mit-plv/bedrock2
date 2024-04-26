(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import bedrock2.TraceInspection.
Require Import bedrock2.NetworkPackets.
Require Import LiveVerifExamples.mbuf.
Require Import LiveVerifExamples.e1000.

Require Import coqutil.Map.OfListWord.

Load LiveVerif.


(* should high-level trace be packets expressed as list of bytes
   or as memory chunks? *)

Definition concat_preds(P Q: list byte -> Prop): list byte -> Prop :=
  fun bs => exists bs1 bs2, bs = bs1 ++ bs2 /\ P bs1 /\ Q bs2.

Definition pure_pred(P: Prop): list byte -> Prop := fun bs => bs = nil /\ P.

Definition and_preds(P Q: list byte -> Prop): list byte -> Prop :=
  fun bs => P bs /\ Q bs.

Definition has_len(n: Z): list byte -> Prop := fun bs => len bs = n.

Definition any: list byte -> Prop := fun _ => True.

Definition eqZs(zs: list Z): list byte -> Prop :=
  fun bs => List.map byte.unsigned bs = zs.

Definition mbuf(payload: list byte -> Prop): list byte -> Prop :=
  and_preds (has_len MBUF_SIZE) (concat_preds payload any).

(*
Definition mbuf(n: Z)(bs: list Z): list byte -> Prop :=
  and_preds (has_len MBUF_SIZE) (concat_preds (and_preds (has_len n) (eqZs bs)) any).
*)

Definition eth_header_bytes(h: ethernet_header_t): list byte -> Prop. Admitted.
Definition ip_header_bytes(h: ip_header_t): list byte -> Prop. Admitted.
Definition udp_header_bytes(h: udp_header_t): list byte -> Prop. Admitted.

Definition eth_buf(h: ethernet_header_t)(payload: list byte -> Prop): list byte -> Prop :=
  mbuf (concat_preds (eth_header_bytes h) payload).

Definition ip_buf(eh: ethernet_header_t)(ih: ip_header_t)
  (payload: list byte -> Prop): list byte -> Prop :=
  eth_buf eh (concat_preds (ip_header_bytes ih) payload).

Definition udp_buf(eh: ethernet_header_t)(ih: ip_header_t)(uh: udp_header_t)
  (payload: list byte -> Prop): list byte -> Prop :=
  ip_buf eh ih (concat_preds (udp_header_bytes uh) payload).

(*
Definition eth_buf(h: ethernet_header_t)(n: Z)(bs: list Z): word -> mem -> Prop :=
  exists header_bytes, decode_ethernet_header header_bytes = h /\
  mbuf (sizeof ethernet_header + n) (header_bytes ++ bs)

  <{ * ethernet_header h a
     * array (uint 8) n bs (a ^+ /[sizeof ethernet_header])
     * array (uint 8) (MBUF_SIZE - n - sizeof ethernet_header) ?
         (a ^+ /[sizeof ethernet_header + n]) }>.

Definition eth_buf(h: ethernet_header_t)(n: Z)(bs: list Z)(a: word): mem -> Prop :=
  <{ * ethernet_header h a
     * array (uint 8) n bs (a ^+ /[sizeof ethernet_header])
     * array (uint 8) (MBUF_SIZE - n - sizeof ethernet_header) ?
         (a ^+ /[sizeof ethernet_header + n]) }>.
 TODO define using mbuf? *)

Definition bytes_pred_at(P: list byte -> Prop)(a: word)(m: mem): Prop :=
  exists bs, m = map.of_list_word_at a bs /\ P bs.

Definition eth_buff(h: ethernet_header_t)(n: Z)(zs: list Z): word -> mem -> Prop :=
  bytes_pred_at (eth_buf h (and_preds (has_len n) (eqZs zs))).

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

(* net_tx_eth *)

(* net_tx_ip *)

Instance spec_of_net_tx_udp: fnspec :=                                          .**/

void net_tx_udp(uintptr_t nw, uintptr_t b, uintptr_t n) /**#
  ghost_args := bs (R: mem -> Prop);
  requires t m := <{ * mbuf.mbuf \[n] bs b (* TODO udp_buf *)
                     * R }> m;
  (* rx may change the mbuf arbitrarily, but must return it *)
  ensures t' m' := t' = t /\
       <{ * R * R }> m' #**/                                                   /**.


(** * Receive, top-down: *)

(* net_rx_udp *)

(* net_rx_ip *)

Instance spec_of_net_rx_eth: fnspec :=                                          .**/

void net_rx_eth(uintptr_t a, uintptr_t n) /**#
  ghost_args := bs (R: mem -> Prop);
  requires t m := <{ * mbuf.mbuf \[n] bs a
                     * R }> m;
  (* rx may change the mbuf arbitrarily, but must return it *)
  ensures t' m' := t' = t /\ exists bs' n',
       <{ * mbuf.mbuf n' bs' a
          * R }> m' #**/                                                   /**.


End LiveVerif. Comments .**/ //.
