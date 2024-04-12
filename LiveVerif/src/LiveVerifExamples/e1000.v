(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import bedrock2.TraceInspection.
Require Import bedrock2.e1000_state.
Require Import bedrock2.e1000_read_write_step.
Require Import LiveVerifExamples.mbuf.

Load LiveVerif.

(* TODO not sure if RegisterSpec should remain *)
Coercion RegisterSpec_to_Z(r: RegisterSpec): Z :=
  word.unsigned (register_address r).

Goal exists z: Z, expr.literal E1000_RDBAL = expr.literal z.
  eexists. unfold E1000_RDBAL.
Abort.

Definition RX_RING_SIZE: Z := 16.
Definition TX_RING_SIZE: Z := 16.

Record e1000_ctx_t := {
  current_RDH: word; (* receive descriptor queue head *)
  current_rxq_len: Z;
  current_TDH: word; (* transmit descriptor queue head *)
  current_txq_len: Z;
  rx_ring_base: word; (* TODO enforce 16-byte alignment *)
  tx_ring_base: word; (* TODO enforce 16-byte alignment *)
  (* rx buffers are statically allocated, tx buffers dynamically, because they
     live beyond the return from the transmit function *)
  tx_buf_allocator: word;
}.

Definition e1000_ctx_raw(c: e1000_ctx_t): word -> mem -> Prop := .**/
  typedef struct __attribute__ ((__packed__)) {
    uintptr_t current_RDH;
    size_t current_rxq_len;
    uintptr_t current_TDH;
    size_t current_txq_len;
    uintptr_t rx_ring_base;
    uintptr_t tx_ring_base;
    uintptr_t tx_buf_allocator;
  } e1000_ctx_t;
/**.

(*
Definition e1000_ctx(c: e1000_ctx_t)(a: word): mem -> Prop :=
  <{ * e1000_ctx_raw c a
     * circular_buffer_slice ...
*)

(* Provided by the network stack, not implemented here *)
Instance spec_of_net_rx_eth: fnspec :=                                          .**/

void net_rx_eth(uintptr_t a) /**#
  ghost_args := mb (R: mem -> Prop);
  requires t m := <{ * mbuf mb a
                     * R }> m;
  (* rx may change the mbuf arbitrarily, but must return it *)
  ensures t' m' := t' = t /\ exists mb',
       <{ * mbuf mb' a
          * R }> m' #**/                                                   /**.


#[export] Instance spec_of_e1000_init: fnspec :=                                .**/

uintptr_t e1000_init(uintptr_t b) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * array (uint 8) (sizeof e1000_ctx_raw) ? b
                     * R }> m;
  ensures t' m' r := t' = t /\
       <{ * e1000_ctx_raw (* TODO not raw *) ? r
          * R }> m' #**/                                                   /**.
Derive e1000_init SuchThat (fun_correct! e1000_init) As e1000_init_ok.          .**/
{                                                                          /**.
Abort.

#[export] Instance spec_of_e1000_rx: fnspec :=                                  .**/

void e1000_rx(uintptr_t c) /**#
  ghost_args := ctx (R: mem -> Prop);
  requires t m := <{ * e1000_ctx_raw ctx c
                     * R }> m;
  ensures t' m' := t' = t /\
       <{ * e1000_ctx_raw ctx c
          * R }> m' #**/                                                   /**.
Derive e1000_rx SuchThat (fun_correct! e1000_rx) As e1000_rx_ok.                .**/
{                                                                          /**.
Abort.

End LiveVerif. Comments .**/ //.
