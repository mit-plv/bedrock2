(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import bedrock2.TraceInspection.
Require Import bedrock2.e1000_state.
Require Import bedrock2.e1000_read_write_step.
Require Import LiveVerifExamples.mbuf.
Require Import LiveVerifExamples.fmalloc.

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
  } e1000_ctx_raw;
/**.

Definition e1000_ctx(c: e1000_ctx_t)(a: word): mem -> Prop :=
  <{ * e1000_ctx_raw c a
     (* software-owned receive-related memory, ie unused receive descriptors & buffers: *)
     * (EX (unused_rxq_elems: list (rx_desc_t * buf)), <{
         * emp (len unused_rxq_elems + c.(current_rxq_len) = RX_RING_SIZE)
         * circular_buffer_slice (rxq_elem MBUF_SIZE) RX_RING_SIZE
             ((\[c.(current_RDH)] + c.(current_rxq_len)) mod RX_RING_SIZE)
             unused_rxq_elems c.(rx_ring_base)
       }>)
     (* software-owned transmit-related memory, ie unused transmit descriptors & buffers:
        Contrary to receive-related memory, we split buffers and descriptors because
        the buffers are owned by the allocator *)
     * (EX (unused_tx_descs: list tx_desc_t), <{
         * emp (len unused_tx_descs + c.(current_txq_len) = TX_RING_SIZE)
         * circular_buffer_slice tx_desc TX_RING_SIZE
             ((\[c.(current_TDH)] + c.(current_txq_len)) mod TX_RING_SIZE)
             unused_tx_descs c.(tx_ring_base)
       }>)
     * allocator MBUF_SIZE (TX_RING_SIZE - c.(current_txq_len)) c.(tx_buf_allocator)
  }>.

(* Provided by the network stack, not implemented here *)
Instance spec_of_net_rx_eth: fnspec :=                                          .**/

void net_rx_eth(uintptr_t a, uintptr_t n) /**#
  ghost_args := bs (R: mem -> Prop);
  requires t m := <{ * mbuf \[n] bs a
                     * R }> m;
  (* rx may change the mbuf arbitrarily, but must return it *)
  ensures t' m' := t' = t /\ exists bs' n',
       <{ * mbuf n' bs' a
          * R }> m' #**/                                                   /**.


Definition e1000_driver_mem_required: Z :=
  MBUF_SIZE * RX_RING_SIZE + MBUF_SIZE * TX_RING_SIZE +
  sizeof rx_desc * RX_RING_SIZE + sizeof tx_desc * TX_RING_SIZE +
  sizeof fmalloc_state + sizeof e1000_ctx_raw.

Goal exists n: Z, e1000_driver_mem_required = n.
Proof. eexists. cbv. (* ca 66KB *) reflexivity. Succeed Qed. Abort.

#[export] Instance spec_of_e1000_init: fnspec :=                                .**/

uintptr_t e1000_init(uintptr_t b) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := \[b] + e1000_driver_mem_required < 2 ^ bitwidth /\
                  <{ * array (uint 8) e1000_driver_mem_required ? b
                     * R }> m;
  ensures t' m' r := t' = t /\ (* TODO trace will actually have setup interactions *)
       <{ * e1000_ctx ? r
          * R }> m' #**/                                                   /**.
Derive e1000_init SuchThat (fun_correct! e1000_init) As e1000_init_ok.          .**/
{                                                                          /**. .**/
  fmalloc_init(b + MBUF_SIZE * RX_RING_SIZE + MBUF_SIZE * TX_RING_SIZE +
               sizeof(rx_desc) * RX_RING_SIZE + sizeof(tx_desc) * TX_RING_SIZE,
               b + MBUF_SIZE * RX_RING_SIZE, MBUF_SIZE, TX_RING_SIZE);     /**.
  (* TODO it would be nicer to keep the constants folded as much as possible *)
  all: unfold e1000_driver_mem_required, MBUF_SIZE, RX_RING_SIZE, TX_RING_SIZE in *.
  1-3: solve [steps].
  clear Error. steps. do 2 delete #(merge_step).                                .**/
  uintptr_t f = b + MBUF_SIZE * RX_RING_SIZE + MBUF_SIZE * TX_RING_SIZE +
                sizeof(rx_desc) * RX_RING_SIZE + sizeof(tx_desc) * TX_RING_SIZE +
                sizeof(fmalloc_state);                                     /**.
  (* TODO better zify and simplification *)
  lazymatch goal with
  | H: f = _ |- _ => unfold MBUF_SIZE, RX_RING_SIZE, TX_RING_SIZE in H;
                     bottom_up_simpl_in_hyp H
  end.
                                                                                .**/
  /* current_RDH */                                                        /**. .**/
  store(f, 0);                                                             /**. .**/
  /* current_rxq_len */                                                    /**. .**/
  store(f + sizeof(uintptr_t), 0);                                         /**. .**/
  /* current_TDH */                                                        /**. .**/
  store(f + 2 * sizeof(uintptr_t), 0);                                     /**. .**/
  /* current_txq_len */                                                    /**. .**/
  store(f + 3 * sizeof(uintptr_t), 0);                                     /**. .**/
  /* rx_ring_base */                                                       /**. .**/
  store(f + 4 * sizeof(uintptr_t),
        b + MBUF_SIZE * RX_RING_SIZE + MBUF_SIZE * TX_RING_SIZE);          /**. .**/
  /* tx_ring_base */                                                       /**. .**/
  store(f + 5 * sizeof(uintptr_t),
        b + MBUF_SIZE * RX_RING_SIZE + MBUF_SIZE * TX_RING_SIZE +
        sizeof(rx_desc) * RX_RING_SIZE);                                   /**. .**/
  /* tx_buf_allocator */                                                   /**. .**/
  store(f + 6 * sizeof(uintptr_t),
        b + MBUF_SIZE * RX_RING_SIZE + MBUF_SIZE * TX_RING_SIZE +
        sizeof(rx_desc) * RX_RING_SIZE + sizeof(tx_desc) * TX_RING_SIZE);  /**.
  repeat match goal with
  | H: merge_step _ |- _ => clear H
  end.
                                                                                .**/
  return f;                                                                /**. .**/
} /**.
  unfold e1000_ctx, e1000_ctx_raw, anyval. clear Warning.
  step. instantiate (1 := {| current_RDH := _ |}). record.simp.
  steps.
  (* TODO circular_buffer_slice support *)
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
