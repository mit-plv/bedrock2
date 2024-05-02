(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import bedrock2.TraceInspection.
Require Import bedrock2.e1000_state.
Require Import bedrock2.e1000_read_write_step.
Require Import bedrock2.e1000_packet_trace.
Require Import LiveVerifExamples.mbuf.
Require Import LiveVerifExamples.fmalloc.
Require Import LiveVerifExamples.e1000_mmio_spec.

(* TODO it would be nice to not import all of LiveVerifExamples.network.
   We only need spec_of_net_rx_eth (to call it), which we could duplicate or put into
   a separate specs-only file,
   and the ethernet_header predicate, which could also be in its own ethernet-specific
   file.
   For the moment, just importing all the network stack seems easier, but TODO reconsider
   once compilation times and lack of build parallelism starts to matter. *)
Require Import LiveVerifExamples.network.


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
  rxq_tail: Z; (* receive descriptor queue tail (RDT) *)
  unused_rx_len: Z; (* number of unused rx descriptors *)
  undelivered_rx_len: Z; (* number of packets received, but not yet delivered to stack *)
  current_TDH: Z; (* transmit descriptor queue head *)
  current_txq_len: Z;
  rx_ring_base: word; (* TODO enforce 16-byte alignment *)
  tx_ring_base: word; (* TODO enforce 16-byte alignment *)
  (* rx buffers are statically allocated, tx buffers dynamically, because they
     live beyond the return from the transmit function *)
  tx_buf_allocator: word;
}.

Definition e1000_ctx_raw(c: e1000_ctx_t): word -> mem -> Prop := .**/
  typedef struct __attribute__ ((__packed__)) {
    uint32_t rxq_tail;
    uint32_t unused_rx_len;
    uint32_t undelivered_rx_len;
    uint32_t current_TDH;
    uint32_t current_txq_len;
    uintptr_t rx_ring_base;
    uintptr_t tx_ring_base;
    uintptr_t tx_buf_allocator;
  } e1000_ctx_raw;
/**.

(*
             RDT --> +-------------+     ---       ---
                     | unused      |      |         |
undelivered_head --> +-------------+   SW-owned     | anywhere in here,
                     | undelivered |      |         | circular buffer
             RDH --> +-------------+     ---        | wraps around
                     | rx queue    |   HW-owned     |
             RDT --> +-------------+     ---       ---

*)

Definition e1000_ctx(c: e1000_ctx_t)(a: word): mem -> Prop :=
  <{ * e1000_ctx_raw c a
     (* software-owned receive-related memory,
        ie unused & undelivered receive descriptors & buffers: *)
     * (EX (unused_rx undelivered_rx : list (rx_desc_t * buf)), <{
         * emp (len unused_rx = c.(unused_rx_len) /\
                len undelivered_rx = c.(undelivered_rx_len) /\
                (* at least 1 so that RDT does not hit RDH *)
                1 <= c.(unused_rx_len) + c.(undelivered_rx_len) <= RX_RING_SIZE)
         * circular_buffer_slice (rxq_elem MBUF_SIZE) RX_RING_SIZE
             c.(rxq_tail) (unused_rx ++ undelivered_rx) c.(rx_ring_base)
       }>)
     (* software-owned transmit-related memory, ie unused transmit descriptors & buffers:
        Contrary to receive-related memory, we split buffers and descriptors because
        the buffers are owned by the allocator *)
     * (EX (unused_tx_descs: list tx_desc_t), <{
         * emp (len unused_tx_descs + c.(current_txq_len) = TX_RING_SIZE)
         * circular_buffer_slice tx_desc TX_RING_SIZE
             ((c.(current_TDH) + c.(current_txq_len)) mod TX_RING_SIZE)
             unused_tx_descs c.(tx_ring_base)
       }>)
     * allocator MBUF_SIZE (TX_RING_SIZE - c.(current_txq_len)) c.(tx_buf_allocator)
  }>.


Definition e1000_driver_mem_required: Z :=
  MBUF_SIZE * RX_RING_SIZE + MBUF_SIZE * TX_RING_SIZE +
  sizeof rx_desc * RX_RING_SIZE + sizeof tx_desc * TX_RING_SIZE +
  sizeof fmalloc_state + sizeof e1000_ctx_raw.

Goal exists n: Z, e1000_driver_mem_required = n.
Proof. eexists. cbv. (* ca 66KB *) reflexivity. Succeed Qed. Abort.

Local Hint Unfold e1000_ctx : heapletwise_always_unfold.

(* TODO circular_buffer_slice can't fit into the PredicateSize framework
   because its range might consist of two chunks and doesn't always start at its
   base address, so automating memory accesses inside a circular_buffer_slice
   won't work well!
   Split into first part and potentially overflowing part?
   Maybe by changing its definition, or using an alternative definition and
   conversion lemma?  *)
Local Hint Extern 1 (PredicateSize_not_found (circular_buffer_slice _ _ _ _))
      => constructor : suppressed_warnings.

(* Calls net_rx_eth 1x with the oldest undelived packet if some packets are
   undelivered. Doesn't call the uper layer if no new packets are available.
   Meant to be called from toplevel loop. *)
#[export] Instance spec_of_e1000_rx: fnspec :=                                  .**/

void e1000_rx(uintptr_t c) /**#
  ghost_args := ctx pks (R: mem -> Prop);
  requires t m := (* +2 because 1 to keep TDH and TDT from clashing aind 1 to
                     make sure we have space to send (at least the beginning of)
                     the reply *)
                  current_txq_len ctx + 2 <= TX_RING_SIZE /\
                  packet_trace_rel pks t /\
                  <{ * e1000_ctx ctx c
                     * R }> m;
  ensures t' m' := exists pks',
       packet_trace_rel (pks ++ pks') t' /\ exists c',
       <{ * e1000_ctx ctx c'
          * R }> m' #**/                                                   /**.
Derive e1000_rx SuchThat (fun_correct! e1000_rx) As e1000_rx_ok.                .**/
{                                                                          /**. .**/
  uintptr_t undelivered_len = load32(c+8);                                 /**. .**/
  if (undelivered_len == 0) /* split */ {                                  /**. .**/
    uintptr_t new_head = e1000_read_RDH();                                 /**.
    all: try record.simp_hyps.

Abort.


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
  /* rxq_tail */                                                           /**. .**/
  store32(f, 0);                                                           /**. .**/
  /* unused_rx_len */                                                      /**. .**/
  store32(f + 4, 0);                                                       /**. .**/
  /* undelivered_rx_len */                                                 /**. .**/
  store32(f + 8, 0);                                                       /**. .**/
  /* current_TDH */                                                        /**. .**/
  store32(f + 12, 0);                                                      /**. .**/
  /* current_txq_len */                                                    /**. .**/
  store32(f + 16, 0);                                                      /**. .**/
  /* rx_ring_base */                                                       /**. .**/
  store32(f + 20,
        b + MBUF_SIZE * RX_RING_SIZE + MBUF_SIZE * TX_RING_SIZE);          /**. .**/
  /* tx_ring_base */                                                       /**. .**/
  store32(f + 20 + sizeof(uintptr_t),
        b + MBUF_SIZE * RX_RING_SIZE + MBUF_SIZE * TX_RING_SIZE +
        sizeof(rx_desc) * RX_RING_SIZE);                                   /**. .**/
  /* tx_buf_allocator */                                                   /**. .**/
  store32(f + 20 + 2 * sizeof(uintptr_t),
        b + MBUF_SIZE * RX_RING_SIZE + MBUF_SIZE * TX_RING_SIZE +
        sizeof(rx_desc) * RX_RING_SIZE + sizeof(tx_desc) * TX_RING_SIZE);  /**.
  repeat match goal with
  | H: merge_step _ |- _ => clear H
  end.
                                                                                .**/
  return f;                                                                /**. .**/
} /**.
  unfold e1000_ctx, e1000_ctx_raw, anyval. clear Warning.
  step. instantiate (1 := {| tx_buf_allocator := _ |}). record.simp.
  steps.
  (* TODO circular_buffer_slice support *)
Abort.

End LiveVerif. Comments .**/ //.
