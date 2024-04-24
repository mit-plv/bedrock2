Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String. Local Open Scope string_scope.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Datatypes.ZList.
Require Import bedrock2.ReversedListNotations. Local Open Scope list_scope.
Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
Require Import bedrock2.TraceInspection.
Require Import bedrock2.RecordPredicates.
Require Import bedrock2.e1000_state.
Require Import bedrock2.e1000_read_write_step.

Inductive packet_event: Set :=
| RxPacket(b: buf)
| TxPacket(b: buf).

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.

  Axiom BootSeq: Semantics.trace.

  (* Abstracts a trace of MMIO/DMA events (Semantics.trace)
     into a list of sent/received packets (list packet_event).
     Doesn't repeat all the sideconditions from e1000_read/write_step, but
     only as much as is needed to relate the low-level event to the correct
     high-level events. *)
  Inductive packet_trace_rel: list packet_event -> Semantics.trace -> Prop :=
  | packet_trace_rel_init:
      packet_trace_rel nil BootSeq
  (* receive packets *)
  | packet_trace_rel_rx t s pks (rcvd: list (rx_desc_t * buf)) mRcv newRDH:
      packet_trace_rel pks t ->
      e1000_initialized s t ->
      circular_buffer_slice (rxq_elem s.(rx_buf_size))
            s.(rx_queue_cap) s.(rx_queue_head) rcvd s.(rx_queue_base_addr) mRcv ->
      packet_trace_rel (pks ;++ List.map (fun '(desc, buffer) => RxPacket buffer) rcvd)
        (t ;+ ((map.empty, "memory_mapped_extcall_read32", [|register_address E1000_RDH|]),
               (mRcv, [|newRDH|])))
  (* software provides new receive buffers to NIC: ignored in packet trace *)
  | packet_trace_rel_rx_refill t pks mGive newRDT:
      packet_trace_rel pks t ->
      packet_trace_rel pks
        (t ;+ ((mGive, "memory_mapped_extcall_write32",
                 [|register_address E1000_RDT; newRDT|]),
               (map.empty, nil)))
  (* send packets *)
  | packet_trace_rel_tx t s pks (sent: list (tx_desc_t * buf)) mGive oldTDT newTDT:
      packet_trace_rel pks t ->
      e1000_initialized s t ->
      getTDT t oldTDT ->
      circular_buffer_slice txq_elem s.(tx_queue_cap) oldTDT sent
        s.(tx_queue_base_addr) mGive ->
      packet_trace_rel (pks ;++ List.map (fun '(desc, buffer) => TxPacket buffer) sent)
        (t ;+ ((mGive, "memory_mapped_extcall_write32",
                 [|register_address E1000_TDT; newTDT|]),
               (map.empty, nil)))
  (* recycle sent buffers: ignored in packet trace *)
  | packet_trace_rel_tx_recyle t pks mRcv newTDH:
      packet_trace_rel pks t ->
      packet_trace_rel pks
        (t ;+ ((map.empty, "memory_mapped_extcall_read32", [|register_address E1000_TDH|]),
               (mRcv, [|newTDH|]))).

End WithMem.

(* TODO reuse some definitions made here in e1000_read_write_step? *)
(* OR rewrite e1000_read/write_step so that they spit out lists of received/sent packets? *)
