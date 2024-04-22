(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import bedrock2.TraceInspection.
Require Import bedrock2.e1000_state.
Require Import bedrock2.e1000_read_write_step.

(* Note: The *specs* are stated as if they were generic over any ext_spec,
   even though ext_spec needs to be the e1000 ext_spec for the implemenation
   to conform to the spec, but keeping the specs generic makes it easier
   to be compatible with all LiveVerifExamples files that have a generic
   ext_spec *)
Load LiveVerif.

(* Note: We don't name the instance spec_of_e1000_read_RDH, but just plain e1000_read_RDH,
   to make sure that this identifier is a definition, which is needed for the parser
   (at call sites) to work even when the implementation is not imported there *)
#[export] Instance e1000_read_RDH: fnspec := .**/
uintptr_t e1000_read_RDH( ) /**#
  ghost_args := s mNIC rxq txq;
  requires t m :=
    externally_owned_mem t mNIC /\
    e1000_initialized s t /\
    e1000_invariant s rxq txq mNIC;
  ensures t' m' new_RDH := exists mRcv (done: list (rx_desc_t * buf)),
    (* need explicit mRcv because it appears in trace *)
    map.split m' m mRcv /\
    \[new_RDH] = (s.(rx_queue_head) + len done) mod s.(rx_queue_cap) /\
    len done <= len rxq /\
    List.map fst done = List.map fst rxq[:len done] /\
    (* snd (new buffer) can be any bytes *)
    circular_buffer_slice (rxq_elem s.(rx_buf_size))
      s.(rx_queue_cap) s.(rx_queue_head) done s.(rx_queue_base_addr) mRcv /\
    t' = cons ((map.empty,
               "memory_mapped_extcall_read32",
               [| register_address E1000_RDH |]),
              (mRcv, [|new_RDH|])) t  #**/ /**.

End LiveVerif.
