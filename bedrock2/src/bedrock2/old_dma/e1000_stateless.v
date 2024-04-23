(*
Formalization of a subset of the functionality of Intel's 8254x Network Interface Cards.

PDF Spec:

PCI/PCI-X Family of Gigabit Ethernet Controllers Software Developer's Manual
82540EP/EM, 82541xx, 82544GC/EI, 82545GM/EM, 82546GB/EB, and 82547xx
https://www.intel.com/content/dam/doc/manual/pci-pci-x-family-gbe-controllers-software-dev-manual.pdf

These network cards were launched in the 2000s and discontinued in the 2010s, but continue to be a popular choice for virtualization, where they are often referred to as "e1000".
 *)

Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Z.BitOps.
Require coqutil.Map.SortedListZ.
Require Import coqutil.Datatypes.ZList.
Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
Require Import coqutil.Datatypes.RecordSetters. Import DoubleBraceUpdate.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.old_dma.StateMachineBasedExtSpec_wp.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.
Require Import bedrock2.SepBulletPoints. Local Open Scope sep_bullets_scope.
Require Import bedrock2.RecordPredicates.
Require Import bedrock2.TraceInspection.
Require Import bedrock2.e1000_state. (* for rx/tx_desc and separation logic definitions *)
Require Import bedrock2.old_dma.circular_buffer_slice_based_on_list_of_addrs.

(* Not part of the spec, but a convention we chose to hardcode here: *)
Definition E1000_REGS := 0x40000000.

(* Bitfields of Receive Control Register (Section 13.4.22) *)
Module RCTL.
  (* Bit 0 is reserved *)
  Definition EN := 1. (* Receiver Enable *)
  Definition SBP := 2. (* Store Bad Packets *)
  Definition UPE := 3. (* Unicast Promiscuous Enabled *)
  Definition MPE := 4. (* Multicast Promiscuous Enabled *)
  Definition LPE := 5. (* Long Packet Reception Enable *)
  Definition LBM_start := 6. (* Loopback mode *)
  Definition LBM_pastend := 8.
  Definition RDMTS_start := 8. (* Receive Descriptor Minimum Threshold Size *)
  Definition RDMTS_pastend := 10.
  (* Bits 10 and 11 are reserved *)
  Definition MO_start := 12. (* Multicast Offset *)
  Definition MO_pastend := 14.
  (* Bit 14 is reserved *)
  Definition BAM := 15. (* Broadcast Accept Mode. *)
  Definition BSIZE_start := 16. (* Receive Buffer Size *)
  (* If RCTL.BSEX = 0b: 00b =   2048 B, 01b =  1024 B, 10b =  512 B, 11b =  256 B.
     If RCTL.BSEX = 1b: 00b = Reserved, 01b = 16384 B, 10b = 8192 B, 11b = 4096 B. *)
  Definition BSIZE_pastend := 18.
  Definition VFE := 18. (* VLAN Filter Enable *)
  Definition CFIEN := 19. (* Canonical Form Indicator Enable *)
  Definition CFI := 20. (* Canonical Form Indicator bit value *)
  (* Bit 21 is reserved *)
  Definition DPF := 22.
  Definition PMCF := 23. (* Pass MAC Control Frames *)
  (* Bit 24 is reserved *)
  Definition BSEX := 25. (* Buffer Size Extension *)
  Definition SECRC := 26. (* Strip Ethernet CRC from incoming packet *)
  (* Bits 27 to 31 are reserved *)
End RCTL.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.

  Local Notation IReg ofs init := (InitializedRegister (E1000_REGS + ofs) init)
    (only parsing).
  Local Notation UReg ofs := (UninitializedRegister (E1000_REGS + ofs))
    (only parsing).

  (* E1000 register offsets from Section 13.4 *)

  Definition E1000_RCTL := IReg 0x100 0. (* Receive Control Register *)

  Definition E1000_RDBAL := UReg 0x2800. (* base addr (lo 32 bits) of receive queue *)
  Definition E1000_RDBAH := UReg 0x2804. (* base addr (hi 32 bits) of receive queue *)
  Definition E1000_RDLEN := IReg 0x2808 0. (* length of receive queue in bytes *)
  Definition E1000_RDH := IReg 0x2810 0. (* receive queue head *)
  Definition E1000_RDT := IReg 0x2818 0. (* receive queue tail *)
  Definition E1000_TDBAL := UReg 0x3800. (* base addr (lo 32 bits) of transmit queue *)
  Definition E1000_TDBAH := UReg 0x3804. (* base addr (hi 32 bits) of transmit queue *)
  Definition E1000_TDLEN := IReg 0x3808 0. (* length of transmit queue in bytes *)
  Definition E1000_TDH := IReg 0x3810 0. (* transmit queue head *)
  Definition E1000_TDT := IReg 0x3818 0. (* transmit queue tail *)

  Definition pick_st{A: Type}(p: A -> Prop)(k: A -> Prop) :=
    forall x, p x -> k x.

  Notation "'let/c' x := r 'in' b" := (r (fun x => b))
    (x binder, at level 200, right associativity,
     (* TODO enable printing once we're using Coq 8.19,
        where https://github.com/coq/coq/issues/15221 is fixed *)
     (* format "'[hv' 'let/c'  x  :=  r  'in'  '//' b ']'", *)
     only parsing).

  (* TODO some registers are safe to get using `get_rw_reg REG_NAME`, whereas others
     have "ignore on write" semantics and thus need a special get_rw_REGNAME.
     How can we enforce one never forgets to use the special getter if there is one? *)

  Definition get_RDBAL(t: trace)(ret: word -> Prop) :=
    let/c rdbal := get_rw_reg E1000_RDBAL t in
    ret /[Z.land (Z.lnot 0xf) \[rdbal]].

  Definition get_RDBAH := get_rw_reg E1000_RDBAH.

  Definition get_RDBA(t: trace)(ret: word -> Prop): Prop :=
    let/c rdbal := get_RDBAL t in
    let/c rdbah := get_RDBAH t in
    exists rdba, \[rdba] = \[rdbal] + \[rdbah] * 2^32 /\ ret rdba.

  Definition get_TDBAL(t: trace)(ret: word -> Prop) :=
    let/c tdbal := get_rw_reg E1000_TDBAL t in
    ret /[Z.land (Z.lnot 0xf) \[tdbal]].

  Definition get_TDBAH := get_rw_reg E1000_TDBAH.

  Definition get_TDBA(t: trace)(ret: word -> Prop): Prop :=
    let/c tdbal := get_TDBAL t in
    let/c tdbah := get_TDBAH t in
    exists tdba, \[tdba] = \[tdbal] + \[tdbah] * 2^32 /\ ret tdba.

  Definition get_descriptor_length(r: RegisterSpec)(t: trace)(ret: word -> Prop) :=
    let/c l := get_rw_reg r t in
    ret /[Z.land (Z.lnot 0x7f) \[l]].

  Definition set_descriptor_length(r: RegisterSpec)(v: word)(t: trace)
    (ret: mem -> list word -> Prop): Prop :=
    Z.land (Z.shiftl (Z.ones 12) 20) \[v] = 0 /\ (* bits 31:20 must be 0 *)
    ret map.empty nil.

  Definition get_rx_queue_cap(t: trace)(ret: Z -> Prop) :=
    let/c rdlen := get_descriptor_length E1000_RDLEN t in
    exists n, n * 16 = \[rdlen] /\ ret n.

  Definition get_tx_queue_cap(t: trace)(ret: Z -> Prop) :=
    let/c tdlen := get_descriptor_length E1000_TDLEN t in
    exists n, n * 16 = \[tdlen] /\ ret n.

  Definition get_set_descriptor_length(r: RegisterSpec)(t: trace)
                    (ret: mem -> list word -> Prop): RegisterBehavior := {|
    read := let/c v := get_descriptor_length r t in ret map.empty [|v|];
    write v := set_descriptor_length r v t ret
  |}.

  (* Size of the receive buffers. If a packet doesn't fit, it is split into multiple
     buffers, using multiple descriptors.
     If RCTL.BSEX = 0b: 00b =   2048 B, 01b =  1024 B, 10b =  512 B, 11b =  256 B.
     If RCTL.BSEX = 1b: 00b = Reserved, 01b = 16384 B, 10b = 8192 B, 11b = 4096 B. *)
  Definition get_rx_buf_size(t: trace)(ret: Z -> Prop) :=
    let/c rctl := get_rw_reg E1000_RCTL t in
    let bsex := Z.testbit \[rctl] RCTL.BSEX in
    let bsize := bitSlice \[rctl] RCTL.BSIZE_start RCTL.BSIZE_pastend in
    if bsex then
      match bsize with
      | 1 => ret 16384
      | 2 => ret 8192
      | 3 => ret 4096
      | _ => False
      end
    else
      match bsize with
      | 0 => ret 2048
      | 1 => ret 1024
      | 2 => ret 512
      | 3 => ret 256
      | _ => False
      end.

  Definition get_set(getter: trace -> (word -> Prop) -> Prop)(t: trace)
                    (ret: mem -> list word -> Prop): RegisterBehavior := {|
    read := let/c v := getter t in ret map.empty [|v|];
    write v := ret map.empty nil;
  |}.

  Global Instance e1000_step: ExtSpec :=
    fun (t: trace)(mGive: mem)(action: String.string)(args: list word)
        (ret: mem -> list word -> Prop) =>
      exists mNIC, externally_owned_mem t mNIC /\
      (((* Initialization operations: only allowed if no memory owned by NIC.
           Might be a bit more restrictive than needed, but e.g. changing the
           queue size on-the-fly sounds a bit scary, so we require that software
           refrains from performing such dubious operations. *)
        mNIC = map.empty /\
        mGive = map.empty /\
        dispatch action args [|
          (E1000_RDBAL, get_set get_RDBAL t ret);
          (E1000_RDBAH, get_set get_RDBAH t ret);
          (E1000_RDLEN, get_set_descriptor_length E1000_RDLEN t ret);
          (E1000_TDBAL, get_set get_TDBAL t ret);
          (E1000_TDBAH, get_set get_TDBAH t ret);
          (E1000_TDLEN, get_set_descriptor_length E1000_TDLEN t ret)
        |]) \/
       ((* Main operations: only allowed if rx and tx functionality of NIC both are
           initialized. Might also be a bit more restrictive than needed, but we
           don't currently need a setup where only one of rx/tx is initialized, and
           we already want to use it without initializing the other. *)
         let/c rdba := get_RDBA t in
         let/c rdh := get_rw_reg E1000_RDH t in
         let/c rx_queue_cap := get_rx_queue_cap t in
         let/c rx_buf_size := get_rx_buf_size t in
         let/c tdba := get_TDBA t in
         let/c tdh := get_rw_reg E1000_TDH t in
         let/c tx_queue_cap := get_tx_queue_cap t in
         exists rxq txq rx_bufs tx_bufs, (* <- ghost vars determined by mNIC *)
         let rx_buf_addrs := List.map (fun d => /[d.(rx_desc_addr)]) rxq in
         let tx_buf_addrs := List.map (fun d => /[d.(tx_desc_addr)]) txq in
         <{ (* receive-related: *)
            * circular_buffer_slice rx_desc rx_queue_cap \[rdh] rxq rdba
            * scattered_array (array (uint 8) rx_buf_size) rx_bufs rx_buf_addrs
            (* transmit-related: *)
            * circular_buffer_slice tx_desc tx_queue_cap \[tdh] txq tdba
            * layout_absolute (List.map (fun pkt => array' (uint 8) pkt) tx_bufs)
                              tx_buf_addrs
         }> mNIC /\
         dispatch action args [|
           (E1000_RDH, {|
              (* new RDH can be anywhere between old RDH (incl) and old RDT (excl),
                 we receive the memory chunk for each descriptor between old and new RDH,
                 as well as the buffers pointed to by them, which contain newly received
                 packets *)
              read := (* nondeterministic choices: *)
                forall (new_rdh: word) (new_bufs: list buf) (mReceive: mem),
                (* constrained as follows: *)
                len new_bufs <= len rxq ->
                \[new_rdh] = (\[rdh] + len new_bufs) mod rx_queue_cap ->
                (* we get back a (wrapping) slice of the rx queue as well as the
                   corresponding buffers *)
                <{ * circular_buffer_slice rx_desc rx_queue_cap \[rdh]
                       rxq[:len new_bufs] rdba
                   * scattered_array (array (uint 8) rx_buf_size) new_bufs
                       (List.map (fun d => /[d.(rx_desc_addr)]) rxq[:len new_bufs])
                }> mReceive ->
                (* end of constraints to assume, now follows what we need to prove
                   to prove ext_spec: *)
                ret mReceive [|new_rdh|];
              write v := False (* because hardware controls the pointer (see 13.4.28) *)|})
         |])).

(* TODO what about 13.4.28 "Reading the descriptor head to determine which buffers are
   finished is not reliable" and 13.4.39 "Reading the transmit descriptor head to
   determine which buffers have been used (and can be returned to the memory pool)
   is not reliable".
   --> need to read DD field ("descriptor done") in RDESC.STATUS field and
       DD field in TDESC.STATUS field.
   3.3.3: The DD bit reflects status of all descriptors up to and including the one with
          the RS bit set (or RPS for the 82544GC/EI).
     (so software can decide to only set the RS (report status) bit for certain
      descriptors and only check the DD bit of those)
   So the status field needs to be written by the NIC and concurrently be read by software,
   so we can't strictly assign this piece of memory to either NIC or software! *)

  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Axiom TODO: False.

  Lemma weaken_e1000_step: forall t mGive action args post1 post2,
      e1000_step t mGive action args post1 ->
      (forall mReceive rets, post1 mReceive rets -> post2 mReceive rets) ->
      e1000_step t mGive action args post2.
  Proof.
  Admitted.

  Global Instance e1000_step_ok: ext_spec.ok e1000_step.
  Proof.
    constructor.
    - unfold e1000_step. intros * HSplit1 HSplit2 HStep1 HStep2.
      destruct HStep1 as (mNIC1 & (Own1 & HStep1)).
      destruct HStep2 as (mNIC2 & (Own2 & HStep2)).
      pose proof (externally_owned_mem_unique _ _ _ Own1 Own2).
      subst mNIC2. rename mNIC1 into mNIC. clear Own2. rename Own1 into Own.
      destruct HStep1 as [HStep1 | HStep1];
      destruct HStep2 as [HStep2 | HStep2].
      + fwd. reflexivity.
      + fwd. case TODO.
      + fwd. case TODO.
      + case TODO.
    - unfold Morphisms.Proper, Morphisms.respectful, Morphisms.pointwise_relation,
        Basics.impl.
      intros.
      eapply weaken_e1000_step. 1: eassumption. assumption.
    - (* intersect *)
      case TODO.
  Qed.

  (* getters in non-CPS (direct) style *)

  Definition getRDH(t: trace)(ret: word): Prop :=
    get_rw_reg0 t (register_address E1000_RDH) = Some ret.

  Definition getTDH(t: trace)(ret: word): Prop :=
    get_rw_reg0 t (register_address E1000_TDH) = Some ret.

  Definition getRDBAL(t: trace)(ret: word): Prop :=
    exists rdbal, get_rw_reg0 t (register_address E1000_RDBAL) = Some rdbal /\
    ret = /[Z.land (Z.lnot 0xf) \[rdbal]].

  Definition getRDBAH(t: trace)(ret: word): Prop. Admitted.

  Definition getRDBA(t: trace)(ret: word): Prop. Admitted. (*
    let/c rdbal := getRDBAL t in
    let/c rdbah := getRDBAH t in
    exists rdba, \[rdba] = \[rdbal] + \[rdbah] * 2^32 /\ ret rdba. *)

  Definition getTDBAL(t: trace)(ret: word): Prop. Admitted. (*
    let/c tdbal := getrw_reg E1000_TDBAL t in
    ret /[Z.land (Z.lnot 0xf) \[tdbal]].*)

  Definition getTDBAH(t: trace)(ret: word): Prop. Admitted.

  Definition getTDBA(t: trace)(ret: word): Prop. Admitted. (*
    let/c tdbal := getTDBAL t in
    let/c tdbah := getTDBAH t in
    exists tdba, \[tdba] = \[tdbal] + \[tdbah] * 2^32 /\ ret tdba. *)

  Definition get_receive_queue_cap(t: trace)(ret: Z): Prop. Admitted. (* :=
    let/c rdlen := getdescriptor_length E1000_RDLEN t in
    exists n, n * 16 = \[rdlen] /\ ret n.*)

  Definition get_transmit_queue_cap(t: trace)(ret: Z): Prop. Admitted. (*
    let/c tdlen := getdescriptor_length E1000_TDLEN t in
    exists n, n * 16 = \[tdlen] /\ ret n.*)

  (* Size of the receive buffers. If a packet doesn't fit, it is split into multiple
     buffers, using multiple descriptors.
     If RCTL.BSEX = 0b: 00b =   2048 B, 01b =  1024 B, 10b =  512 B, 11b =  256 B.
     If RCTL.BSEX = 1b: 00b = Reserved, 01b = 16384 B, 10b = 8192 B, 11b = 4096 B. *)
  Definition get_receive_buf_size(t: trace)(ret: Z): Prop :=
    exists rctl, get_rw_reg0 t (register_address E1000_RCTL) = Some rctl /\
    let bsex := Z.testbit \[rctl] RCTL.BSEX in
    let bsize := bitSlice \[rctl] RCTL.BSIZE_start RCTL.BSIZE_pastend in
    if bsex then
      match bsize with
      | 1 => ret = 16384
      | 2 => ret = 8192
      | 3 => ret = 4096
      | _ => False
      end
    else
      match bsize with
      | 0 => ret = 2048
      | 1 => ret = 1024
      | 2 => ret = 512
      | 3 => ret = 256
      | _ => False
      end.

  Context {locals: map.map String.string word}.

  Local Open Scope string_scope.

  (* read RDH: new RDH can be anywhere between old RDH (incl) and old RDT (excl),
     we receive the memory chunk for each descriptor between old and new RDH,
     as well as the buffers pointed to by them, which contain newly received packets *)
  Lemma wp_read_RDH: forall e mNIC rdh tdh old_rx_descs rx_queue_cap tx_queue_cap
                            rdba tdba rx_buf_size t m l r post
                            rxq txq rx_bufs tx_bufs,
      externally_owned_mem t mNIC ->
      (* begin NIC invariant, TODO factor out *)
      getRDBA t rdba ->
      getRDH t rdh ->
      get_receive_queue_cap t rx_queue_cap ->
      get_receive_buf_size t rx_buf_size ->
      getTDBA t tdba ->
      getTDH t tdh ->
      get_transmit_queue_cap t tx_queue_cap ->
      let rx_buf_addrs := List.map (fun d => /[d.(rx_desc_addr)]) rxq in
      let tx_buf_addrs := List.map (fun d => /[d.(tx_desc_addr)]) txq in
      <{ (* receive-related: *)
          * circular_buffer_slice rx_desc rx_queue_cap \[rdh] rxq rdba
          * scattered_array (array (uint 8) rx_buf_size) rx_bufs rx_buf_addrs
          (* transmit-related: *)
          * circular_buffer_slice tx_desc tx_queue_cap \[tdh] txq tdba
          * layout_absolute (List.map (fun pkt => array' (uint 8) pkt) tx_bufs) tx_buf_addrs
        }> mNIC ->
      (* end of NIC invariant *)
      (forall (m' mRcv: mem) (packets: list buf),
          map.split m' mRcv m ->
          len packets <= len rxq ->
          let new_RDH := /[(\[rdh] + len packets) mod rx_queue_cap] in
          (* we get back a (wrapping) slice of the rx queue as well as the corresponding
             buffers *)
          <{ * circular_buffer_slice rx_desc rx_queue_cap \[rdh]
                                     old_rx_descs[:len packets] rdba
             * scattered_array (array (uint 8) rx_buf_size) packets
                   (List.map (fun d => /[d.(rx_desc_addr)]) (old_rx_descs[:len packets]))
          }> mRcv ->
          post (cons ((map.empty, "MMIOREAD", [| register_address E1000_RDH |]),
                      (mRcv, [|new_RDH|])) t)
               m' (map.put l r new_RDH)) ->
      exec e (cmd.interact [|r|] "MMIOREAD" [|expr.literal \[register_address E1000_RDH]|])
           t m l post.
  Proof.
    intros.
    eapply exec.interact_cps.
    2: {
      cbn [eval_call_args eval_expr]. rewrite word.of_Z_unsigned. reflexivity.
    }
    2: {
      unfold e1000_step.
      eexists. split. 1: eassumption. right.
      cbn [dispatch String.eqb].
      rewrite (word.eqb_eq _ _ (eq_refl (register_address E1000_RDH))).
      cbn [read].
      (* looks promising, but still need to determine ?mGive and ?mKeep,
         and need to consolidate cps vs non-cps style *)
  Abort.

End WithMem.
