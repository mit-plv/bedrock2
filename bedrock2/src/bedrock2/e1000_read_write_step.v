(*
Formalization of a subset of the functionality of Intel's 8254x Network Interface Cards.

PDF Spec:

PCI/PCI-X Family of Gigabit Ethernet Controllers Software Developer's Manual
82540EP/EM, 82541xx, 82544GC/EI, 82545GM/EM, 82546GB/EB, and 82547xx
https://www.intel.com/content/dam/doc/manual/pci-pci-x-family-gbe-controllers-software-dev-manual.pdf

These network cards were launched in the 2000s and discontinued in the 2010s, but continue to be a popular choice for virtualization, and are often referred to as "e1000".
 *)

From Coq Require Import String.
From Coq Require Import ZArith.
From Coq Require Import Lia.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Datatypes.HList coqutil.Byte.
Require Import coqutil.Z.BitOps.
Require coqutil.Map.SortedListZ.
Require Import coqutil.Datatypes.ZList.
Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
Require Import coqutil.Datatypes.RecordSetters. Import DoubleBraceUpdate.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.
Require Import bedrock2.SepBulletPoints. Local Open Scope sep_bullets_scope.
Require Import bedrock2.RecordPredicates.
Require Import bedrock2.TraceInspection.
Require Import bedrock2.memory_mapped_ext_spec.
Require Import bedrock2.e1000_state. (* for rx/tx_desc and separation logic definitions *)

Definition E1000_MMIO_SPACE_SIZE := 0x20000. (* 128 KB, Section 13.1 *)

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

  (* TODO some registers are safe to get using `get_rw_reg REG_NAME`, whereas others
     have "ignore on write" semantics and thus need a special get_rw_REGNAME.
     How can we enforce one never forgets to use the special getter if there is one? *)

  Definition getRDH(t: trace)(ret: Z): Prop :=
    exists r, get_rw_reg0 t (register_address E1000_RDH) = Some r /\ \[r] = ret.

  Definition getTDH(t: trace)(ret: Z): Prop :=
    exists r, get_rw_reg0 t (register_address E1000_TDH) = Some r /\ \[r] = ret.

  Definition getRDT(t: trace)(ret: Z): Prop :=
    exists r, get_rw_reg0 t (register_address E1000_RDT) = Some r /\ \[r] = ret.

  Definition getTDT(t: trace)(ret: Z): Prop :=
    exists r, get_rw_reg0 t (register_address E1000_TDT) = Some r /\ \[r] = ret.

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

  (* This are just the registers, and do not include the owned memory or the queues *)
  Record initialized_e1000_state := {
    rx_queue_base_addr: word; (* RDBAL/RDBAH, 64 bits total, but need to fit into a word *)
    tx_queue_base_addr: word; (* TDBAL/TDBAH, 64 bits total, but need to fit into a word *)
    rx_queue_cap: Z; (* RDLEN / 16 *)
    tx_queue_cap: Z; (* TDLEN / 16 *)
    (* Size of the receive buffers. If a packet doesn't fit, it is split into multiple
       buffers, using multiple descriptors.
       Hardware supports the following receive buffer sizes:
       256 B, 512 B, 1024 B, 2048 B, 4096 B, 8192 B, 16384 B (Section 3.2.2).
       The buffer size is controlled using RCTL.BSIZE and RCTL.BSEX (Section 13.4.22). *)
    rx_buf_size: Z;
    rx_queue_head: Z; (* RDH *)
    tx_queue_head: Z; (* TDH *)
  }.

  Definition e1000_initialized(s: initialized_e1000_state)(t: trace): Prop :=
    getRDBA t s.(rx_queue_base_addr) /\
    getTDBA t s.(tx_queue_base_addr) /\
    get_receive_queue_cap t s.(rx_queue_cap) /\
    get_transmit_queue_cap t s.(tx_queue_cap) /\
    get_receive_buf_size t s.(rx_buf_size) /\
    getRDH t s.(rx_queue_head) /\
    getTDH t s.(tx_queue_head).

  Lemma e1000_initialized_unique: forall [s1 s2 t],
      e1000_initialized s1 t ->
      e1000_initialized s2 t ->
      s1 = s2.
  Proof.
    unfold e1000_initialized.
    intros. fwd.
    destruct s1. destruct s2. cbn in *.
    f_equal.
  Admitted.

  (* Potential notations for (circular_buffer_slice elem n i vs addr):
     * addr |-(->i, mod n)-> vs
     * addr [⇥i ⟳n]-> vs
     * addr [shift i, mod size]-> vs
     * vs @[+i, mod n] addr  *)

  Definition e1000_invariant(s: initialized_e1000_state)
    (rxq: list (rx_desc_t * buf))(txq: list (tx_desc_t * buf)): mem -> Prop :=
    <{ * circular_buffer_slice (rxq_elem s.(rx_buf_size))
           s.(rx_queue_cap) s.(rx_queue_head) rxq s.(rx_queue_base_addr)
       * circular_buffer_slice txq_elem
           s.(tx_queue_cap) s.(tx_queue_head) txq s.(tx_queue_base_addr) }>.

  Lemma rxq_txq_unique: forall [s rxq1 rxq2 txq1 txq2 m],
      e1000_invariant s rxq1 txq1 m ->
      e1000_invariant s rxq2 txq2 m ->
      rxq1 = rxq2 /\ txq1 = txq2.
  Admitted.

  (* not using an Inductive because:
     - some parts are shared between the different cases
     - inversion creates existT equalities on dependently-typed postconditions *)
  Definition e1000_read_step
    (sz: nat) (* number of bytes to read *)
    (t: trace) (* trace of events that happened so far *)
    (addr: word) (* address to be read *)
    (post: tuple byte sz -> mem -> Prop): (* postcondition on returned value and memory *)
    Prop :=
    sz = 4%nat /\
    exists s mNIC rxq txq,
      externally_owned_mem t mNIC /\
      e1000_initialized s t /\
      e1000_invariant s rxq txq mNIC /\
      ((addr = register_address E1000_RDH /\
       (* Hardware gives newly received packets to software:
          New RDH can be anywhere between old RDH (incl) and old RDT (excl),
          we receive the memory chunk for each descriptor between old and new RDH,
          as well as the buffers pointed to by them, which contain newly received
          packets *)
        forall mRcv (done: list (rx_desc_t * buf)),
          len done <= len rxq ->
          List.map fst done = List.map fst rxq[:len done] ->
          (* snd (new buffer) can be any bytes *)
          circular_buffer_slice (rxq_elem s.(rx_buf_size))
            s.(rx_queue_cap) s.(rx_queue_head) done s.(rx_queue_base_addr) mRcv ->
          post (LittleEndian.split sz ((s.(rx_queue_head) + len done)
                                        mod s.(rx_queue_cap))) mRcv)
       \/
      (addr = register_address E1000_TDH /\
      (* Hardware gives back transmitted buffers to software:
         New TDH can be anywhere between old TDH (incl) and TDT (excl),
         increased TDH means some packets were sent, and we get back the memory chunk
         for each descriptor between old and new TDH, as well as the buffers pointed to
         by them, so we can start reusing these descriptors & buffers for new packets *)
       forall mRcv nDone,
          0 <= nDone <= len txq ->
          circular_buffer_slice txq_elem
            s.(tx_queue_cap) s.(tx_queue_head) txq[:nDone] s.(tx_queue_base_addr) mRcv ->
          post (LittleEndian.split sz ((s.(tx_queue_head) + nDone)
                                        mod s.(tx_queue_cap))) mRcv)).

  Definition e1000_write_step
    (sz: nat) (* number of bytes to write *)
    (t: trace) (* trace of events that happened so far *)
    (addr: word) (* address to be written *)
    (val: tuple byte sz) (* value to be written *)
    (mGive: mem): (* memory whose ownership is passed to the external world *)
    Prop :=
    sz = 4%nat /\
    exists s mNIC rxq txq,
      externally_owned_mem t mNIC /\
      e1000_initialized s t /\
      e1000_invariant s rxq txq mNIC /\
      ((addr = register_address E1000_RDT /\
       (* Software gives fresh empty buffers to hardware:
          Software may set new RDT to anywhere between old RDT (incl) and
          RDH (excl, because otherwise queue considered empty), and by doing so, abandons
          the memory chunks corresponding to these descriptors and the buffers pointed to
          by them, thus providing more space for hardware to store received packets *)
        exists (fresh: list (rx_desc_t * buf)),
          len rxq + len fresh < s.(rx_queue_cap) /\
          LittleEndian.combine sz val = (s.(rx_queue_head) + len rxq + len fresh)
                                         mod s.(rx_queue_cap) /\
          circular_buffer_slice (rxq_elem s.(rx_buf_size)) s.(rx_queue_cap)
                                   ((s.(rx_queue_head) + len rxq) mod s.(rx_queue_cap))
                                fresh s.(rx_queue_base_addr) mGive)
       \/
       (addr = register_address E1000_TDT /\
       (* Software gives buffers to be sent to hardware:
          Software may set new TDT to anywhere between old TDT (incl) and
          TDH (excl, because otherwise queue considered empty), and by doing so, indicates
          that between old and new TDT, there are new packets to be sent, and yields
          the descriptor chunks and the buffers pointed to by them to hardware *)
        exists (toSend: list (tx_desc_t * buf)),
          len txq + len toSend < s.(tx_queue_cap) /\
          LittleEndian.combine sz val = (s.(tx_queue_head) + len txq + len toSend)
                                         mod s.(tx_queue_cap) /\
          circular_buffer_slice txq_elem s.(tx_queue_cap)
              ((s.(tx_queue_head) + len txq) mod s.(tx_queue_cap))
              toSend s.(tx_queue_base_addr) mGive)).

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

  Global Instance e1000_MemoryMappedExtCalls: MemoryMappedExtCalls := {
    read_step := e1000_read_step;
    write_step := e1000_write_step;
    mmio_addrs a := E1000_REGS <= \[a] < E1000_REGS + E1000_MMIO_SPACE_SIZE;
  }.

  Axiom TODO: False.

  Ltac destruct_or :=
    lazymatch goal with
    | H: _ \/ _ |- _ => destruct H
    end.

  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Global Instance e1000_MemoryMappedExtCallsOk:
    MemoryMappedExtCallsOk e1000_MemoryMappedExtCalls.
  Proof.
    constructor;
    unfold read_step, write_step, mmio_addrs, e1000_MemoryMappedExtCalls,
      e1000_read_step, e1000_write_step; intros; fwd; subst n.
    - (* weaken_read_step *)
      destruct_or; fwd; eauto 15.
    - (* intersect_read_step *)
      lazymatch goal with
      | H1: externally_owned_mem _ ?m1, H2: externally_owned_mem _ ?m2 |- _ =>
          pose proof (externally_owned_mem_unique _ _ _ H1 H2); subst m1
      end.
      lazymatch goal with
      | H1: e1000_initialized ?s1 ?t, H2: e1000_initialized ?s2 ?t |- _ =>
          pose proof (e1000_initialized_unique H1 H2); subst s1
      end.
      lazymatch goal with
      | H1: e1000_invariant _ ?rxq1 ?txq1 _, H2: e1000_invariant _ ?rxq2 ?txq2 _ |- _ =>
          destruct (rxq_txq_unique H1 H2); subst rxq1 txq1
      end.
      do 2 destruct_or; fwd.
      2,3:
        exfalso;
        lazymatch goal with
        | H: register_address _ = register_address _ |- _ =>
            cbn in H;
            apply (f_equal word.unsigned) in H;
            rewrite !word.unsigned_of_Z_nowrap in H
                by (destruct width_cases as [W | W]; rewrite W in *; lia);
            discriminate H
        end.
      all: eauto 15.
    - (* read_step_nonempty *)
      unfold e1000_invariant in *.
      PurifySep.purify_hyp Hp1p2.
      destruct_or; fwd.
      all: specialize (Hp1 map.empty).
      1: specialize (Hp1 nil).
      2: specialize (Hp1 0).
      1: rewrite List.len_nil in Hp1.
      all: rewrite Z.add_0_r in Hp1.
      all: do 2 eexists; apply Hp1; try apply circular_buffer_slice_nil_empty;
        try reflexivity; try lia.
    - (* read_step_returns_owned_mem *)
      case TODO.
    - (* write_step_unique_mGive *)
      case TODO.
    - (* read_step_addrs_ok *)
      left.
      destruct_or; fwd; cbn;
        unfold PropSet.subset, PropSet.of_list, PropSet.elem_of, E1000_REGS;
        rewrite <- ?word.ring_morph_add;
        cbn; clear -word_ok BW; intros; repeat destruct_or; try contradiction; subst x;
        (rewrite word.unsigned_of_Z_nowrap; [lia | ]);
        destruct width_cases as [W | W]; rewrite W in *; lia.
    - (* write_step_addrs_ok *)
      left.
      destruct_or; fwd; cbn;
        unfold PropSet.subset, PropSet.of_list, PropSet.elem_of, E1000_REGS;
        rewrite <- ?word.ring_morph_add;
        cbn; clear -word_ok BW; intros; repeat destruct_or; try contradiction; subst x;
        (rewrite word.unsigned_of_Z_nowrap; [lia | ]);
        destruct width_cases as [W | W]; rewrite W in *; lia.
  Qed.

  Local Open Scope string_scope.

  Context {locals: map.map String.string word}.

  Local Open Scope string_scope.

  (* read RDH: new RDH can be anywhere between old RDH (incl) and old RDT (excl),
     we receive the memory chunk for each descriptor between old and new RDH,
     as well as the buffers pointed to by them, which contain newly received packets *)
  Lemma wp_read_RDH: forall e t m l s r mNIC rxq txq post,
      externally_owned_mem t mNIC ->
      e1000_initialized s t ->
      e1000_invariant s rxq txq mNIC ->
      (forall m' mRcv (done: list (rx_desc_t * buf)) new_RDH,
          (* need explicit mRcv because it appears in trace *)
          map.split m' m mRcv ->
          \[new_RDH] = (s.(rx_queue_head) + len done) mod s.(rx_queue_cap) ->
          len done <= len rxq ->
          List.map fst done = List.map fst rxq[:len done] ->
          (* snd (new buffer) can be any bytes *)
          circular_buffer_slice (rxq_elem s.(rx_buf_size))
            s.(rx_queue_cap) s.(rx_queue_head) done s.(rx_queue_base_addr) mRcv ->
          post (cons ((map.empty,
                       "memory_mapped_extcall_read32",
                       [| register_address E1000_RDH |]),
                      (mRcv, [|new_RDH|])) t)
               m' (map.put l r new_RDH)) ->
      exec e (cmd.interact [|r|] "memory_mapped_extcall_read32"
                [|expr.literal \[register_address E1000_RDH]|]) t m l post.
  Proof.
    intros.
    eapply exec.interact_cps with (mGive := map.empty).
    { eapply map.split_empty_r. reflexivity. }
    { cbn [eval_call_args eval_expr]. rewrite word.of_Z_unsigned. reflexivity. }
    { unfold ext_spec. exists 4%nat.
      split; [solve [clear; auto] | ]. left.
      split; [reflexivity | ].
      eexists.
      split; [reflexivity | ].
      split; [reflexivity | ].
      unfold read_step, e1000_MemoryMappedExtCalls, e1000_read_step.
      split; [reflexivity | ].
      exists s, mNIC, rxq, txq.
      do 3 (split; [assumption | ]).
      left.
      split; [reflexivity | ].
      intros mRcv done B F M.
      rewrite LittleEndian.combine_split. cbn [map.putmany_of_list_zip].
      change (Z.of_nat 4 * 8) with 32.
      eexists.
      split; [reflexivity | ].
      intros m' Sp.
      eapply H2.
      - exact Sp.
      - rewrite word.unsigned_of_Z_nowrap.
        + case TODO. (* bound rx_queue_cap *)
        + destruct width_cases as [W | W]; rewrite W;
            Z.to_euclidean_division_equations; lia.
      - eassumption.
      - assumption.
      - exact M. }
  Qed.

End WithMem.
