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
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require coqutil.Map.SortedListZ.
Require Import coqutil.Datatypes.ZList.
Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
Require Import coqutil.Datatypes.RecordSetters. Import DoubleBraceUpdate.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.
Require Import bedrock2.PurifySep.
Require Import bedrock2.SepBulletPoints.
Require Import bedrock2.SepappBulletPoints. Local Open Scope sepapp_bullets_scope.
Require Import bedrock2.RecordPredicates.

(* Not part of the spec, but a convention we chose to hardcode here: *)
Definition E1000_REGS := 0x40000000.

Local Notation R x := (E1000_REGS + x) (only parsing).

(* E1000 register offsets from Section 13.4 *)
Definition E1000_RDBAL := R 0x2800. (* base addr (lo 32 bits) of receive descriptor queue *)
Definition E1000_RDBAH := R 0x2804. (* base addr (hi 32 bits) of receive descriptor queue *)
Definition E1000_RDLEN := R 0x2808. (* length of receive descriptor queue in bytes *)
Definition E1000_RDH := R 0x2810. (* receive descriptor queue head *)
Definition E1000_RDT := R 0x2818. (* receive descriptor queue tail *)
Definition E1000_TDBAL := R 0x3800. (* base addr (lo 32 bits) of transmit descriptor queue *)
Definition E1000_TDBAH := R 0x3804. (* base addr (hi 32 bits) of transmit descriptor queue *)
Definition E1000_TDLEN := R 0x3808. (* length of transmit descriptor queue in bytes *)
Definition E1000_TDH := R 0x3810. (* transmit descriptor queue head *)
Definition E1000_TDT := R 0x3818. (* transmit descriptor queue tail *)

(* Receive Descriptors (Section 3.2.3) *)
Record rx_desc_t: Set := {
  (* 64 bits *) rx_desc_addr: Z; (* address of buffer to write to *)
  (* 16 bits *) rx_desc_length: Z; (* length of packet received *)
  (* 16 bits *) rx_desc_csum: Z; (* checksum *)
  (*  8 bits *) rx_desc_status: Z;
  (*  8 bits *) rx_desc_errors: Z;
  (* 16 bits *) rx_desc_special: Z;
}.

(* Transmit Descriptors (Section 3.3.3) *)
Record tx_desc_t: Set := {
  (* 64 bits *) tx_desc_addr: Z; (* address of buffer to read from *)
  (* 16 bits *) tx_desc_length: Z; (* length of packet to be sent *)
  (*  8 bits *) tx_desc_cso: Z; (* checksum offset: where to insert checksum (if enabled) *)
  (*  8 bits *) tx_desc_cmd: Z; (* command bitfield *)
  (*  8 bits *) tx_desc_status: Z;
  (*  8 bits *) tx_desc_css: Z; (* checksum start: where to begin computing checksum *)
  (* 16 bits *) tx_desc_special: Z;
}.

(* The Receive Queue

   The queue between head (RDH) and tail (RDT) is a queue of descriptors
   pointing to buffers that software has provided to hardware, and
   the buffers in this queue are waiting to be filled by hardware.
   Hardware pushes new packets at head and increases head.
   If head reaches tail, it means there's no more space for new
   packets, so hardware starts discarding packets.
   Software adds new receive descriptors by setting the tail pointer to
   one beyond the last valid descriptor that is ready to be filled.
   Note from Section 3.2.6:
   > HARDWARE OWNS ALL DESCRIPTORS BETWEEN [HEAD AND TAIL]. Any descriptor
   > not in this range is owned by software.


   The Transmit Queue

   The queue between head (TDH) and tail (TDT) is a queue of descriptors
   pointing to buffers that software has provided to hardware and that
   hardware is supposed to sent over the network.
   Hardware sends the packets at head and increases head.
   Software adds new transmit descriptors at tail and increases tail, but
   must stop before tail equals head, because that is interpreted as an
   empty queue, not a full queue.
   From Section 3.4:
   > Descriptors passed to hardware should not be manipulated by software
   > until the head pointer has advanced past them.
*)

(* Note: The Ethernet card treats memory as little-endian (see Section 2.4), and so does
   RISC-V, but most network protocols encode multi-byte fields in big-endian order, but
   this file is not about protocols, so everything in the current file is little-endian. *)

Definition buf := list Z. (* Zs representing bytes *)

Definition z_to_buf_map: map.map Z buf := SortedListZ.map buf.

Record e1000_config: Set := {
  rx_queue_base_addr: option Z; (* RDBAL/RDBAH, 64-bit total, None means uninitialized *)
  tx_queue_base_addr: option Z; (* TDBAL/TDBAH, same *)
  rx_queue_capacity: Z; (* RDLEN / 16 *)
  tx_queue_capacity: Z; (* TDLEN / 16 *)
  (* Size of the receive buffers. If a packet doesn't fit, it is split into multiple
     buffers, using multiple descriptors.
     Hardware supports the following receive buffer sizes:
     256 B, 512 B, 1024 B, 2048 B, 4096 B, 8192 B, 16384 B (Section 3.2.2).
     The buffer size is controlled using RCTL.BSIZE and RCTL.BSEX (Section 13.4.22). *)
  rx_buf_size: Z;
}.
(* rx/tx_queue_base_addr: Why we use option Z instead of just leaving the Z unspecified in
   is_initial_e1000_state: We want mGive to be unique given a trace and extcall args, but
   the rx/tx queue base addresses are not unique (because initial value is unspecified),
   (but the heads and tails are), so given a trace and a list of extcall arguments,
   the given-away memory is not uniquely determined, because the heads and tails are
   relative to the potentially-undefined base address.
   So if the base address is unspecified, we need to reject all steps that would give
   up memory, so we need to use an option for the base address... *)

Record e1000_state := {
  get_e1000_config :> e1000_config;
  rx_queue: list rx_desc_t;
  tx_queue: list tx_desc_t;
  rx_queue_head: Z; (* RDH *)
  tx_queue_head: Z; (* TDH *)
  (* We keep track of tx buffers because these remain unchanged when handed back to
     software. Its keys are Z because the spec says that buffer addresses are always
     64-bit addresses, even if the processor is 32-bit, and we use "word" only for
     "word of bitwidth of processor". *)
  tx_bufs: z_to_buf_map;
}.

Definition rx_queue_tail(s: e1000_state): Z := (* RDT *)
  (s.(rx_queue_head) + len s.(rx_queue)) mod s.(rx_queue_capacity).

Definition tx_queue_tail(s: e1000_state): Z := (* TDT *)
  (s.(tx_queue_head) + len s.(tx_queue)) mod s.(tx_queue_capacity).

Record e1000_ok(cfg: e1000_config)(s: e1000_state): Prop := {
  config_matches: s.(get_e1000_config) = cfg;
  RDH_bounded: 0 <= s.(rx_queue_head) < cfg.(rx_queue_capacity);
  TDH_bounded: 0 <= s.(tx_queue_head) < cfg.(tx_queue_capacity);
  rx_queue_bounded: len s.(rx_queue) <= cfg.(rx_queue_capacity);
  tx_queue_bounded: len s.(tx_queue) <= cfg.(tx_queue_capacity);
  tx_bufs_present: forall txd, List.In txd s.(tx_queue) ->
                   exists bs, map.get s.(tx_bufs) txd.(tx_desc_addr) = Some bs /\
                              len bs = txd.(tx_desc_length);
}.

Definition is_initial_e1000_state(s: e1000_state) :=
  (* initially, the network card does not own any memory *)
  s.(rx_queue) = nil /\ s.(tx_queue) = nil /\ s.(tx_bufs) = map.empty /\
  (* some registers (eg RDBAL/RDBAH, TDBAL/TDBAH have an initial value of X (undefined),*)
  s.(rx_queue_base_addr) = None /\ s.(tx_queue_base_addr) = None /\
  (* while others are specified to have an initial value of 0 (see Section 13) *)
  s.(rx_queue_capacity) = 0 /\ s.(tx_queue_capacity) = 0 /\
  s.(rx_buf_size) = 2048 /\ (* <- meaning of RCTL.BSIZE=0 /\ RCTL.BSEX=0 *)
  s.(rx_queue_head) = 0 /\ s.(tx_queue_head) = 0.

Definition agree_on_unique_state_fields(s1 s2: e1000_state) :=
  s1.(rx_queue_base_addr) = s2.(rx_queue_base_addr) /\
  s1.(tx_queue_base_addr) = s2.(tx_queue_base_addr) /\
  s1.(rx_queue_capacity) = s2.(rx_queue_capacity) /\
  s1.(tx_queue_capacity) = s2.(tx_queue_capacity) /\
  s1.(rx_buf_size) = s2.(rx_buf_size) /\
  s1.(rx_queue) = s2.(rx_queue) /\
  s1.(tx_queue) = s2.(tx_queue) /\
  s1.(rx_queue_head) = s2.(rx_queue_head) /\
  s1.(tx_queue_head) = s2.(tx_queue_head).

Lemma initial_states_agree_on_unique_state_fields: forall s1 s2,
    is_initial_e1000_state s1 ->
    is_initial_e1000_state s2 ->
    agree_on_unique_state_fields s1 s2.
Proof.
  unfold is_initial_e1000_state, agree_on_unique_state_fields.
  intros. destruct s1 as [ [ ] ]; destruct s2 as [ [ ] ]; cbn -[map.empty] in *.
  fwd. auto 10.
Qed.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.

  (* TODO move? *)
  Section WithElem.
    Context {E: Type}.

    (* The address a passed to this predicate is the base address. The area
       occupied by the whole buffer is a..a+modulus*sz, but there might actually
       be nothing at a, since the slice starts at a+startIndex*sz. *)
    Definition circular_buffer_slice(elem: E -> word -> mem -> Prop)
      {sz: PredicateSize elem}(modulus startIndex: Z)(vs: list E): word -> mem -> Prop :=
      <{ + emp_at_addr (len vs <= modulus /\ 0 <= startIndex < modulus)
         + array elem (Z.max 0 (len vs - (modulus - startIndex))) vs[modulus-startIndex:]
         + hole (modulus - len vs)
         + array elem (Z.min (len vs) (modulus - startIndex)) vs[:modulus-startIndex] }>.

    Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

    Lemma purify_circular_buffer_slice(elem: E -> word -> mem -> Prop)
      {sz: PredicateSize elem}(modulus startIndex: Z)(vs: list E)(addr: word):
      purify (circular_buffer_slice elem modulus startIndex vs addr)
             (len vs <= modulus /\ 0 <= startIndex < modulus).
    Proof.
      unfold purify, circular_buffer_slice. intros.
      cbn in H. unfold sepapp, emp_at_addr in H. eapply sep_emp_l in H. apply H.
    Qed.

    (* given a goal of the form (iff1 LHS RHS), where LHS and RHS only consist
     of sep and emp, turns it into purely propositional goals *)
    Ltac de_emp :=
      intro m'; split; intros Hm;
      rewrite ?sep_assoc_eq in Hm;
      rewrite ?sep_assoc_eq;
      repeat match goal with
        | H: sep (emp _) _ _ |- _ => eapply sep_emp_l in H; destruct H
        | H: emp _ _ |- _ => destruct H
        end;
      subst;
      repeat match goal with
        | |- sep (emp _) _ _ => eapply sep_emp_l
        | |- _ /\ _ => split
        | |- emp _ map.empty => refine (conj eq_refl _)
        | |- True => constructor
        end.

    Lemma circular_buffer_slice_nil elem {sz: PredicateSize elem} modulus startIndex a:
      emp (0 <= startIndex < modulus) =
        (circular_buffer_slice elem modulus startIndex nil a).
    Proof.
      eapply iff1ToEq.
      unfold circular_buffer_slice. cbn.
      unfold List.upto, List.from. rewrite List.skipn_nil, List.firstn_nil.
      unfold sepapp, array, hole, emp_at_addr.
      do 2 replace (Array.array _ _ _ _) with (@emp _ _ mem True)
        by (symmetry; eapply iff1ToEq; eapply Array.array_nil).
      rewrite ?sep_assoc_eq.
      cbn.
      de_emp.
      all: try Lia.lia.
    Qed.

    Lemma circular_buffer_slice_nil_empty elem {sz: PredicateSize elem} modulus startIndex a:
      0 <= startIndex < modulus ->
      circular_buffer_slice elem modulus startIndex nil a map.empty.
    Proof.
      intros. rewrite <- circular_buffer_slice_nil. unfold emp. split.
      1: reflexivity. Lia.lia.
    Qed.
  End WithElem.

  Definition rx_desc(r: rx_desc_t): word -> mem -> Prop := .**/
    typedef struct __attribute__ ((__packed__)) {
      uint64_t rx_desc_addr;
      uint16_t rx_desc_length;
      uint16_t rx_desc_csum;
      uint8_t rx_desc_status;
      uint8_t rx_desc_errors;
      uint16_t rx_desc_special;
    } rx_desc_t;
  /**.

  (* A receive descriptor together with the buffer it points to *)
  (* Note: buf_len is the total allocated amount and usually bigger than
     rx_desc_length, which is the actual length of the received packet *)
  Definition rxq_elem(buf_len: Z)(v: rx_desc_t * buf)(addr: word): mem -> Prop :=
    sep (rx_desc (fst v) addr)
        (array (uint 8) buf_len (snd v) /[rx_desc_addr (fst v)]).

  Definition tx_desc(r: tx_desc_t): word -> mem -> Prop := .**/
    typedef struct __attribute__ ((__packed__)) {
      uint64_t tx_desc_addr;
      uint16_t tx_desc_length;
      uint8_t tx_desc_cso;
      uint8_t tx_desc_cmd;
      uint8_t tx_desc_status;
      uint8_t tx_desc_css;
      uint16_t tx_desc_special;
    } tx_desc_t;
  /**.

  (* A transmit descriptor together with the buffer it points to *)
  (* Note: length of buffer is given by tx_desc_length field *)
  Definition txq_elem(v: tx_desc_t * buf)(addr: word): mem -> Prop :=
    sep (tx_desc (fst v) addr)
        (array (uint 8) (tx_desc_length (fst v)) (snd v) /[tx_desc_addr (fst v)]).

End WithMem.

(* For the purpose of laying out rx/tx queue elements contiguously in memory,
   only the size of the first part (the descriptor) matters: *)
#[export] Hint Extern 1 (PredicateSize (rxq_elem _)) => exact (sizeof rx_desc)
  : typeclass_instances.
#[export] Hint Extern 1 (PredicateSize txq_elem) => exact (sizeof tx_desc)
  : typeclass_instances.

#[export] Hint Resolve purify_circular_buffer_slice : purify.
