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
Require Import coqutil.Map.Interface coqutil.Word.Interface coqutil.Word.Bitwidth.
Require coqutil.Map.SortedListZ.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.StateMachineBasedExtSpec.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Require Import bedrock2.SepLib.
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
Record rx_desc := {
  (* 64 bits *) rx_desc_addr: Z; (* address of buffer to write to *)
  (* 16 bits *) rx_desc_length: Z; (* length of packet received *)
  (* 16 bits *) rx_desc_csum: Z; (* checksum *)
  (*  8 bits *) rx_desc_status: Z;
  (*  8 bits *) rx_desc_errors: Z;
  (* 16 bits *) rx_desc_special: Z;
}.

(* Transmit Descriptors (Section 3.3.3) *)
Record tx_desc := {
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

Definition z_to_buf_map: map.map Z (list Byte.byte) := SortedListZ.map (list Byte.byte).

Record e1000_state := {
  rx_queue_base_addr: Z; (* RDBAL/RDBAH, 64-bit total *)
  tx_queue_base_addr: Z; (* TDBAL/TDBAH, 64-bit *)
  rx_queue_capacity: Z; (* RDLEN / 16 *)
  tx_queue_capacity: Z; (* TDLEN / 16 *)
  rx_queue_head: Z; (* RDH *)
  rx_queue_tail: Z; (* RDT *)
  tx_queue_head: Z; (* TDH *)
  tx_queue_tail: Z; (* TDT *)
  rx_queue: list rx_desc;
  tx_queue: list tx_desc;
  (* We keep track of tx buffers because these remain unchanged when handed back to
     software. Its keys are Z because the spec says that buffer addresses are always
     64-bit addresses, even if the processor is 32-bit, and we use "word" only for
     "word of bitwidth of processor". *)
  tx_bufs: z_to_buf_map;
}.

Definition is_initial_e1000_state(s: e1000_state) :=
  (* we don't know anything about the initial values of the registers, but we know
     that it initially does not own any memory *)
  s.(rx_queue) = nil /\ s.(tx_queue) = nil /\ s.(tx_bufs) = map.empty.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.

  Definition rx_desc_t(r: rx_desc): word -> mem -> Prop := .**/
    typedef struct __attribute__ ((__packed__)) {
      uint64_t rx_desc_addr;
      uint16_t rx_desc_length;
      uint16_t rx_desc_csum;
      uint8_t rx_desc_status;
      uint8_t rx_desc_errors;
      uint16_t rx_desc_special;
    } rx_desc_t;
  /**.

  Definition tx_desc_t(r: tx_desc): word -> mem -> Prop := .**/
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

(* Operations:

- receive-related:
  + read RDH: new RDH can be anywhere between old RDH (incl) and RDT (excl),
    we receive the memory chunk for each descriptor between old and new RDH,
    as well as the buffers pointed to by them, which contain newly received packets
  + write RDT: software may set new RDT to anywhere between old RDT (incl) and
    RDH (excl, because otherwise queue considered empty), and by doing so, abandons
    the memory chunks corresponding to these descriptors and the buffers pointed to
    by them, thus providing more space for hardware to store received packets
- transmit-related:
  + read TDH: new TDH can be anywhere between old TDH (incl) and TDT (excl),
    increased TDH means some packets were sent, and we get back the memory chunk
    for each descriptor between old and new TDH, as well as the buffers pointed to
    by them, so we can start reusing these descriptors & buffers for new packets
  + write TDT: software may set new TDT to anywhere between old TDT (incl) and
    TDH (excl, because otherwise queue considered empty), and by doing so, indicates
    that between old and new TDT, there are new packets to be sent, and yields
    the descriptor chunks and the buffers pointed to by them to hardware
*)

  Definition read_RDH(s: e1000_state)(post: word -> e1000_state -> Prop): Prop :=
    False. (* TODO add is mGive and mReceive *)

  Definition e1000_step:
    e1000_state ->
    ((mem * String.string * list word) * (mem * list word)) ->
    e1000_state ->
    Prop :=
    fun s '((mGive, action, args), (mReceive, rets)) s' =>
      if String.eqb action "MMIOREAD"%string then
        match args with
        | cons addr nil =>
            if \[addr] =? E1000_RDH then False
            else False
        | _ => False
        end
      else if String.eqb action "MMIOWRITE" then
        match args with
        | cons addr (cons value nil) =>
            if \[addr] =? E1000_RDT then False
            else False
        | _ => False
        end
      else False.

  Global Instance ext_spec: ExtSpec :=
    StateMachineBasedExtSpec.ext_spec is_initial_e1000_state e1000_step.

  Global Instance ext_spec_ok: ext_spec.ok ext_spec.
  Proof.
    apply StateMachineBasedExtSpec.ext_spec_ok.
    unfold e1000_step. intros.
  Admitted.

  Import List.ListNotations.
  Context {locals: map.map String.string word}.

  (* read RDH: new RDH can be anywhere between old RDH (incl) and RDT (excl),
     we receive the memory chunk for each descriptor between old and new RDH,
     as well as the buffers pointed to by them, which contain newly received packets *)
  Lemma wp_read_RDH: forall e t m l r post,

      exec e (cmd.interact [r] "MMIOREAD" [expr.literal E1000_RDH]) t m l post.
  Proof.
    intros.
    eapply exec.interact.
  Abort.

End WithMem.
