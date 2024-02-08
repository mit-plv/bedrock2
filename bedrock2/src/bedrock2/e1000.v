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
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth.
Require coqutil.Map.SortedListZ.
Require Import coqutil.Datatypes.ZList.
Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
Require Import coqutil.Datatypes.RecordSetters. Import DoubleBraceUpdate.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.StateMachineBasedExtSpec.
Require Import bedrock2.WordNotations. Local Open Scope word_scope.
Require Import bedrock2.Map.SeparationLogic.
Require Import bedrock2.SepLib.
Require Import bedrock2.SepBulletPoints.
Require Import bedrock2.RecordPredicates.

(* Consider a circular buffer of size `modulus` whose elements are indexed from
   `0` to `modulus-1`. Given a `candidate` and a (potentially-wrapping) interval from
   `start` (inclusive) to `past_end` (exclusive), is `candidate` inside that range?
   Note that `start=past_end` is treated as the empty interval, so it is not possible
   to express an interval that covers the whole buffer. *)
Definition in_circular_interval(modulus candidate start past_end: Z): Prop :=
  (candidate - start) mod modulus < (past_end - start) mod modulus.

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
Record rx_desc: Set := {
  (* 64 bits *) rx_desc_addr: Z; (* address of buffer to write to *)
  (* 16 bits *) rx_desc_length: Z; (* length of packet received *)
  (* 16 bits *) rx_desc_csum: Z; (* checksum *)
  (*  8 bits *) rx_desc_status: Z;
  (*  8 bits *) rx_desc_errors: Z;
  (* 16 bits *) rx_desc_special: Z;
}.

(* Transmit Descriptors (Section 3.3.3) *)
Record tx_desc: Set := {
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
  rx_queue_base_addr: Z; (* RDBAL/RDBAH, 64-bit total *)
  tx_queue_base_addr: Z; (* TDBAL/TDBAH, 64-bit *)
  rx_queue_capacity: Z; (* RDLEN / 16 *)
  tx_queue_capacity: Z; (* TDLEN / 16 *)
  (* Size of the receive buffers. If a packet doesn't fit, it is split into multiple
     buffers, using multiple descriptors.
     Hardware supports the following receive buffer sizes:
     256 B, 512 B, 1024 B, 2048 B, 4096 B, 8192 B, 16384 B (Section 3.2.2).
     The buffer size is controlled using RCTL.BSIZE and RCTL.BSEX (Section 13.4.22). *)
  rx_buf_size: Z;
}.

Record e1000_state := {
  get_e1000_config :> e1000_config;
  rx_queue: list rx_desc;
  tx_queue: list tx_desc;
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
  (* we don't know anything about the initial values of the registers, but we know
     that it initially does not own any memory *)
  s.(rx_queue) = nil /\ s.(tx_queue) = nil /\ s.(tx_bufs) = map.empty.

Section WithMem.
  Context {width: Z} {BW: Bitwidth width}
          {word: word.word width} {mem: map.map word Byte.byte}.

  (* TODO move,
     and maybe this could be used to define array and sepapps more conveniently? *)
  Section WithElem.
    Context {E: Type}.

    Definition layout_absolute(ps: list (word -> mem -> Prop))(addrs: list word) :=
      seps' (List.map (fun '(p, a) => p a) (List.combine ps addrs)).

    Definition layout_offsets(ps: list (word -> mem -> Prop))(offsets: list Z)(addr: word):
      mem -> Prop :=
      layout_absolute ps (List.map (fun ofs => word.add addr (word.of_Z ofs)) offsets).

    Definition scattered_array(elem: E -> word -> mem -> Prop)
                              (vs: list E)(addrs: list word): mem -> Prop :=
      layout_absolute (List.map elem vs) addrs.

    Definition array'(elem: E -> word -> mem -> Prop){sz: PredicateSize elem}
                     (vs: list E): word -> mem -> Prop :=
      layout_offsets (List.map elem vs)
             (List.map (fun i => sz * Z.of_nat i) (List.seq O (List.length vs))).

    (* starts with 0 and has same length as given list, so the last element sum
       excludes the last element *)
    Fixpoint prefix_sums_starting_at(s: Z)(l: list Z): list Z :=
      match l with
      | nil => nil
      | cons h t => cons (s + h) (prefix_sums_starting_at (s + h) t)
      end.
    Definition prefix_sums: list Z -> list Z := prefix_sums_starting_at 0.

    Definition sepapps'(l: list sized_predicate): word -> mem -> Prop :=
      layout_offsets (List.map proj_predicate l) (prefix_sums (List.map proj_size l)).

    Definition circular_interval(modulus start: Z)(count: nat): list Z :=
      List.unfoldn (fun x => (x + 1) mod modulus) count start.

    (* The address a passed to this predicate is the base address. The area
       occupied by the whole buffer is a..a+modulus*sz, but there might actually
       be nothing at a, since the slice starts at a+startIndex*sz. *)
    Definition circular_buffer_slice(elem: E -> word -> mem -> Prop)
      {sz: PredicateSize elem}(modulus startIndex: Z)(vs: list E): word -> mem -> Prop :=
      layout_offsets (List.map elem vs)
             (List.map (Z.mul sz) (circular_interval modulus startIndex (List.length vs))).
  End WithElem.

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

  Local Open Scope sep_bullets_scope.
  Local Open Scope string_scope.

  Inductive e1000_step: e1000_state -> LogItem -> e1000_state -> Prop :=
  (* read RDH: new RDH can be anywhere between old RDH (incl) and old RDT (excl),
     we receive the memory chunk for each descriptor between old and new RDH,
     as well as the buffers pointed to by them, which contain newly received packets *)
  | read_RDH_step: forall s mRcv new_RDH (packets: list buf),
      len packets <= len s.(rx_queue) ->
      \[new_RDH] = (s.(rx_queue_head) + len packets) mod s.(rx_queue_capacity) ->
      (* we get back a (wrapping) slice of the rx queue as well as the corresponding
         buffers *)
      <{ * circular_buffer_slice rx_desc_t s.(rx_queue_capacity) s.(rx_queue_head)
                                 s.(rx_queue)[:len packets] /[s.(rx_queue_base_addr)]
         * scattered_array (array (uint 8) s.(rx_buf_size)) packets
             (List.map (fun d => /[d.(rx_desc_addr)]) s.(rx_queue)[:len packets])
        }> mRcv ->
      e1000_step s ((map.empty, "MMIOREAD", [| /[E1000_RDH] |]), (mRcv, [|new_RDH|]))
        s{{ rx_queue := s.(rx_queue)[:len packets];
            rx_queue_head := (s.(rx_queue_head) + len packets) mod s.(rx_queue_capacity) }}
  (* write RDT: software may set new RDT to anywhere between old RDT (incl) and
     RDH (excl, because otherwise queue considered empty), and by doing so, abandons
     the memory chunks corresponding to these descriptors and the buffers pointed to
     by them, thus providing more space for hardware to store received packets *)
  | write_RDT_step: forall s mGive new_RDT new_descs (fillable: list buf),
      (* Note: strict < because otherwise we had head=tail which would be interpreted
         as an empty circular buffer *)
      len s.(rx_queue) + len fillable < s.(rx_queue_capacity) ->
      \[new_RDT] = (s.(rx_queue_head) + len s.(rx_queue) + len fillable)
                     mod s.(rx_queue_capacity) ->
      len fillable = len new_descs ->
      <{ * circular_buffer_slice rx_desc_t s.(rx_queue_capacity) s.(rx_queue_head)
                  (s.(rx_queue) ++ new_descs)%list /[s.(rx_queue_base_addr)]
         * scattered_array (array (uint 8) s.(rx_buf_size)) fillable
             (List.map (fun d => /[d.(rx_desc_addr)]) (s.(rx_queue) ++ new_descs)%list)
        }> mGive ->
      e1000_step s ((mGive, "MMIOWRITE", [| /[E1000_RDT]; new_RDT |]), (map.empty, nil))
        s{{ rx_queue := (s.(rx_queue) ++ new_descs)%list (* TODO *) }}
        (* no need to update rx_queue_tail because it is inferred from
           rx_queue_head and len rx_queue *)
  .

  Global Instance ext_spec: ExtSpec :=
    StateMachineBasedExtSpec.ext_spec is_initial_e1000_state e1000_step.

  Axiom TODO: False.

  Global Instance ext_spec_ok: ext_spec.ok ext_spec.
  Proof.
    apply StateMachineBasedExtSpec.ext_spec_ok.
    intros. inversion H3; subst; clear H3; inversion H4; subst; clear H4.
    - (* read_RDH_step *)
      reflexivity.
    - (* write_RDT_step *)
      lazymatch goal with
      | H: sep _ _ _ |- _ => destruct H as (mGive2a & mGive2b & D2 & M2a & M2b)
      end.
      lazymatch goal with
      | H: sep _ _ _ |- _ => destruct H as (mGive1a & mGive1b & D1 & M1a & M1b)
      end.
      (* uniqueness stuff: *)
      replace (rx_queue s2) with (rx_queue s1) in * by case TODO.
      replace (rx_queue_base_addr s2) with (rx_queue_base_addr s1) in * by case TODO.
      replace (rx_queue_capacity s2) with (rx_queue_capacity s1) in * by case TODO.
      replace (rx_buf_size s2) with (rx_buf_size s1) in * by case TODO.
      replace (rx_queue_head s2) with (rx_queue_head s1) in * by case TODO.
      rename fillable0 into fillable2, fillable into fillable1.
      rename new_descs0 into new_descs2, new_descs into new_descs1.
      assert (len fillable1 = len fillable2). {
        assert (
          (rx_queue_head s1 + len (rx_queue s1) + len fillable1) mod rx_queue_capacity s1 =
          (rx_queue_head s1 + len (rx_queue s1) + len fillable2) mod rx_queue_capacity s1)
          by lia.
        assert (
          (len fillable1) mod rx_queue_capacity s1 =
          (len fillable2) mod rx_queue_capacity s1)
          as Hlf by case TODO.
        rewrite 2Z.mod_small in Hlf by lia.
        exact Hlf.
      }
      assert (len new_descs1 = len new_descs2) by lia.
      (* In M1a and M2a, we have the same base address, start index, modulus, and
         list length, so: *)
      assert (map.same_domain mGive1a mGive2a) as Hsd by case TODO.
      (* Because of D1, D2, H1, H2: mGive1a and mGive2a are part of the same big m,
         so since they have the same footprint, they must also have the same values: *)
      assert (mGive1a = mGive2a) by case TODO.
      subst mGive2a. clear Hsd.
      (* But now, M1a and M2a imply: *)
      replace new_descs2 with new_descs1 in * by case TODO.
      set (addrs := (List.map (fun d : rx_desc => /[rx_desc_addr d])
                       (rx_queue s1 ++ new_descs1))) in *.
      move M1b at bottom. move M2b at bottom.
      (* same addresses in M1b and M2b and same element size means same footprint: *)
      assert (map.same_domain mGive1b mGive2b) as Hsd by case TODO.
      (* Because of D1, D2, H1, H2: mGive1b and mGive2b are part of the same big m,
         so since they have the same footprint, they must also have the same values: *)
      assert (mGive1b = mGive2b) by case TODO.
      subst mGive2b. clear Hsd.
      (* But now, M1b and M2b imply: *)
      replace fillable2 with fillable1 in * by case TODO.
      unfold map.split in D1, D2.
      destruct D1 as (? & D1). destruct D2 as (? & D2).
      subst mGive1 mGive2.
      reflexivity.
  Qed.

  Definition trace_state_satisfies(t: trace)(P: e1000_state -> Prop): Prop :=
    (exists s, trace_can_lead_to is_initial_e1000_state e1000_step t s) /\
    (forall s, trace_can_lead_to is_initial_e1000_state e1000_step t s -> P s).

  Context {locals: map.map String.string word}.

  (* TODO move to bedrock2.Semantics *)
  Lemma exec_interact_cps: forall e binds action arges args t m l post mKeep mGive,
      map.split m mKeep mGive ->
      eval_call_args m l arges = Some args ->
      ext_spec t mGive action args (fun mReceive resvals =>
          exists l', map.putmany_of_list_zip binds resvals l = Some l' /\
          forall m', map.split m' mKeep mReceive ->
          post (cons ((mGive, action, args), (mReceive, resvals)) t) m' l') ->
      exec e (cmd.interact binds action arges) t m l post.
  Proof. intros. eauto using exec.interact. Qed.

  (* read RDH: new RDH can be anywhere between old RDH (incl) and old RDT (excl),
     we receive the memory chunk for each descriptor between old and new RDH,
     as well as the buffers pointed to by them, which contain newly received packets *)
  Lemma wp_read_RDH: forall e cfg old_RDH old_rx_descs t m l r post,
      trace_state_satisfies t (fun s => e1000_ok cfg s /\
         s.(rx_queue_head) = old_RDH /\ s.(rx_queue) = old_rx_descs) ->
      (forall (m' mRcv: mem) (packets: list buf),
          map.split m' mRcv m ->
          len packets <= len old_rx_descs ->
          let new_RDH := /[(old_RDH + len packets) mod cfg.(rx_queue_capacity)] in
          (* we get back a (wrapping) slice of the rx queue as well as the corresponding
             buffers *)
          <{ * circular_buffer_slice rx_desc_t cfg.(rx_queue_capacity) old_RDH
                                     old_rx_descs[:len packets] /[cfg.(rx_queue_base_addr)]
             * scattered_array (array (uint 8) cfg.(rx_buf_size)) packets
                   (List.map (fun d => /[d.(rx_desc_addr)]) (old_rx_descs[:len packets]))
          }> mRcv ->
          post (cons ((map.empty, "MMIOREAD", [| /[E1000_RDH] |]), (mRcv, [|new_RDH|])) t)
               m' (map.put l r new_RDH)) ->
      exec e (cmd.interact [|r|] "MMIOREAD" [|expr.literal E1000_RDH|]) t m l post.
  Proof.
    intros.
    unfold trace_state_satisfies in *. fwd.
    eapply exec_interact_cps.
    3: {
      unfold ext_spec, StateMachineBasedExtSpec.ext_spec.
      split. 1: eauto.
      intros. split.
      - do 3 eexists. eapply read_RDH_step.
        (* TODO the "exists step" part needs to be in the hypotheses *)
  Abort.

End WithMem.
