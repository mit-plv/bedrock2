Require Import bedrock2.TracePredicate.
Require Import Coq.ZArith.BinInt Coq.Strings.String.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Byte.
Require Import coqutil.Word.LittleEndianList.

Section LightbulbSpec.
  Local Open Scope list_scope.
  Import BinInt List.ListNotations TracePredicateNotations.
  Local Open Scope Z_scope.
  Let width := 32.
  Local Notation word := (bits width).
  Implicit Types v : word.

  Declare Scope word_scope.
  Notation "! n" := (bits.of_Z width n) (at level 0, n at level 0, format "! n") : word_scope.
  Notation "# n" := (Z.of_nat n) (at level 0, n at level 0, format "# n") : word_scope.
  Infix "+" := Zmod.add : word_scope.
  Infix "-" := Zmod.sub : word_scope.
  Infix "*" := Zmod.mul : word_scope.
  Notation "- x" := (Zmod.opp x) : word_scope.
  Delimit Scope word_scope with word.
  Local Open Scope word_scope.
  Local Open Scope string_scope.

  (* Common event between bedrock2 and Kami.
     Has to be of the form ("ld", addr, value) or ("st", addr, value).
     We don't use Inductives here so that we can share the same type with bedrock2 without
     depending on a common library. *)
  Definition OP: Type := (string * word * word).

  (** FE310 GPIO *)
  Definition GPIO_DATA_ADDR : word := bits.of_Z width (0x1001200c).
  (* i < 32, only some GPIOs are connected to external pins *)
  Definition gpio_set (i:Z) value :=
    existsl (fun v =>
      one ("ld", GPIO_DATA_ADDR, v) +++
      one ("st", GPIO_DATA_ADDR, (
        let cleared := Zmod.and v (bits.of_Z width (Z.clearbit (2^32-1) i)) in
        Zmod.or cleared (Zmod.slu (bits.of_Z width (Z.b2z value)) i)
      ))).

  (** F310 SPI *)
  Definition SPI_RX_FIFO_ADDR : word := bits.of_Z width (0x1002404c).
  Definition SPI_TX_FIFO_ADDR : word := bits.of_Z width (0x10024048).
  Definition SPI_CSMODE_ADDR : word := bits.of_Z width (0x10024018).
  Definition SPI_CSMODE_HOLD : word := bits.of_Z width 2.

  Definition spi_read_empty l :=
    exists v, one ("ld", SPI_RX_FIFO_ADDR, v) l /\ Z.shiftr (Zmod.unsigned v) 31 <> 0.
  Definition spi_read_dequeue (b : byte) l :=
    exists v, one ("ld", SPI_RX_FIFO_ADDR, v) l /\ Z.shiftr (Zmod.unsigned v) 31 = 0 /\ b = byte.of_Z (Zmod.unsigned v).
  Definition spi_read b :=
    spi_read_empty^* +++ spi_read_dequeue b.

  Definition spi_write_full l :=
    exists v, one ("ld", SPI_TX_FIFO_ADDR, v) l /\ Z.shiftr (Zmod.unsigned v) 31 <> 0.
  Definition spi_write_ready l :=
    exists v, one ("ld", SPI_TX_FIFO_ADDR, v) l /\ Z.shiftr (Zmod.unsigned v) 31 = 0.
  Definition spi_write_enqueue (b : byte) :=
    one ("st", SPI_TX_FIFO_ADDR, (bits.of_Z width (byte.unsigned b))).
  Definition spi_write b :=
    spi_write_full^* +++ (spi_write_ready +++ spi_write_enqueue b).

  Definition patience : Z := 2^32-1.

  Definition spi_timeout ioh := (spi_write_full ^* ||| spi_read_empty ^* ) ioh /\ Z.of_nat (List.length ioh) = patience.

  Definition spi_begin := existsl (fun v =>
    one ("ld", SPI_CSMODE_ADDR, v) +++ one ("st", SPI_CSMODE_ADDR, (Zmod.or v SPI_CSMODE_HOLD))).
  Definition spi_xchg tx rx :=
    spi_write tx +++ spi_read rx.
  Definition spi_xchg_deaf tx :=
    existsl (fun rx => spi_xchg tx rx).
  Definition spi_xchg_mute rx :=
    existsl (fun tx => spi_xchg tx rx).
  Definition spi_xchg_dummy :=
    existsl (fun tx => (existsl (fun rx => spi_xchg tx rx))).
  Definition spi_end := existsl (fun v =>
    one ("ld", SPI_CSMODE_ADDR, v) +++
    one ("st", SPI_CSMODE_ADDR, (Zmod.and v (bits.of_Z width (Z.lnot (Zmod.unsigned SPI_CSMODE_HOLD)))))).

  (** LAN9250 *)
  Definition LAN9250_FASTREAD : byte := Byte.x0b.

  Definition lan9250_fastread4 (a v : word) t :=
    exists a0 a1 b0 b1 b2 b3, (
    spi_begin +++
    spi_xchg_deaf LAN9250_FASTREAD +++
    spi_xchg_deaf a1 +++
    spi_xchg_deaf a0 +++
    spi_xchg_dummy +++
    spi_xchg_mute b0 +++
    spi_xchg_mute b1 +++
    spi_xchg_mute b2 +++
    spi_xchg_mute b3 +++
    spi_end) t /\
    byte.unsigned a1 = Zmod.unsigned (Zmod.sru a 8) /\
    byte.unsigned a0 = Zmod.unsigned (Zmod.and a 255) /\
    Zmod.unsigned v = le_combine (cons b0 (cons b1 (cons b2 (cons b3 nil)))).

  Definition LAN9250_WRITE : byte := Byte.x02.
  Definition HW_CFG : Z := 0x074.
  Definition TX_DATA_FIFO : Z := 0x20.

  Definition lan9250_write4 (a v : word) t :=
    exists a0 a1 b0 b1 b2 b3, (
    spi_begin +++
    spi_xchg_deaf LAN9250_WRITE +++
    spi_xchg_deaf a1 +++
    spi_xchg_deaf a0 +++
    spi_xchg_deaf b0 +++
    spi_xchg_deaf b1 +++
    spi_xchg_deaf b2 +++
    spi_xchg_deaf b3 +++
    spi_end) t /\
    byte.unsigned a1 = Zmod.unsigned (Zmod.sru a 8) /\
    byte.unsigned a0 = Zmod.unsigned (Zmod.and a 255) /\
    Zmod.unsigned v = le_combine (cons b0 (cons b1 (cons b2 (cons b3 nil)))).

  Local Definition lan9250_writeword (a v : Z) := lan9250_write4 (bits.of_Z width a) (bits.of_Z width v).

  (* NOTE: we could do this without rounding up to the nearest word, and this
  * might be necessary for other stacks than IP-TCP and IP-UDP *)
  Definition lan9250_decode_length  (status : word) : word :=
    let x := Zmod.and (Zmod.sru status 16) (bits.of_Z width (2^14-1)) in
    let y := Zmod.sru (Zmod.add x 3) 2 in
    let z := Zmod.add y y in
    Zmod.add z z.

  Fixpoint lan9250_readpacket (bs : list byte) :=
    match bs with
    | nil => eq nil
    | cons b0 (cons b1 (cons b2 (cons b3 bs))) =>
      lan9250_fastread4 (bits.of_Z width 0) (bits.of_Z width (le_combine [b0;b1;b2;b3])) +++
      lan9250_readpacket bs
    | _ => constraint False (* TODO: padding? *)
    end.

  Definition lan9250_recv_no_packet ioh :=
    exists info, lan9250_fastread4 (bits.of_Z width 124) info ioh /\
    Zmod.unsigned (Zmod.and info (bits.of_Z width ((2^8-1)*2^16))) = 0.
  Definition lan9250_recv_packet_too_long ioh := ((exists (info status:word),
    (lan9250_fastread4 (bits.of_Z width 124) info +++ lan9250_fastread4 (bits.of_Z width 64) status) ioh /\
    Z.land (Zmod.unsigned info) ((2^8-1)*2^16) <> 0 /\
    (Zmod.unsigned (lan9250_decode_length status) > 1520))).
  Definition lan9250_recv (recv : list byte) ioh : Prop :=
    exists info status,
    (lan9250_fastread4 (bits.of_Z width 124) info +++
    lan9250_fastread4 (bits.of_Z width 64) status +++
    lan9250_readpacket recv) ioh /\
    Z.land (Zmod.unsigned info) ((2^8-1)*2^16) <> 0 /\
    Z.of_nat (List.length recv) = Zmod.unsigned (lan9250_decode_length status).

  Fixpoint lan9250_writepacket (bs : list byte) : list _ -> Prop :=
    match bs with
    | nil => fun trace => trace = []
    | b0::b1::b2::b3::bs => lan9250_writeword TX_DATA_FIFO (le_combine [b0;b1;b2;b3])
                            +++ lan9250_writepacket bs
    | _ => fun _ => False
    end.
  Definition lan9250_send (send : list byte) : list _ -> Prop :=
    lan9250_write4 (bits.of_Z width TX_DATA_FIFO) (Zmod.or (Zmod.or (bits.of_Z width (2^13)) ((bits.of_Z width (2^12)))) (bits.of_Z width (# (List.length send)))) +++
    lan9250_write4 (bits.of_Z width TX_DATA_FIFO) (bits.of_Z width (# (List.length send))) +++
    lan9250_writepacket send.

  Definition lan9250_boot_attempt : list OP -> Prop :=
    (fun attempt => exists v, lan9250_fastread4 (bits.of_Z width (0x64)) v attempt
    /\ Zmod.unsigned v <> 0x87654321).
  Definition lan9250_boot_timeout : list OP -> Prop :=
    multiple lan9250_boot_attempt (Z.to_nat patience).

  Definition lan9250_wait_for_boot_trace : list OP -> Prop :=
    lan9250_boot_attempt ^* +++
    lan9250_fastread4 (bits.of_Z width (0x64)) (bits.of_Z width (0x87654321)).

  Definition lan9250_mac_write_trace a v ioh := exists x,
     (lan9250_write4 (bits.of_Z width 168) v +++
     lan9250_write4 (bits.of_Z width 164) (Zmod.or (bits.of_Z width (2^31)) a) +++
     lan9250_fastread4 (bits.of_Z width 100) x) ioh.

  Definition lan9250_init_trace ioh := exists cfg0,
    let cfg' := Zmod.or cfg0 1048576 in
    let cfg := Zmod.and cfg' (bits.of_Z width (-2097153)) in
    (lan9250_wait_for_boot_trace  +++
    lan9250_fastread4 (bits.of_Z width HW_CFG) cfg0 +++
    lan9250_write4 (bits.of_Z width HW_CFG) cfg +++
    lan9250_mac_write_trace (bits.of_Z width 1) (bits.of_Z width (Z.lor (Z.shiftl 1 20) (Z.lor (Z.shiftl 1 18) (Z.lor (Z.shiftl 1 3) (Z.shiftl 1 2))))) +++
    lan9250_write4 (bits.of_Z width (0x070)) (bits.of_Z width (Z.lor (Z.shiftl 1 2) (Z.shiftl 1 1)))) ioh.

  (** lightbulb *)
  Definition lightbulb_packet_rep cmd (buf : list byte) := (
    let idx i buf : word := bits.of_Z width (byte.unsigned (List.hd Byte.x00 (List.skipn i buf))) in
    42 < Z.of_nat (List.length buf) /\
    1535 < Zmod.unsigned ((Zmod.or (Zmod.slu (idx 12%nat buf) 8) (idx 13%nat buf))) /\
    idx 23%nat buf = bits.of_Z width (0x11) /\
    cmd = Z.testbit (byte.unsigned (List.hd Byte.x00 (List.skipn 42 buf))) 0).

  Definition iocfg : list OP -> Prop :=
    one ("st", !(0x10012038), !(Z.shiftl (0xf) 2)) +++
    one ("st", !(0x10012008), !(Z.shiftl 1 23)).

  Definition BootSeq : list OP -> Prop :=
    iocfg +++ (lan9250_init_trace
                 ||| lan9250_boot_timeout
                 ||| (any+++spi_timeout)).

  Definition Recv (cmd : bool) (t : list OP) : Prop :=
    exists (packet : list byte),
      lan9250_recv packet t /\
      lightbulb_packet_rep cmd packet.

  Definition LightbulbCmd (cmd : bool) : list OP -> Prop := gpio_set 23 cmd.

  Definition RecvInvalid : list OP -> Prop :=
    (fun t => exists (packet : list byte),
         lan9250_recv packet t /\
         ~ (exists (cmd : bool), lightbulb_packet_rep cmd packet)) |||
    (lan9250_recv_packet_too_long) |||
    (any+++spi_timeout).

  Definition PollNone : list OP -> Prop := lan9250_recv_no_packet.

  Definition goodHlTrace: list OP -> Prop :=
    BootSeq +++ ((EX b: bool, Recv b +++ LightbulbCmd b)
                 ||| RecvInvalid ||| PollNone) ^*.

  Context {mem: Interface.map.map word Byte.byte}.

  Definition mmio_event_abstraction_relation (h : OP)
    (l : mem * string * list word * (mem * list word)) :=
    Logic.or
      (exists a v, h = ("st", a, v) /\ l = (map.empty, "MMIOWRITE", [a; v], (map.empty, [])))
      (exists a v, h = ("ld", a, v) /\ l = (map.empty, "MMIOREAD", [a], (map.empty, [v]))).
  Definition mmio_trace_abstraction_relation :=
    List.Forall2 mmio_event_abstraction_relation.
  Definition only_mmio_satisfying P t :=
    exists mmios, mmio_trace_abstraction_relation mmios t /\ P mmios.
End LightbulbSpec.
Global Arguments mmio_event_abstraction_relation {_}.
Global Arguments mmio_trace_abstraction_relation {_}.

Lemma align_trace_cons {T} x xs cont t (H : xs = app cont t) : @cons T x xs = app (cons x cont) t.
Proof. intros. cbn. congruence. Qed.
Lemma align_trace_app {T} x xs cont t (H : xs = app cont t) : @app T x xs = app (app x cont) t.
Proof. intros. cbn. subst. rewrite List.app_assoc; trivial. Qed.
