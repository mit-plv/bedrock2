Require Import bedrock2.TracePredicate.
Require Import Coq.ZArith.BinInt Coq.Strings.String.
Require Import coqutil.Word.Interface.
Require Import coqutil.Byte.
Require coqutil.Word.LittleEndianList.

Section LightbulbSpec.
  Import BinInt TracePredicateNotations.
  Local Open Scope Z_scope.
  Let width := 32.
  Context (word : word width).
  Implicit Types v : word.

  Declare Scope word_scope.
  Notation "! n" := (word.of_Z n) (at level 0, n at level 0, format "! n") : word_scope.
  Notation "# n" := (Z.of_nat n) (at level 0, n at level 0, format "# n") : word_scope.
  Infix "+" := word.add : word_scope.
  Infix "-" := word.sub : word_scope.
  Infix "*" := word.mul : word_scope.
  Notation "- x" := (word.opp x) : word_scope.
  Delimit Scope word_scope with word.
  Local Open Scope word_scope.
  Local Open Scope string_scope.

  (* Common event between bedrock2 and Kami.
     Has to be of the form ("ld", addr, value) or ("st", addr, value).
     We don't use Inductives here so that we can share the same type with bedrock2 without
     depending on a common library. *)
  Definition OP: Type := (string * word * word).

  (** FE310 GPIO *)
  Definition GPIO_DATA_ADDR : word := word.of_Z (0x1001200c).
  (* i < 32, only some GPIOs are connected to external pins *)
  Definition gpio_set (i:Z) value :=
    existsl (fun v =>
      one ("ld", GPIO_DATA_ADDR, v) +++
      one ("st", GPIO_DATA_ADDR, (
        let cleared := word.and v (word.of_Z (Z.clearbit (2^32-1) i)) in
        word.or cleared (word.slu (word.of_Z (Z.b2z value)) (word.of_Z i))
      ))).

  (** F310 SPI *)
  Definition SPI_RX_FIFO_ADDR : word := word.of_Z (0x1002404c).
  Definition SPI_TX_FIFO_ADDR : word := word.of_Z (0x10024048).
  Definition SPI_CSMODE_ADDR : word := word.of_Z (0x10024018).
  Definition SPI_CSMODE_HOLD : word := word.of_Z 2.

  Definition spi_read_empty l :=
    exists v, one ("ld", SPI_RX_FIFO_ADDR, v) l /\ Z.shiftr (word.unsigned v) 31 <> 0.
  Definition spi_read_dequeue (b : byte) l :=
    exists v, one ("ld", SPI_RX_FIFO_ADDR, v) l /\ Z.shiftr (word.unsigned v) 31 = 0 /\ b = byte.of_Z (word.unsigned v).
  Definition spi_read b :=
    spi_read_empty^* +++ spi_read_dequeue b.

  Definition spi_write_full l :=
    exists v, one ("ld", SPI_TX_FIFO_ADDR, v) l /\ Z.shiftr (word.unsigned v) 31 <> 0.
  Definition spi_write_ready l :=
    exists v, one ("ld", SPI_TX_FIFO_ADDR, v) l /\ Z.shiftr (word.unsigned v) 31 = 0.
  Definition spi_write_enqueue (b : byte) :=
    one ("st", SPI_TX_FIFO_ADDR, (word.of_Z (width:=width) (byte.unsigned b))).
  Definition spi_write b :=
    spi_write_full^* +++ (spi_write_ready +++ spi_write_enqueue b).

  Definition patience : Z := 2^32-1.

  Definition spi_timeout ioh := (spi_write_full ^* ||| spi_read_empty ^* ) ioh /\ Z.of_nat (List.length ioh) = patience.

  Definition spi_begin := existsl (fun v =>
    one ("ld", SPI_CSMODE_ADDR, v) +++ one ("st", SPI_CSMODE_ADDR, (word.or v SPI_CSMODE_HOLD))).
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
    one ("st", SPI_CSMODE_ADDR, (word.and v (word.of_Z (Z.lnot (word.unsigned SPI_CSMODE_HOLD)))))).

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
    byte.unsigned a1 = word.unsigned (word.sru a (word.of_Z 8)) /\
    byte.unsigned a0 = word.unsigned (word.and a (word.of_Z 255)) /\
    word.unsigned v = LittleEndianList.le_combine (cons b0 (cons b1 (cons b2 (cons b3 nil)))).

  Definition LAN9250_WRITE : byte := Byte.x02.
  Definition HW_CFG : Z := 0x074.

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
    byte.unsigned a1 = word.unsigned (word.sru a (word.of_Z 8)) /\
    byte.unsigned a0 = word.unsigned (word.and a (word.of_Z 255)) /\
    word.unsigned v = LittleEndianList.le_combine (cons b0 (cons b1 (cons b2 (cons b3 nil)))).

  (* NOTE: we could do this without rounding up to the nearest word, and this
  * might be necessary for other stacks than IP-TCP and IP-UDP *)
  Definition lan9250_decode_length  (status : word) : word :=
    let x := word.and (word.sru status (word.of_Z 16)) (word.of_Z (2^14-1)) in
    let y := word.sru (word.add x (word.of_Z 3)) (word.of_Z 2) in
    let z := word.add y y in
    word.add z z.

  Fixpoint lan9250_readpacket (bs : list byte) :=
    match bs with
    | nil => eq nil
    | cons v0 (cons v1 (cons v2 (cons v3 bs))) =>
      lan9250_fastread4 (word.of_Z 0) (word.of_Z (LittleEndianList.le_combine (cons v0 (cons v1 (cons v2 (cons v3 nil)))))) +++
      lan9250_readpacket bs
    | _ => constraint False (* TODO: padding? *)
    end.

  Definition lan9250_recv_no_packet ioh :=
    exists info, lan9250_fastread4 (word.of_Z 124) info ioh /\
    word.unsigned (word.and info (word.of_Z ((2^8-1)*2^16))) = 0.
  Definition lan9250_recv_packet_too_long ioh := ((exists (info status:word),
    (lan9250_fastread4 (word.of_Z 124) info +++ lan9250_fastread4 (word.of_Z 64) status) ioh /\
    Z.land (word.unsigned info) ((2^8-1)*2^16) <> 0 /\
    (word.unsigned (lan9250_decode_length status) > 1520))).
  Definition lan9250_recv (recv : list byte) ioh : Prop :=
    exists info status,
    (lan9250_fastread4 (word.of_Z 124) info +++
    lan9250_fastread4 (word.of_Z 64) status +++
    lan9250_readpacket recv) ioh /\
    Z.land (word.unsigned info) ((2^8-1)*2^16) <> 0 /\
    Z.of_nat (List.length recv) = word.unsigned (lan9250_decode_length status).

  Definition lan9250_boot_attempt : list OP -> Prop :=
    (fun attempt => exists v, lan9250_fastread4 (word.of_Z (0x64)) v attempt
    /\ word.unsigned v <> 0x87654321).
  Definition lan9250_boot_timeout : list OP -> Prop :=
    multiple lan9250_boot_attempt (Z.to_nat patience).

  Definition lan9250_wait_for_boot_trace : list OP -> Prop :=
    lan9250_boot_attempt ^* +++
    lan9250_fastread4 (word.of_Z (0x64)) (word.of_Z (0x87654321)).

  Definition lan9250_mac_write_trace a v ioh := exists x,
     (lan9250_write4 (word.of_Z 168) v +++
     lan9250_write4 (word.of_Z 164) (word.or (word.of_Z (2^31)) a) +++
     lan9250_fastread4 (word.of_Z 100) x) ioh.

  Definition lan9250_init_trace ioh := exists cfg0,
    let cfg' := word.or cfg0 (word.of_Z 1048576) in
    let cfg := word.and cfg' (word.of_Z (-2097153)) in
    (lan9250_wait_for_boot_trace  +++
    lan9250_fastread4 (word.of_Z HW_CFG) cfg0 +++
    lan9250_write4 (word.of_Z HW_CFG) cfg +++
    lan9250_mac_write_trace (word.of_Z 1) (word.of_Z (Z.lor (Z.shiftl 1 20) (Z.lor (Z.shiftl 1 18) (Z.lor (Z.shiftl 1 3) (Z.shiftl 1 2))))) +++
    lan9250_write4 (word.of_Z (0x070)) (word.of_Z (Z.lor (Z.shiftl 1 2) (Z.shiftl 1 1)))) ioh.

  (** lightbulb *)
  Definition lightbulb_packet_rep cmd (buf : list byte) := (
    let idx i buf : word := word.of_Z (byte.unsigned (List.hd Byte.x00 (List.skipn i buf))) in
    42 < Z.of_nat (List.length buf) /\
    1535 < word.unsigned ((word.or (word.slu (idx 12%nat buf) (word.of_Z 8)) (idx 13%nat buf))) /\
    idx 23%nat buf = word.of_Z (0x11) /\
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

End LightbulbSpec.

Lemma align_trace_cons {T} x xs cont t (H : xs = app cont t) : @cons T x xs = app (cons x cont) t.
Proof. intros. cbn. congruence. Qed.
Lemma align_trace_app {T} x xs cont t (H : xs = app cont t) : @app T x xs = app (app x cont) t.
Proof. intros. cbn. subst. rewrite List.app_assoc; trivial. Qed.
