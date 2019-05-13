Require Import bedrock2.TracePredicate.
Require Import Coq.ZArith.BinInt.
Require Import coqutil.Word.Interface.
Section LightbulbSpec.
  Import TracePredicateNotations.
  Let width := 32%Z.
  Context (byte : word 8%Z) (word : word width).
  
  (** MMIO *)
  Inductive OP :=
  | ld (addr value:word)
  | st (addr value:word).
  
  (** FE310 GPIO *)
  Definition GPIO_DATA_ADDR : word. Admitted.
  (* i < 32, only some GPIOs are connected to external pins *)
  Definition gpio_on (i:Z) :=
    existsl (fun v =>
      one (ld GPIO_DATA_ADDR v) +++
      one (st GPIO_DATA_ADDR (word.of_Z (Z.setbit (word.unsigned v) i)))).
  Definition gpio_off (i:Z) :=
    existsl (fun v =>
      one (ld GPIO_DATA_ADDR v) +++
      one (st GPIO_DATA_ADDR (word.of_Z (Z.clearbit (word.unsigned v) i)))).
  
  (** F310 SPI *)
  Definition SPI_RX_FIFO_ADDR : word. Admitted.
  Definition SPI_TX_FIFO_ADDR : word. Admitted.
  Definition SPI_CSMODE_ADDR : word. Admitted.
  Definition SPI_CSMODE_AUTO : word. Admitted.
  Definition SPI_CSMODE_HOLD : word. Admitted.

  Definition spi_read_empty l :=
    exists v, one (ld SPI_RX_FIFO_ADDR v) l /\ Z.testbit (word.unsigned v) 31 = true.
  Definition spi_read_success (b : byte) l :=
    exists v, one (ld SPI_RX_FIFO_ADDR v) l /\ Z.testbit (word.unsigned v) 31 = false /\ word.unsigned (word.and v (word.of_Z (2^8-1))) = word.unsigned b.
  Definition spi_read_dequeue b :=
    spi_read_empty^* +++ spi_read_success b.
  
  Definition spi_write_full l :=
    exists v, one (ld SPI_TX_FIFO_ADDR v) l /\ Z.testbit (word.unsigned v) 31 = true.
  Definition spi_write_ready l :=
    exists v, one (ld SPI_TX_FIFO_ADDR v) l /\ Z.testbit (word.unsigned v) 31 = false.
  Definition spi_write_enqueue (b : byte) l :=
    exists v, one (st SPI_RX_FIFO_ADDR v) l /\ word.unsigned (word.and v (word.of_Z (2^8-1))) = word.unsigned b.
  Definition spi_write b :=
    spi_write_full^* +++ spi_write_ready^+ +++ spi_write_enqueue b.
  
  Definition spi_begin := one (st SPI_CSMODE_ADDR SPI_CSMODE_HOLD).
  Definition spi_xchg tx rx :=
    spi_write tx +++ spi_read_dequeue rx.
  Definition spi_xchg_deaf tx :=
    existsl (fun rx => spi_write tx +++ spi_read_dequeue rx).
  Definition spi_xchg_mute rx :=
    existsl (fun tx => spi_write tx +++ spi_read_dequeue rx).
  Definition spi_xchg_dummy :=
    existsl (fun tx => (existsl (fun rx => spi_write tx +++ spi_read_dequeue rx))).
  Definition spi_end := one (st SPI_CSMODE_ADDR SPI_CSMODE_AUTO).
  
  (** LAN9250 *)
  Definition LAN9250_FASTREAD : byte. Admitted.
  (* TODO: byte order? *)
  Definition lan9250_fastread4 (a0 a1 v0 v1 v2 v3 : byte) := 
    spi_begin +++
    spi_xchg_deaf LAN9250_FASTREAD +++
    spi_xchg_deaf a1 +++
    spi_xchg_deaf a0 +++
    spi_xchg_dummy +++
    spi_xchg_mute v0 +++
    spi_xchg_mute v1 +++
    spi_xchg_mute v2 +++
    spi_xchg_mute v3.
  
  Fixpoint lan9250_readpacket (bs : list byte) :=
    match bs with
    | nil => eq nil
    | cons b0 (cons b1 (cons b2 (cons b3 bs))) =>
      lan9250_fastread4 (word.of_Z 0) (word.of_Z 0) b0 b1 b2 b3 +++
      lan9250_readpacket bs
    | _ => constraint False (* TODO: padding? *)
    end.
  
  Definition lan9250_recv (bs : list byte) : list OP -> Prop. refine (
      lan9250_fastread4 _ _ _ _ _ _ +++
      lan9250_readpacket bs).
  Admitted.
  
  (** lightbulb *)
  Definition packet_turn_on_light (bs : list byte) : Prop. Admitted.
  Definition packet_turn_off_light (bs : list byte) : Prop. Admitted.

  Definition lightbulb_init : list OP -> Prop. Admitted.
  
  Definition lightbulb_step :=
    existsl (fun p => lan9250_recv p +++ (
      eq nil
      ||| (constraint (packet_turn_on_light p) +++ gpio_on 23)
      ||| (constraint (packet_turn_on_light p) +++ gpio_off 23))).
  
  Definition lightbulb_spec :=
    lightbulb_init +++ lightbulb_step^*.
End LightbulbSpec.