(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Definition MBUF_SIZE := 2048.

Record mbuf_t := {
  mbuf_len: Z;
  mbuf_data: list Z;
}.

Definition mbuf(r: mbuf_t): word -> mem -> Prop := .**/
  typedef struct __attribute__ ((__packed__)) {
    size_t mbuf_len;
    uint8_t mbuf_data[MBUF_SIZE];
  } mbuf_t;
/**.

End LiveVerif.
