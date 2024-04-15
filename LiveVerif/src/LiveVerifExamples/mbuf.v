(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Definition MBUF_SIZE := 2048.

(* Note: this will result in mbufs slightly bigger than half of a 4KB page,
   so most mbufs will span two pages, which seems bad --> don't do this!
Record mbuf_t := {
  mbuf_len: Z;
  mbuf_data: list Z;
}.
Definition mbuf(r: mbuf_t): word -> mem -> Prop := .**/
  typedef struct __attribute__ ((__packed__)) {
    size_t mbuf_len;
    uint8_t mbuf_data[MBUF_SIZE];
  } mbuf;
/**. *)

Definition mbuf(n: Z)(bs: list Z)(a: word): mem -> Prop :=
  <{ * array (uint 8) n bs a
     * array (uint 8) (MBUF_SIZE - n) ? (a ^+ /[n]) }>.

End LiveVerif.

#[export] Hint Extern 1 (PredicateSize (mbuf ?n ?bs)) => exact MBUF_SIZE
: typeclass_instances.
