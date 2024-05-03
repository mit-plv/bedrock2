(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Notation ".* */ '#define' lhs rhs /* *" := (lhs = rhs)
  (at level 200, lhs constr at level 0, rhs constr at level 0, only parsing).

Definition MBUF_SIZE := 2048. Remark MBUF_SIZE_def: .**/
#define MBUF_SIZE 2048
/**. reflexivity. Qed.

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

(* Note: this is not easily compatible with viewing a buffer as a more structured packet
Definition mbuf(n: Z)(bs: list Z)(a: word): mem -> Prop :=
  <{ * array (uint 8) n bs a
     * array (uint 8) (MBUF_SIZE - n) ? (a ^+ /[n]) }>. *)

(* Note: this is not easily compatible with predicates that combine headers & payload
   (to put length of payload into headers)
Definition mbuf
  (headers: word -> mem -> Prop){headers_sz: PredicateSize headers}
  (payload: word -> mem -> Prop){payload_sz: PredicateSize payload}
  : word -> mem -> Prop :=
  <{ + headers
     + payload
     + anyval (array (uint 8) (MBUF_SIZE - headers_sz - payload_sz)) }>. *)

(* Note: requiring a packet_sz for a potentially abstract packet predicate
   is a bit awkward, because quantifying over {packet_sz: PredicateSize packet}
   in a function spec will put it into a forall, where we can't really mark
   arguments as implicit, and we will typically still pass the size as a
   non-ghost parameter, so we need an equality between the ghost size and the
   actual size, all a bit awkward.
   BUT using mbuf by passing it an abstract predicate is a bad idea anyways,
   because we can't know that the footprint of the abstract predicate is
   exactly packet_sz bytes starting at addr, so we will always pass concrete
   predicates (eg array, or combinations of array and packet headers) to mbuf. *)
Definition mbuf(packet: word -> mem -> Prop){packet_sz: PredicateSize packet}
  : word -> mem -> Prop :=
  <{ + packet
     + anyval (array (uint 8) (MBUF_SIZE - packet_sz)) }>.

(* Or how about we just make the packet_sz argument explicit:

Definition mbuf(packet: word -> mem -> Prop)(packet_sz: PredicateSize packet)
  : word -> mem -> Prop :=
  <{ + packet
     + anyval (array (uint 8) (MBUF_SIZE - packet_sz)) }>.

But now, putting the size after the packet is a bit awkward (because eg in array,
size comes first), so let's flip the order:

Definition mbuf(packet_sz: Z)(packet: word -> mem -> Prop)(addr: word): mem -> Prop :=
  <{ * packet addr
     * array (uint 8) (MBUF_SIZE - packet_sz) ? (addr ^+ /[packet_sz]) }>.

but usage requires size twice (as an argument to mbuf & to array)
mbuf \[n]
     <{ + headers_upto_ethernet h
        + array (uint 8) (\[n] - sizeof headers_upto_ethernet) bs }> a
*)

End LiveVerif.

#[export] Hint Extern 1 (PredicateSize (mbuf ?n ?bs)) => exact MBUF_SIZE
: typeclass_instances.
