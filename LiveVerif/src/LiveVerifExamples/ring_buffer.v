(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Record raw_ring_buffer := {
  capacity: Z;
  dequeue_pos: Z;
  n_elems: Z;
  data: list word;
}.

Definition raw_ring_buffer_t(r: raw_ring_buffer): word -> mem -> Prop := .**/
typedef struct __attribute__ ((__packed__)) {
  uint32_t capacity;
  uint32_t dequeue_pos;
  uint32_t n_elems;
  uintptr_t data[/**# capacity r #**/];
} raw_ring_buffer_t;
/**.

Definition ring_buffer(cap: Z)(vs: list word)(addr: word): mem -> Prop :=
  ex1 (fun b: raw_ring_buffer =>
    sep (raw_ring_buffer_t b addr)
        (emp (capacity b = cap /\
              0 <= dequeue_pos b < cap /\
              0 <= n_elems b <= cap /\
              len (data b) = cap /\
              (data b ++ data b)[dequeue_pos b : dequeue_pos b + n_elems b] = vs))).

Lemma purify_ring_buffer: forall cap vs addr,
    purify (ring_buffer cap vs addr) (len vs <= cap).
Proof.
  unfold purify, ring_buffer, ex1. intros. fwd.
  repeat step_silent.
  subst.
  bottom_up_simpl_in_goal.
  lia.
Qed.
Hint Resolve purify_ring_buffer : purify.

Hint Unfold ring_buffer : live_always_unfold.

#[export] Instance spec_of_ring_buf_enq: fnspec :=                              .**/

void ring_buf_enq(uintptr_t b_addr, uintptr_t v) /**#
  ghost_args := cap vs (R: mem -> Prop);
  requires t m := <{ * ring_buffer cap vs b_addr
                     * R }> m /\
                  len vs < cap;
  ensures t' m' := t' = t /\
       <{ * ring_buffer cap (vs ++ [|v|]) b_addr
          * R }> m' #**/                                                   /**.
Derive ring_buf_enq SuchThat (fun_correct! ring_buf_enq) As ring_buf_enq_ok.    .**/
{                                                                          /**. .**/
  uintptr_t i = (load32(b_addr+4) + load32(b_addr+8)) % load32(b_addr);    /**.

  (* TODO support &p->field notation, which would allow writing this:
     (but probably need a cast of uintptr to record type first?
  uintptr_t i = (load32(&b_addr->dequeue_pos) + load32(&b_addr->n_elems))
                % load32(&b_addr->capacity);

  store32(&b_addr->data +
  store32(b_addr + 12 + load32(b_addr
*)

Abort.

End LiveVerif. Comments .**/ //.
