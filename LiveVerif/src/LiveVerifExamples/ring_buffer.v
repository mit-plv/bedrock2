(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import bedrock2.RecordPredicates.

Load LiveVerif.

Record raw_ring_buffer_t := {
  capacity: uint_t 32;
  dequeue_pos: uint_t 32;
  n_elems: uint_t 32;
  data: array_t word capacity;
}.

Global Instance raw_ring_buffer: RepPredicate raw_ring_buffer_t := ltac:(create_predicate).

Definition ring_buffer(cap: Z)(vs: list word)(addr: word): mem -> Prop :=
  ex1 (fun b: raw_ring_buffer_t =>
    sep (raw_ring_buffer b addr)
        (emp (capacity b = cap /\ n_elems b = len vs /\
             (data b ++ data b)[dequeue_pos b : dequeue_pos b + n_elems b] = vs))).

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
  uintptr_t i = (load4(b_addr+4) + load4(b_addr+8)) % load4(b_addr);       /**.

  clear Error.
  unfold raw_ring_buffer in *|-.

  (* TODO support &p->field notation, which would allow writing
  uintptr_t i = (load4(&b_addr->dequeue_pos) + load4(&b_addr->n_elems))
                % load4(&b_addr->capacity);

  store4(&b_addr->data +
  store4(b_addr + 12 + load4(b_addr
*)

Abort.

End LiveVerif. Comments .**/ //.
