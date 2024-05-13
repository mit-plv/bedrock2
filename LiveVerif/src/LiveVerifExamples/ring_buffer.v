(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Record raw_ring_buf := {
  capacity: Z;
  dequeue_pos: Z;
  n_elems: Z;
  data: list word;
}.

Definition raw_ring_buf_t(r: raw_ring_buf): word -> mem -> Prop := .**/
typedef struct __attribute__ ((__packed__)) {
  uint32_t capacity;
  uint32_t dequeue_pos;
  uint32_t n_elems;
  uintptr_t data[/**# capacity r #**/];
} raw_ring_buf_t;
/**.

Definition ring_buf(cap: Z)(vs: list word)(addr: word): mem -> Prop :=
  EX b: raw_ring_buf,
  <{ * raw_ring_buf_t b addr
     * emp (capacity b = cap /\
            (0 < n_elems b -> 0 <= dequeue_pos b < cap) /\
            0 <= n_elems b <= cap /\
            len (data b) = cap /\
            (data b ++ data b)[dequeue_pos b :][: n_elems b] = vs) }>.

Lemma purify_ring_buf: forall cap vs addr,
    purify (ring_buf cap vs addr) (len vs <= cap).
Proof.
  unfold purify, ring_buf, ex1. intros. fwd.
  repeat step_silent.
  subst.
  bottom_up_simpl_in_goal.
  lia.
Qed.
Hint Resolve purify_ring_buf : purify.

Hint Unfold ring_buf : heapletwise_always_unfold.

#[export] Instance spec_of_raw_ring_buf_init: fnspec :=                           .**/

void raw_ring_buf_init(uintptr_t addr, uintptr_t cap) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * array (uint 8) (12 + 4 * \[cap]) ? addr
                     * R }> m;
  ensures t' m' := t' = t /\ exists b: raw_ring_buf,
      len (data b) = \[cap] /\
       <{ * raw_ring_buf_t b addr
          * R }> m' #**/                                                   /**.
Derive raw_ring_buf_init
  SuchThat (fun_correct! raw_ring_buf_init) As raw_ring_buf_init_ok.            .**/
{                                                                          /**. .**/
  store32(addr, cap);                                                      /**. .**/
}                                                                          /*?.
  delete #(merge_step).
  step. step. step.
  (* TODO this essentially manually pushes down existentials, could we automate this? *)
  enough (<{ * uint 32 \[cap] addr
             * uint 32 ? (addr ^+ /[4])
             * uint 32 ? (addr ^+ /[8])
             * array uintptr \[cap] ? (addr ^+ /[12])
             * R }> m5).
  { unfold anyval in *.
    find_step (fun _ => lazymatch goal with
                        | |- exists _, _ => fail
                        | |- _ => idtac
                        end).
    eexists (Build_raw_ring_buf _ _ _ _).
    unfold raw_ring_buf_t. cbn -[sepapps].
    steps. puri_simpli_zify_hyps false. assumption. }
  steps. new_mem_hyp H2. steps.
Qed.

Ltac predicates_safe_to_cancel_hook hypPred conclPred ::=
  lazymatch conclPred with
  | raw_ring_buf_t ?b2 =>
      lazymatch hypPred with
      | raw_ring_buf_t ?b1 => tryif is_evar b2 then unify b1 b2 else idtac
      end
  end.

(* TODO can we infer injectivity of predicates automatically? *)
Lemma raw_ring_buf_t_inj: forall r1 r2 a,
    safe_implication (r1 = r2) (impl1 (raw_ring_buf_t r1 a) (raw_ring_buf_t r2 a)).
Proof. unfold safe_implication. intros. subst. reflexivity. Qed.

#[local] Hint Resolve raw_ring_buf_t_inj : safe_implication.

#[export] Instance spec_of_ring_buf_init: fnspec :=                              .**/

void ring_buf_init(uintptr_t addr, uintptr_t cap) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * array (uint 8) (12 + 4 * \[cap]) ? addr
                     * R }> m;
  ensures t' m' := t' = t /\
       <{ * ring_buf \[cap] nil addr
          * R }> m' #**/                                                   /**.
Derive ring_buf_init SuchThat (fun_correct! ring_buf_init) As ring_buf_init_ok. .**/
{                                                                          /**. .**/
  raw_ring_buf_init(addr, cap);                                            /**. .**/
  store32(addr + 4, 0);                                                    /**. .**/
  store32(addr + 8, 0);                                                    /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_ring_buf_enq: fnspec :=                              .**/

void ring_buf_enq(uintptr_t b_addr, uintptr_t v) /**#
  ghost_args := cap vs (R: mem -> Prop);
  requires t m := <{ * ring_buf cap vs b_addr
                     * R }> m /\
                  len vs < cap;
  ensures t' m' := t' = t /\
       <{ * ring_buf cap (vs ++ [|v|]) b_addr
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
