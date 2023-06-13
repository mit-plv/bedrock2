(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Class malloc_constants := {
  malloc_state_ptr: Z;
  malloc_block_size: Z;
}.

Load LiveVerif.

Record malloc_state := {
  free_list: word;
}.

Definition malloc_state_t(s: malloc_state): word -> mem -> Prop := .**/

typedef struct __attribute__ ((__packed__)) {
  uintptr_t free_list;
} malloc_state_t;

/**.

Context {consts: malloc_constants}.

(* The Inductive conveniently provides the fuel needed for the recursion *)
Inductive fixed_size_free_list(block_size: Z): word -> mem -> Prop :=
| fixed_size_free_list_nil p m:
  p = /[0] ->
  emp True m ->
  fixed_size_free_list block_size p m
| fixed_size_free_list_cons p q m:
  p <> /[0] ->
  <{ * <{ + uintptr q
          + anyval (array (uint 8) (block_size - 4)) }> p
     * fixed_size_free_list block_size q }> m ->
  fixed_size_free_list block_size p m.

Definition allocator_with_potential_failure(f: option word): mem -> Prop :=
  ex1 (fun addr => <{
    * malloc_state_t {| free_list := addr |} /[malloc_state_ptr]
    * fixed_size_free_list malloc_block_size addr
    * emp (match f with
           | Some n => (* empty free list *)
                       addr = /[0] \/
                       (* trying to allocate more than supported *)
                       malloc_block_size < \[n]
           | None => True
           end)
    * emp (8 <= malloc_block_size < 2 ^ 32)
  }>).

Definition allocator: mem -> Prop :=
  allocator_with_potential_failure None.
Definition allocator_cannot_allocate(n: word): mem -> Prop :=
  allocator_with_potential_failure (Some n).

Definition freeable(sz: Z)(a: word): mem -> Prop :=
  array (uint 8) (malloc_block_size - sz) ? (a ^+ /[sz]).

Local Hint Extern 1 (cannot_purify (fixed_size_free_list _ _))
      => constructor : suppressed_warnings.
Local Hint Extern 1 (cannot_purify allocator)
      => constructor : suppressed_warnings.
Local Hint Extern 1 (cannot_purify (allocator_cannot_allocate _))
      => constructor : suppressed_warnings.
Local Hint Extern 1 (cannot_purify (allocator_with_potential_failure _))
      => constructor : suppressed_warnings.
Local Hint Extern 1 (cannot_purify (freeable _ _))
      => constructor : suppressed_warnings.
Local Hint Extern 1 (PredicateSize_not_found (fixed_size_free_list _))
      => constructor : suppressed_warnings.

Local Hint Unfold
  allocator
  allocator_cannot_allocate
  allocator_with_potential_failure
  freeable
: heapletwise_always_unfold.

Lemma recover_allocation_failure: forall n,
    impl1 (allocator_cannot_allocate n) allocator.
Proof.
  unfold allocator_cannot_allocate, allocator, allocator_with_potential_failure.
  intros n m M. steps.
Qed.

#[export] Instance spec_of_malloc: fnspec :=                                    .**/

uintptr_t malloc (uintptr_t n) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * allocator
                     * R }> m;
  ensures t' m' p := t' = t /\
     (if \[p] =? 0 then
        <{ * allocator_cannot_allocate n
           * R }> m'
      else
        <{ * allocator
           * array (uint 8) \[n] ? p
           * freeable \[n] p
           * R }> m') #**/                                                   /**.
Derive malloc SuchThat (fun_correct! malloc) As malloc_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t l = load(malloc_state_ptr);                                    /**. .**/
  uintptr_t p = 0;                                                         /**. .**/
  if (l != 0 && n <= malloc_block_size) {                                  /**.

    let H := constr:(#(fixed_size_free_list ?? ??)) in inversion H; clear H.
    (* TODO better inversion tactic for such use cases *)
    1: congruence.
    repeat let lastHypType := lazymatch goal with _: ?t |- _ => t end in
           lazymatch lastHypType with
           | ?lhs = _ => subst lhs
           end.
    repeat heapletwise_step.
                                                                                .**/
    store(malloc_state_ptr, load(l));                                      /**. .**/
    p = l;                                                                 /**.

    let H := constr:(#(array (uint 8))) in rename H into h.
    unfold with_mem in h.
    eapply cast_to_anybytes in h.
    2: { eauto with contiguous. }
    bottom_up_simpl_in_hyp h.
    lazymatch type of h with
    | ?p ?m => change (with_mem m p) in h
    end.
                                                                                .**/
  } else {                                                                 /**. .**/
    /* empty */                                                            /**. .**/
  }                                                                        /**. .**/
  return p;                                                                /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_free: fnspec :=                                      .**/

void free (uintptr_t p) /**#
  ghost_args := n (R: mem -> Prop);
  requires t m := <{ * allocator
                     * array (uint 8) \[n] ? p
                     * freeable \[n] p
                     * R }> m;
  ensures t' m' := t' = t /\
                   <{ * allocator
                      * R }> m' #**/                                       /**.
Derive free SuchThat (fun_correct! free) As free_ok.                            .**/
{                                                                          /**.
  pose proof merge_anyval_array as M.
  specialize M with (addr :=  p).
  start_canceling_in_hyp M.
  canceling_step_in_hyp M.
  rewrite Z.mul_1_l in M.
  rewrite word.of_Z_unsigned in M.
  canceling_step_in_hyp M.
  eapply canceling_done_in_hyp in M.
  destruct M as (?m, (?D, ?H)).
  bottom_up_simpl_in_hyp H.
                                                                                .**/
  uintptr_t x = load(malloc_state_ptr);                                    /**. .**/
  store(p, x);                                                             /**.
(*
 .**/
  store(p, load(malloc_state_ptr));                                        /**. .**/
*)

Abort.

End LiveVerif. Comments .**/ //.
