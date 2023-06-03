(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import bedrock2.to_from_anybytes.

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
          + anybytes (block_size - 4) }> p
     * fixed_size_free_list block_size q }> m ->
  fixed_size_free_list block_size p m.

Definition allocator: mem -> Prop :=
  ex1 (fun addr => <{
    * malloc_state_t {| free_list := addr |} /[malloc_state_ptr]
    * fixed_size_free_list malloc_block_size addr
  }>).

Definition allocator_cannot_allocate(n: word): mem -> Prop :=
  ex1 (fun addr => <{
    * malloc_state_t {| free_list := addr |} /[malloc_state_ptr]
    * fixed_size_free_list malloc_block_size addr
    * emp (addr = /[0] \/ (* empty free list *)
           malloc_block_size mod 2 ^ 32 < \[n]) (* trying to allocate more than supported *)
  }>).

Definition freeable(sz: Z)(a: word): mem -> Prop :=
  anybytes (malloc_block_size - sz) (a ^+ /[sz]).

Local Hint Extern 1 (cannot_purify (fixed_size_free_list _ _))
      => constructor : suppressed_warnings.
Local Hint Extern 1 (cannot_purify allocator)
      => constructor : suppressed_warnings.
Local Hint Extern 1 (cannot_purify (allocator_cannot_allocate _))
      => constructor : suppressed_warnings.
Local Hint Extern 1 (cannot_purify (freeable _ _))
      => constructor : suppressed_warnings.
Local Hint Extern 1 (PredicateSize_not_found (fixed_size_free_list _))
      => constructor : suppressed_warnings.

Local Hint Unfold allocator allocator_cannot_allocate : live_always_unfold.

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
           * anybytes \[n] p
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

    rename H5 into h.
    unfold with_mem in h.
    eapply cast_to_anybytes in h.
    2: { eauto with contiguous. }
    bottom_up_simpl_in_hyp h.
    change (with_mem m0 (anybytes malloc_block_size l)) in h.
                                                                                .**/
  } else {                                                                 /**. .**/
    /* empty */                                                            /**. .**/
  }                                                                        /**. .**/
  return p;                                                                /**. .**/
}                                                                          /**.
Abort.

#[export] Instance spec_of_free: fnspec :=                                      .**/

void free (uintptr_t p) /**#
  ghost_args := n (R: mem -> Prop);
  requires t m := <{ * allocator
                     * anybytes \[n] p
                     * freeable \[n] p
                     * R }> m;
  ensures t' m' := t' = t /\
                   <{ * allocator
                      * R }> m' #**/                                       /**.
Derive free SuchThat (fun_correct! free) As free_ok. Abort.

End LiveVerif. Comments .**/ //.
