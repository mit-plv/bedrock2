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
  <{ * uintptr q p
     * anybytes block_size (p ^+ /[4])
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
           malloc_block_size < \[n]) (* trying to allocate more than supported *)
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

Local Hint Unfold allocator : live_always_unfold.

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
  uintptr_t l = load(malloc_state_ptr);                                    /**.
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
