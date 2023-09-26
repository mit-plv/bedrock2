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

Definition allocator_with_potential_failure(f: option Z): mem -> Prop :=
  ex1 (fun addr => <{
    * malloc_state_t {| free_list := addr |} /[malloc_state_ptr]
    * fixed_size_free_list malloc_block_size addr
    * emp (match f with
           | Some n => (* empty free list *)
                       addr = /[0] \/
                       (* trying to allocate more than supported *)
                       malloc_block_size < n
           | None => True
           end)
    * emp (8 <= malloc_block_size < 2 ^ 32)
  }>).

Definition allocator: mem -> Prop :=
  allocator_with_potential_failure None.
Definition allocator_cannot_allocate(n: Z): mem -> Prop :=
  allocator_with_potential_failure (Some n).

Definition allocator_failed_below(n: Z): mem -> Prop :=
  ex1 (fun amount => <{ * allocator_cannot_allocate amount
                        * emp (amount <= n) }>).

Lemma allocator_failed_below_monotone: forall n1 n2 m,
    n1 <= n2 ->
    allocator_failed_below n1 m ->
    allocator_failed_below n2 m.
Proof.
  unfold allocator_failed_below, ex1. intros. fwd. eexists.
  eapply sep_emp_r. eapply sep_emp_r in H0. destruct H0. split.
  - eassumption.
  - etransitivity; eassumption.
Qed.

Definition freeable(sz: Z)(a: word): mem -> Prop :=
  <{ * emp (a <> /[0]) (* TODO maybe this should be in array instead? *)
     * array (uint 8) (malloc_block_size - sz) ? (a ^+ /[sz]) }>.

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
  allocator_failed_below
  allocator_with_potential_failure
  freeable
: heapletwise_always_unfold.

Lemma recover_allocator_cannot_allocate: forall n,
    impl1 (allocator_cannot_allocate n) allocator.
Proof.
  unfold allocator_cannot_allocate, allocator, allocator_with_potential_failure.
  intros n m M. steps.
Qed.

Lemma recover_allocator_failed_below: forall n m,
    allocator_failed_below n m -> allocator m.
Proof.
  unfold allocator_failed_below. intros. destruct H as [amount H].
  eapply sep_emp_r in H. eapply recover_allocator_cannot_allocate. eapply H.
Qed.

#[export] Instance spec_of_malloc_init: fnspec :=                                .**/

uintptr_t malloc_init (uintptr_t p, uintptr_t n) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := 8 <= malloc_block_size < 2 ^ 32 /\
                  \[n] mod malloc_block_size = 0 /\
                  <{ * array (uint 8) (sizeof malloc_state_t) ? /[malloc_state_ptr]
                     * array (uint 8) \[n] ? p
                     * R }> m;
  ensures t' m' p := t' = t /\
        <{ * allocator
           * R }> m' #**/                                                     /**.
Derive malloc_init SuchThat (fun_correct! malloc_init) As malloc_init_ok.          .**/
{                                                                          /**. .**/
  store(malloc_state_ptr, p);                                              /**. .**/
  uintptr_t tail = NULL;                                                   /**. .**/
  uintptr_t head = p + n;                                                  /**.

  assert (\[n] = \[n] / malloc_block_size * malloc_block_size) as NAlt. {
    Z.div_mod_to_equations. (* <-- also adds eqs for non-const modulo *)
    lia.
  }
  assert (0 <= \[n] / malloc_block_size). {
    zify_goal.
    Z.div_mod_to_equations. (* <-- also adds eqs for non-const modulo *)
    lia.
  }
  forget (\[n] / malloc_block_size) as c.
  let h := find #(array (uint 8)) in rewrite NAlt in h.
  let h := find #(head = ??) in replace n with /[c * malloc_block_size] in Def1 by steps.
  pose proof (fixed_size_free_list_nil malloc_block_size tail map.empty
                ltac:(assumption) ltac:(unfold emp; auto)) as A.
  rewrite <- (mmap.du_empty_r m3) in D0.
  forget (map.empty (map := mem)) as m.
  change (m |= fixed_size_free_list malloc_block_size tail) in A.
  delete #(tail = ??).
  let h := find #(8 <= malloc_block_size) in move h after tail.
  delete #(?? mod malloc_block_size = 0).
  loop invariant above tail.
                                                                                .**/
  while (head != p) /* decreases c */ {                                    /**. .**/
    head = head - malloc_block_size;                                       /**. .**/
    store(head, tail);                                                     /**.
Abort.

#[export] Instance spec_of_malloc: fnspec :=                                    .**/

uintptr_t malloc (uintptr_t n) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * allocator
                     * R }> m;
  ensures t' m' p := t' = t /\
                     <{ * (if \[p] =? 0 then
                             allocator_failed_below \[n]
                           else
                             <{ * allocator
                                * array (uint 8) \[n] ? p
                                * freeable \[n] p }>)
                        * R }> m' #**/                                     /**.
Derive malloc SuchThat (fun_correct! malloc) As malloc_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t l = load(malloc_state_ptr);                                    /**. .**/
  if (l != 0 && n <= malloc_block_size) /* split */ {                      /**.

    let H := constr:(#(fixed_size_free_list ?? ??)) in inversion H; clear H.
    (* TODO better inversion tactic for such use cases *)
    1: congruence.
    repeat let lastHypType := lazymatch goal with _: ?t |- _ => t end in
           lazymatch lastHypType with
           | ?lhs = _ => subst lhs
           end.
    repeat heapletwise_step.
                                                                                .**/
    store(malloc_state_ptr, load(l));                                      /**.

    let H := constr:(#(array (uint 8))) in rename H into h.
    unfold with_mem in h.
    eapply cast_to_anybytes in h.
    2: { eauto with contiguous. }
    bottom_up_simpl_in_hyp h.
    lazymatch type of h with
    | ?p ?m => change (with_mem m p) in h
    end.
                                                                                .**/
    return l;                                                              /**. .**/
  }                                                                        /**.
    replace (\[l] =? 0) with false; steps.                                      .**/
  else {                                                                   /**. .**/
    return NULL;                                                           /**. .**/
  }                                                                        /**.
    replace (\[/[0]] =? 0) with true; steps.
    instantiate (1 := \[n]). 1-2: steps.
                                                                                .**/
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
  store(p, load(malloc_state_ptr));                                        /**. .**/
  store(malloc_state_ptr, p);                                              /**.

  discard_merge_step.
  epose proof (fixed_size_free_list_cons malloc_block_size p) as HL.
  lazymatch goal with
  | H: p <> /[0] |- _ => specialize HL with (1 := H)
  end.
  unfold sepapps, List.fold_right, proj_predicate, sepapp_sized_predicates,
    sepapp, sized_emp in HL.
  cancel_in_hyp HL.
                                                                                .**/
}                                                                          /**.
Qed.

End LiveVerif.

#[export] Hint Extern 1 (cannot_purify (freeable _ _))
      => constructor : suppressed_warnings.
#[export] Hint Extern 1 (PredicateSize_not_found (freeable _))
      => constructor : suppressed_warnings.
#[export] Hint Extern 1 (PredicateSize_not_found allocator_failed_below)
      => constructor : suppressed_warnings.
#[export] Hint Extern 1 (PredicateSize_not_found (@allocator _ _))
      => constructor : suppressed_warnings.
#[export] Hint Extern 1 (cannot_purify allocator)
      => constructor : suppressed_warnings.

Comments .**/ //.
