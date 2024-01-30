(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
(* fmalloc: fixed-size malloc *)
Require Import LiveVerif.LiveVerifLib.

(* TODO move *)
(*
C                 Separation Logic   Description
----------------- ------------------ -----------------------------------------------------
uintptr_t         uintptr            32 or 64 bit, value is of type word
uint8/16/32/64_t  uint 8/16/32/64    value is of type Z, and predicate ensures bounds on Z
size_t            uint 32/64         value is of type Z, and predicate ensures bounds on Z
*)
Ltac exact_uint_of_bitwidth :=
  let bw := constr:(_ : Bitwidth _) in
  lazymatch type of bw with
  | Bitwidth ?w => exact (uint w)
  end.
Notation "'size_t'" := (ltac:(exact_uint_of_bitwidth))
  (in custom c_type_as_predicate, only parsing).

Load LiveVerif.

Record fmalloc_state := {
  block_size: Z;
  free_list: word;
}.

Definition fmalloc_state_t(s: fmalloc_state): word -> mem -> Prop := .**/

typedef struct __attribute__ ((__packed__)) {
  size_t block_size;
  uintptr_t free_list;
} fmalloc_state_t;

/**.

Section WithBlockSize.
  Context (block_size: Z).
  Fixpoint fixed_size_free_list(n: nat)(p: word): mem -> Prop :=
    match n with
    | O => emp (p = /[0])
    | S n' => EX q,
        <{ * emp (p <> /[0])
           * <{ + uintptr q
                + anyval (array (uint 8) (block_size - sizeof uintptr)) }> p
           * fixed_size_free_list n' q }>
    end.
End WithBlockSize.

Lemma fixed_size_free_list_nil: forall blk_size,
    fixed_size_free_list blk_size O /[0] map.empty.
Proof. intros. simpl. split; reflexivity. Qed.

Lemma fixed_size_free_list_null: forall blk_size n m,
    fixed_size_free_list blk_size n /[0] m ->
    emp (n = O) m.
Proof.
  intros. destruct n; simpl in *.
  - unfold emp in *. intuition congruence.
  - exfalso. steps. congruence.
Qed.

Lemma fixed_size_free_list_nonnull: forall blk_size n a m,
    a <> /[0] ->
    fixed_size_free_list blk_size n a m ->
    exists q n', n = S n' /\
    <{ * <{ + uintptr q
            + anyval (array (uint 8) (blk_size - sizeof(uintptr))) }> a
       * fixed_size_free_list blk_size n' q }> m.
Proof.
  intros. destruct n; simpl in *.
  - unfold emp in H0. exfalso. apply proj2 in H0. congruence.
  - steps.
Qed.

Definition allocator(block_size nRemaining: Z)(outer_addr: word): mem -> Prop :=
  ex1 (fun addr => <{
    * fmalloc_state_t {| block_size := block_size; free_list := addr |} outer_addr
    * fixed_size_free_list block_size (Z.to_nat nRemaining) addr
    * emp (0 <= nRemaining /\ 2 * sizeof uintptr <= block_size < 2 ^ bitwidth)
  }>).

(* Note: size argument is ignored (but other implementations that allow different
   sizes might need it) *)
Definition freeable(sz: Z)(a: word): mem -> Prop :=
  emp (a <> /[0]). (* TODO maybe this should be in array instead? *)

Local Hint Extern 1 (cannot_purify (fixed_size_free_list _ _ _))
      => constructor : suppressed_warnings.
Local Hint Extern 1 (cannot_purify allocator)
      => constructor : suppressed_warnings.
Local Hint Extern 1 (cannot_purify (freeable _ _))
      => constructor : suppressed_warnings.
Local Hint Extern 1 (PredicateSize_not_found (fixed_size_free_list _ _))
      => constructor : suppressed_warnings.

Local Hint Unfold
  allocator
  freeable
: heapletwise_always_unfold.

Ltac predicates_safe_to_cancel_hook hypPred conclPred ::=
  lazymatch conclPred with
  | fmalloc_state_t {| free_list := ?addr2 |} =>
      lazymatch hypPred with
      | fmalloc_state_t {| free_list := ?addr1 |} =>
          is_evar addr2; unify addr1 addr2
      end
  end.

Axiom TODO: False.

#[export] Instance spec_of_fmalloc_init: fnspec :=                              .**/

void fmalloc_init(uintptr_t a, uintptr_t buf, uintptr_t blk_size, uintptr_t n) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := 2 * sizeof uintptr <= \[blk_size] /\
                  (* disallow wrap to avoid null pointers in free list: *)
                  \[buf] + \[n] * \[blk_size] < 2 ^ bitwidth /\
                  <{ * array (uint 8) (sizeof fmalloc_state_t) ? a
                     * array (uint 8) (\[blk_size] * \[n]) ? buf
                     * R }> m;
  ensures t' m' := t' = t /\
        <{ * allocator \[blk_size] \[n] a
           * R }> m' #**/                                                  /**.
Derive fmalloc_init SuchThat (fun_correct! fmalloc_init) As fmalloc_init_ok.    .**/
{                                                                          /**. .**/
  uintptr_t tail = 0;                                                      /**. .**/
  uintptr_t head = buf + blk_size * n;                                     /**.

  pose proof (fixed_size_free_list_nil \[blk_size]) as A.
  rewrite <- (mmap.du_empty_r m3) in D.
  forget (map.empty (map := mem)) as mE.
  change (mE |= fixed_size_free_list \[blk_size] 0 /[0]) in A.
  swap /[0] with tail in A.
  delete #(tail = ??).
  let h := find #(?? + ?? < ??) in move h after tail.
  let h := find #(?? <= ??) in move h after tail.
  pose (nOrig := n). swap n with nOrig in #(?? < 2 ^ ??).
  swap O with (Z.to_nat (\[nOrig] - \[n])) in A.
  prove (0 <= \[n] <= \[nOrig]).
  swap nOrig with n in #(head = ??).
  clearbody nOrig.
  move n after tail.
  loop invariant above tail.
                                                                                .**/
  while (0 < n) /* decreases n */ {                                        /**. .**/
    head = head - blk_size;                                                /**. .**/
    n = n - 1;                                                             /**.

    assert (\[head ^- buf] + sizeof uintptr <= \[blk_size] * \[n'']). {
      (* TODO can we automate this proof so that the assertion is not needed
         any more, because the subrange check that needs it finds it on its own? *)
      subst head.
      subst head'.
      bottom_up_simpl_in_goal.
      zify_hyps.
      zify_goal.
      case TODO. (*
      assert (0 < \[n]) by lia.
      replace (/[c]) with (/[c-1] ^+ /[1]).
      2: solve [steps].
      bottom_up_simpl_in_goal.
      zify_goal.
      lia.*)
    }                                                                           .**/
    store(head, tail);                                                     /**. .**/
    tail = head;                                                           /**. .**/
  }                                                                        /*?.
    lazymatch goal with
    | H: merge_step _ |- _ => clear H
    end.
    steps.
    unzify.
(*
  store(a+sizeof(uintptr_t), buf);                                         /**. .**/
*)
(*
    assert (\[tail] <> 0). {
      subst.
      assert (0 < c) by lia.
      replace (/[c]) with (/[c-1] ^+ /[1]).
      2: solve [steps].
      bottom_up_simpl_in_goal.
      zify_goal.
      lia.

      zify_goal.
 by steps.
    2: {
    clear Error. unfold find_hyp_for_range.
    unzify.


assert (subrange head 4 p (c * malloc_block_size * 1)). {
  unfold subrange.
  subst head.
  subst head'.
  bottom_up_simpl_in_goal.

  clear Error.
  assert (0 < c) by lia.
  replace (/[c]) with (/[c-1] ^+ /[1]).
  2: solve [steps].
  bottom_up_simpl_in_goal.

  zify_goal.
  lia.

clear Error.
Search p.

jj
*)
  case TODO.
                                                                                .**/
}                                                                          /**.
  all: case TODO.
  Unshelve. try exact (word.of_Z 0).
Qed.

#[export] Instance spec_of_fmalloc: fnspec :=                                    .**/

uintptr_t fmalloc(uintptr_t al) /**#
  ghost_args := blk_size n_remaining (R: mem -> Prop);
  requires t m := <{ * allocator blk_size n_remaining al
                     * R }> m;
  ensures t' m' p := t' = t /\
                     (if \[p] =? 0 then
                        <{ * allocator blk_size 0 al
                           * R }>
                      else
                        <{ * allocator blk_size (n_remaining - 1) al
                           * array (uint 8) blk_size ? p
                           * freeable blk_size p
                           * R }>) m' #**/                                  /**.
Derive fmalloc SuchThat (fun_correct! fmalloc) As fmalloc_ok.                   .**/
{                                                                          /**. .**/
  uintptr_t l = load(al + sizeof(uintptr_t));                              /**. .**/
  if (l) /* split */ {                                                     /**.

    let H := constr:(#(fixed_size_free_list ?? ??)) in
    eapply fixed_size_free_list_nonnull in H.
    2: assumption. fwd. repeat heapletwise_step.
                                                                                .**/
    store(al + sizeof(uintptr_t), load(l));                                /**.

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
    replace (\[l] =? 0) with false; steps.
    replace (Z.to_nat (n_remaining - 1)) with n'; steps.                        .**/
  else {                                                                   /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**.
    replace (\[/[0]] =? 0) with true; steps.
    simpl fixed_size_free_list.
    let H := constr:(#fixed_size_free_list) in eapply fixed_size_free_list_null in H.
    steps.
                                                                                .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_fmalloc_free: fnspec :=                              .**/

void fmalloc_free (uintptr_t al, uintptr_t p) /**#
  ghost_args := blk_size n_remaining (R: mem -> Prop);
  requires t m := <{ * allocator blk_size n_remaining al
                     * array (uint 8) blk_size ? p
                     * freeable blk_size p
                     * R }> m;
  ensures t' m' := t' = t /\
                   <{ * allocator blk_size (n_remaining + 1) al
                      * R }> m' #**/                                       /**.
Derive fmalloc_free SuchThat
  (fun_correct! fmalloc_free) As fmalloc_free_ok.                               .**/
{                                                                          /**. .**/
  store(p, load(al+sizeof(uintptr_t)));                                    /**. .**/
  store(al+sizeof(uintptr_t), p);                                          /**. .**/
}                                                                          /**.
  replace (Z.to_nat (n_remaining + 1)) with (S (Z.to_nat n_remaining)) by lia.
  simpl fixed_size_free_list.
  prove_emp_in_hyps.
  steps.
Qed.

End LiveVerif.

#[export] Hint Extern 1 (cannot_purify (freeable _ _))
      => constructor : suppressed_warnings.
#[export] Hint Extern 1 (PredicateSize_not_found (freeable _))
      => constructor : suppressed_warnings.
#[export] Hint Extern 1 (PredicateSize_not_found (allocator _ _))
      => constructor : suppressed_warnings.
#[export] Hint Extern 1 (cannot_purify (allocator _ _))
      => constructor : suppressed_warnings.

Comments .**/ //.
