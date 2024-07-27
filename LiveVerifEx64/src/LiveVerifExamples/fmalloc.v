(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
(* fmalloc: fixed-size malloc *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Record fmalloc_state_t := {
  block_size: Z;
  free_list: word;
}.

Definition fmalloc_state(s: fmalloc_state_t): word -> mem -> Prop := .**/

typedef struct __attribute__ ((__packed__)) {
  size_t block_size;
  uintptr_t free_list;
} fmalloc_state;

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
            + anyval (array (uint 8) (blk_size - sizeof uintptr)) }> a
       * fixed_size_free_list blk_size n' q }> m.
Proof.
  intros. destruct n; simpl in *.
  - unfold emp in H0. exfalso. apply proj2 in H0. congruence.
  - steps.
Qed.

Definition allocator(block_size nRemaining: Z)(outer_addr: word): mem -> Prop :=
  ex1 (fun addr => <{
    * fmalloc_state {| block_size := block_size; free_list := addr |} outer_addr
    * fixed_size_free_list block_size (Z.to_nat nRemaining) addr
    * emp (0 <= nRemaining /\ 2 * sizeof uintptr <= block_size < 2 ^ bitwidth)
  }>).

(* Note: size argument is ignored (but other implementations that allow different
   sizes might need it) *)
Definition freeable(sz: Z)(a: word): mem -> Prop :=
  emp (a <> /[0]). (* TODO maybe this should be in array instead? *)

Local Hint Extern 1 (cannot_purify (fixed_size_free_list _ _ _))
      => constructor : suppressed_warnings.
Local Hint Extern 1 (cannot_purify (allocator _ _ _))
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
  | fmalloc_state {| free_list := ?addr2 |} =>
      lazymatch hypPred with
      | fmalloc_state {| free_list := ?addr1 |} =>
          is_evar addr2; unify addr1 addr2
      end
  end.

#[export] Instance spec_of_fmalloc_init: fnspec :=                              .**/

void fmalloc_init(uintptr_t a, uintptr_t buf, uintptr_t blk_size, uintptr_t n) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := 2 * sizeof uintptr <= \[blk_size] /\
                  (* disallow wrap to avoid null pointers in free list: *)
                  \[buf] <> 0 /\ \[buf] + \[n] * \[blk_size] < 2 ^ bitwidth /\
                  <{ * array (uint 8) (sizeof fmalloc_state) ? a
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
  change n with nOrig at 2.
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

    assert (\[head ^- buf] + sizeof uintptr <= \[blk_size] * \[n']). {
      (* TODO can we automate this proof so that the assertion is not needed
         any more, because the subrange check that needs it finds it on its own? *)
      subst head.
      subst head'.
      bottom_up_simpl_in_goal.
      replace (blk_size ^* n' ^- blk_size) with (blk_size ^* (n' ^- /[1])) by ring.
      (* non-linear arithmetic! *)
      rewrite word.unsigned_mul_nowrap.
      2: {
        eapply Z.le_lt_trans. 2: eassumption.
        rewrite Z.mul_comm.
        etransitivity.
        1: eapply Z.mul_le_mono_nonneg_r. 1: solve [steps].
        1: instantiate (1 := \[nOrig]).
        all: steps.
      }
      replace \[n' ^- /[1]] with (\[n'] - 1) by steps. steps.
    }                                                                           .**/
    store(head, tail);                                                     /**. .**/
    tail = head;                                                           /**. .**/
  }                                                                        /**.
    unfold split_concl_at.
    replace (\[blk_size] * \[n]) with \[head ^- buf].
    2: {
      subst head head' n.
      bottom_up_simpl_in_goal.
      replace (blk_size ^* n' ^- blk_size) with (blk_size ^* (n' ^- /[1])) by ring.
      (* non-linear arithmetic! *)
      rewrite word.unsigned_mul_nowrap.
      2: {
        eapply Z.le_lt_trans. 2: eassumption.
        rewrite Z.mul_comm.
        etransitivity.
        1: eapply Z.mul_le_mono_nonneg_r. 1: solve [steps].
        1: instantiate (1 := \[nOrig]).
        all: steps.
      }
      steps.
    }
    step. step.
    replace (Z.to_nat (\[nOrig] - \[n])) with (S (Z.to_nat (\[nOrig] - \[n']))).
    2: {
      subst n. steps.
    }
    simpl fixed_size_free_list.
    steps.

    subst tail head head'.
    assert (0 < \[buf ^+ blk_size ^* n' ^- blk_size]).
    2: solve [steps].
    eapply Z.lt_le_trans with (m := \[buf]). 1: solve[steps].
    replace (buf ^+ blk_size ^* n' ^- blk_size)
      with (buf ^+ blk_size ^* (n' ^- /[1])) by ring.
    rewrite word.unsigned_add_nowrap. 1: solve[steps].
    (* non-linear arithmetic! *)
    eapply Z.le_lt_trans.
    2: eassumption.
    eapply (proj1 (Z.add_le_mono_l _ _ _)).
    rewrite Z.mul_comm.
    rewrite word.unsigned_mul_nowrap.
    2: {
      eapply Z.le_lt_trans. 2: eassumption.
      rewrite Z.mul_comm.
      etransitivity.
      1: eapply Z.mul_le_mono_nonneg_r. 1: solve [steps].
      1: instantiate (1 := \[nOrig]).
      all: steps.
    }
    eapply Z.mul_le_mono_nonneg_l; solve [steps].

    rewrite mmap.du_empty_l.
    lazymatch goal with
    | H: with_mem ?m (array _ ?n ? _) |- canceling nil (mmap.Def ?m) True =>
        replace n with 0 in H
    end.
    prove_emp_in_hyps. steps.
    subst head head' tail.
    bottom_up_simpl_in_goal.
    rewrite word.unsigned_sub_nowrap.
    2: {
      rewrite word.unsigned_mul_nowrap by nia.
      nia.
    }
    rewrite word.unsigned_mul_nowrap by nia.
    steps.
                                                                                .**/
  store(a, blk_size);                                                      /**. .**/
  store(a+sizeof(uintptr_t), tail);                                        /**.

  assert (n = /[0]) as Hn by steps.
  rewrite Hn in *|-.
  bottom_up_simpl_in_hyps.
  prove_emp_in_hyps.
  repeat heapletwise_step.
                                                                                .**/
}                                                                          /**.
  unfold fmalloc_state, split_concl_at.
  steps.
Qed.

#[export] Instance spec_of_fmalloc_has_space: fnspec :=                         .**/

uintptr_t fmalloc_has_space(uintptr_t al) /**#
  ghost_args := blk_size n_remaining (R: mem -> Prop);
  requires t m := <{ * allocator blk_size n_remaining al
                     * R }> m;
  ensures t' m' r := t' = t /\
                     ((\[r] = 0 /\ n_remaining = 0) \/ (\[r] = 1 /\ 0 < n_remaining)) /\
                     <{ * allocator blk_size n_remaining al
                        * R }> m' #**/                                     /**.
Derive fmalloc_has_space
  SuchThat (fun_correct! fmalloc_has_space) As fmalloc_has_space_ok.            .**/
{                                                                          /**. .**/
  uintptr_t l = load(al + sizeof(uintptr_t));                              /**. .**/
  return l != 0;                                                           /**.
  unfold expr.not. (* TODO support boolean operators in non-condition position *)
  steps.                                                                        .**/
}                                                                          /**.
  destr (word.eqb l /[0]); [left|right]; steps.
  - let H := constr:(#(fixed_size_free_list)) in eapply fixed_size_free_list_null in H.
    steps.
  - let H := constr:(#(fixed_size_free_list)) in eapply fixed_size_free_list_nonnull in H.
    2: assumption.
    steps. lia.
Qed.

#[export] Instance spec_of_fmalloc: fnspec :=                                   .**/

uintptr_t fmalloc(uintptr_t al) /**#
  ghost_args := blk_size n_remaining (R: mem -> Prop);
  requires t m := <{ * allocator blk_size n_remaining al
                     * R }> m;
  ensures t' m' p := t' = t /\
                     if \[p] =? 0 then
                       n_remaining = 0 /\
                       <{ * allocator blk_size 0 al
                          * R }> m'
                     else
                       <{ * allocator blk_size (n_remaining - 1) al
                          * array (uint 8) blk_size ? p
                          * freeable blk_size p
                          * R }> m' #**/                                  /**.
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
    let H := constr:(#fixed_size_free_list) in eapply fixed_size_free_list_null in H.
    steps.
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
#[export] Hint Extern 1 (cannot_purify (allocator _ _ _))
      => constructor : suppressed_warnings.

Comments .**/ //.
