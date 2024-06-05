(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Definition sorted(vs: list word): Prop :=
  forall i j, 0 <= i -> i < j -> j < len vs -> \[vs[i]] <= \[vs[j]].

#[export] Instance spec_of_bsearch: fnspec :=                                   .**/

uintptr_t bsearch(uintptr_t a, uintptr_t n, uintptr_t v, uintptr_t idxp) /**#
  ghost_args := vs (R: mem -> Prop);
  requires t m := <{ * array uintptr \[n] vs a
                     * uintptr ? idxp
                     * R }> m /\
                  sorted vs;
  ensures t' m' r := t' = t /\ exists i,
      ((r = /[1] /\ vs[\[i]] = v) \/ (r = /[0] /\ ~ List.In v vs)) /\
       <{ * array uintptr \[n] vs a
          * uintptr i idxp
          * R }> m' #**/                                                   /**.
Derive bsearch SuchThat (fun_correct! bsearch) As bsearch_ok.                   .**/
{                                                                          /**.
  unfold anyval in *. repeat heapletwise_step. rename v0 into i0.               .**/
  if (n == 0) /* split */ {                                                /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**.
    right. step. step. destruct vs. 2: discriminate. intro C. inversion C.      .**/
  else {                                                                   /**. .**/
  uintptr_t lo = 0;                                                        /**. .**/
  uintptr_t hi = n - 1;                                                    /**. .**/
  uintptr_t ret = 0;                                                       /**.

  prove (0 <= \[lo] /\ \[lo] <= \[hi] /\ \[hi] < \[n]).
  delete #(ret = ??).
  delete #(lo = ??).
  delete #(hi = ??).
  delete #(n <> /[0]).
  loop invariant above lo.
  (* TODO why are these moves needed if we don't want old memory predicates
     to be visible in loop body? *)
  move H0 after Scope4. move H2 after H0. move H3 after H2. move D after H2.

                                                                                .**/
  while (lo < hi) /* decreases (hi^-lo) */ {                               /**. .**/
    uintptr_t mid = (lo + hi)/2;                                           /**. .**/
    uintptr_t midv = load(a + mid * sizeof(uintptr_t));                    /**.

    assert (subrange (a ^+ mid ^* /[4]) 4 a (\[n] * 4)). {
      clear Error.
      unfold subrange.
      subst mid.
      bottom_up_simpl_in_goal.
      (* if we use indices, there's actually no risk for overflow because they
         are at least 4x smaller than 2^32 *)
(*
    if (mid == v) /* split */ {                                            /**. .**/
      ret = 1;                                                             /**. .**/
    }                                                                      /**. .**/


else {                                                               /**. .**/
      if (v < mid) /* split */ {                                           /**. .**/
        hi = mid;                                                          /**. .**/
      } else {                                                             /**. .**/
        lo = mid;                                                          /**. .**/
      }                                                                    /**. .**/
    }                                                                      /**. .**/
  }                                                                        /**. .**/

  return ret;
*)
Abort.

End LiveVerif. Comments .**/ //.
