(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import coqutil.Sorting.Permutation.
Require Import LiveVerif.LiveVerifLib. Load LiveVerif.

Hint Extern 4 (Permutation _ _) =>
  eauto using perm_nil, perm_skip, perm_swap, perm_trans
: prove_post.

#[export] Instance spec_of_sort3_separate_args: fnspec :=                      .**/

void sort3_separate_args(uintptr_t a0, uintptr_t a1, uintptr_t a2) /**#
  ghost_args := (R: mem -> Prop) in0 in1 in2;
  requires t m := <{ * uint 32 in0 a0
                     * uint 32 in1 a1
                     * uint 32 in2 a2
                     * R }> m;
  ensures t' m' := t' = t /\ exists out0 out1 out2,
            <{ * uint 32 out0 a0
               * uint 32 out1 a1
               * uint 32 out2 a2
               * R }> m' /\
            Permutation [| in0; in1; in2 |] [| out0; out1; out2 |] /\
            out0 <= out1 <= out2 #**/                                    /**.
Derive sort3_separate_args SuchThat (fun_correct! sort3_separate_args)
As sort3_separate_args_ok.                                                    .**/
{                                                                        /**. .**/
  uintptr_t w0 = load32(a0);                                             /**. .**/
  uintptr_t w1 = load32(a1);                                             /**. .**/
  uintptr_t w2 = load32(a2);                                             /**. .**/
  if (w1 <= w0 && w1 <= w2) {                                            /**. .**/
    store32(a0, w1);                                                     /**. .**/
    w1 = w0;                                                             /**. .**/
  } else {                                                               /**. .**/
    if (w2 <= w0 && w2 <= w1) {                                          /**. .**/
      store32(a0, w2);                                                   /**. .**/
      w2 = w0;                                                           /**. .**/
    } else {                                                             /**. .**/
    } /**. end if.                                                            .**/
  } /**. end if.                                                              .**/
  if (w2 < w1) {                                                         /**. .**/
    store32(a1, w2);                                                     /**. .**/
    store32(a2, w1);                                                     /**. .**/
  } else {                                                               /**. .**/
    store32(a1, w1);                                                     /**. .**/
    store32(a2, w2);                                                     /**. .**/
  } /**. end if.                                                              .**/
}                                                                        /*?.
step. step. step. step. step. step. step. step. step. step. step. step.
step.
step.
2: step.
(* TODO automate *)
Import coqutil.Tactics.ident_ops.
repeat match goal with
       | H: ?x = _ |- _ => ident_starts_with Def H; subst x
       end.
destruct_ifs.
all: bottom_up_simpl_in_goal.
all: eauto with prove_post.
Qed.

End LiveVerif. Comments .**/ //.
