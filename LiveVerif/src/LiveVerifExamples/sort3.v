(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import coqutil.Sorting.Permutation.
Require Import LiveVerif.LiveVerifLib. Load LiveVerif.

Hint Extern 4 (Permutation _ _) =>
  eauto using perm_nil, perm_skip, perm_swap, perm_trans
: prove_post.

#[export] Instance spec_of_sort3: fnspec :=                                   .**/

void sort3(uintptr_t a) /**#
  ghost_args := (R: mem -> Prop) in1 in2 in3;
  requires t m := sep (array (uint 32) 3 [| in1; in2; in3 |] a) R m;
  ensures t' m' := t' = t /\ exists out1 out2 out3,
            sep (array (uint 32) 3 [| out1; out2; out3 |] a) R m' /\
            Permutation [| in1; in2; in3 |] [| out1; out2; out3 |] /\
            out1 <= out2 <= out3 #**/                                    /**.
Derive sort3 SuchThat (fun_correct! sort3) As sort3_ok.                       .**/
{                                                                        /**. .**/
  uintptr_t w0 = load32(a);                                              /**. .**/
  uintptr_t w1 = load32(a+4);                                            /**. .**/
  uintptr_t w2 = load32(a+8);                                            /**. .**/
  if (w1 <= w0 && w1 <= w2) {                                            /**. .**/
    store32(a, w1);                                                      /**. .**/
    w1 = w0;                                                             /**. .**/
  } else {                                                               /**. .**/
    if (w2 <= w0 && w2 <= w1) {                                          /**. .**/
      store32(a, w2);                                                    /**. .**/
      w2 = w0;                                                           /**. .**/
    } else {                                                             /**. .**/
    } /**. merge.                                                             .**/
  } /**. merge.                                                               .**/
  if (w2 < w1) {                                                         /**. .**/
    store32(a+4, w2);                                                    /**. .**/
    store32(a+8, w1);                                                    /**. .**/
  } else {                                                               /**. .**/
    store32(a+4, w1);                                                    /**. .**/
    store32(a+8, w2);                                                    /**. .**/
  }                                                                      /**. .**/
}                                                                        /**.
all: clear Error.
(* TODO automate *)
Import coqutil.Tactics.ident_ops.
all: repeat match goal with
       | H: ?x = _ |- _ => ident_starts_with Def H; subst x
       end.
all: destruct_ifs.
all: bottom_up_simpl_in_goal.
all: eauto with prove_post.
Qed.

End LiveVerif. Comments .**/ //.
