(* -*- eval: (load-file "../live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import coqutil.Tactics.syntactic_unify.

Load LiveVerif.

#[export] Instance spec_of_memset: fnspec :=                                    .**/

void memset(uintptr_t a, uintptr_t b, uintptr_t n) /**#
  ghost_args := bs (R: mem -> Prop);
  requires t m := <{ * array (uint 8) \[n] bs a
                     * R }> m /\
                  \[b] < 2 ^ 8;
  ensures t' m' := t' = t /\
       <{ * array (uint 8) \[n] (List.repeatz \[b] (len bs)) a
          * R }> m' #**/                                                   /**.
Derive memset SuchThat (fun_correct! memset) As memset_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t i = 0;                                                         /**.

  ltac1:(replace bs with (List.repeatz \[b] \[i] ++ bs[\[i]:]) in *
      by (subst i; (* TODO heurisits for when to inline vars *)
          bottom_up_simpl_in_goal;
          syntactic_exact_deltavar (@eq_refl _ _))).
  ltac1:(loop invariant above i).
  lazy_match! goal with [ h: _ < 2 ^ 8 |- _ ] => move $h before R end.
  assert (0 <= \[i] <= \[n]) by ltac1:(ZnWords).
  Std.clearbody [ @i ].
                                                                                .**/
  while (i < n) /* decreases (n ^- i) */ {                                 /**. .**/
    store1(a + i, b);                                                      /**. .**/
     i = i + 1;                                                            /**. (* .**/
  }                                                                        /**.
*)
Abort.

End LiveVerif. Comments .**/ //.
