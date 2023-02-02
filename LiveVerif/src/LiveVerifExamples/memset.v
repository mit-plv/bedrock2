(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
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
       <{ * array (uint 8) \[n] (List.repeatz \[b] \[n]) a
          * R }> m' #**/                                                   /**.
Derive memset SuchThat (fun_correct! memset) As memset_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t i = 0;                                                         /**.

  assert (len bs = \[n]) as lenbs by bottom_up_simpl_sidecond_hook.
  let h := lazymatch goal with h: _ |= array _ _ _ _ |- _ => h end in
  replace bs with (List.repeatz \[b] \[i] ++ bs[\[i]:]) in h
      by (subst i; (* TODO heurisits for when to inline vars *)
          bottom_up_simpl_in_goal;
          syntactic_exact_deltavar (@eq_refl _ _)).
  loop invariant above i.
  move lenbs before R.
  lazymatch goal with h: _ < 2 ^ 8 |- _ => move h before R end.
  assert (0 <= \[i] <= \[n]) by ZnWords.
  clearbody i.
                                                                                .**/
  while (i < n) /* decreases (n ^- i) */ {                                 /**. .**/
    store8(a + i, b);                                                      /**. .**/
     i = i + 1;                                                            /**.

     (* TODO if canceling is on same range with different values, assert
        equality between values and automate proving list equality.
        Here, little hope for a canonical form that both sides can reach. *)
     1: replace (List.repeatz \[b] \[i'] ++ \[b] :: bs[\[i'] + 1:]) with
             (List.repeatz \[b] \[i' ^+ /[1]] ++ bs[\[i' ^+ /[1]]:]) in *.
     2: {
       unfold List.repeatz.
       replace (Z.to_nat \[i' ^+ /[1]]) with (Z.to_nat \[i'] + 1)%nat by ZnWords.
       rewrite List.repeat_app.
       rewrite <- List.app_assoc.
       replace (\[i' ^+ /[1]]) with (\[i'] + 1) by ZnWords.
       reflexivity.
     }
                                                                                .**/
  } /**. end while.                                                             .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
