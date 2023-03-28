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

  assert (len bs = \[n]) as lenbs by hwlia.
  let h := lazymatch goal with h: _ |= array _ _ _ _ |- _ => h end in
  replace bs with (List.repeatz \[b] \[i] ++ bs[\[i]:]) in h by steps.
  loop invariant above i.
  move lenbs before R.
  assert (0 <= \[i] <= \[n]) by steps.
  clearbody i.
                                                                                .**/
  while (i < n) /* decreases (n ^- i) */ {                                 /**. .**/
    store8(a + i, b);                                                      /**. .**/
     i = i + 1;                                                            /**. .**/
  }                                                                        /**.

  (* TODO in series of List.app, try to merge each pair of two adjacent lists *)
  unfold List.repeatz. subst i.
  replace (Z.to_nat \[i' ^+ /[1]]) with (Z.to_nat \[i'] + 1)%nat by steps.
  rewrite List.repeat_app.
  rewrite <- List.app_assoc.
  replace (\[i' ^+ /[1]]) with (\[i'] + 1) by steps.
  reflexivity.
                                                                                .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
