(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

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

  prove (len bs = \[n]) as lenbs.
  move lenbs before t.
  swap bs with
    (List.repeatz \[b] \[i] ++ bs[\[i]:])
    in #(array (uint 8)).
  loop invariant above i.
  delete #(i = ??).
                                                                                .**/
  while (i < n) /* decreases (n ^- i) */ {                                 /**. .**/
    store8(a + i, b);                                                      /**. .**/
    i = i + 1;                                                             /**. .**/
  }                                                                        /**. .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
