(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

#[export] Instance spec_of_Memcpy: fnspec :=                                    .**/

void Memcpy(uintptr_t dst, uintptr_t src, uintptr_t n) /**#
  ghost_args := srcData oldDstData (R: mem -> Prop);
  requires t m :=
      <{ * array (uint 8) \[n] oldDstData dst
         * array (uint 8) \[n] srcData src
         * R }> m;
  ensures t' m' := t' = t /\
      <{ * array (uint 8) \[n] srcData dst
         * array (uint 8) \[n] srcData src
         * R }> m' #**/                                                    /**.
Derive Memcpy SuchThat (fun_correct! Memcpy) As Memcpy_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t i = 0;                                                         /**.

  prove (len srcData = \[n]) as L1. move L1 before t.
  prove (len oldDstData = \[n]) as L2. move L2 before t.
  swap oldDstData with (srcData[:\[i]] ++ oldDstData[\[i]:]) in #(dst).
  loop invariant above i.
  delete #(i = ??).
                                                                                .**/
  while (i < n) /* decreases (n ^- i) */ {                                 /**. .**/
    store8(dst + i, load8(src + i));                                       /**.

    (* TODO automate *)
    bottom_up_simpl_in_goal. assumption.
                                                                                .**/
    i = i + 1;                                                             /**. .**/
  }                                                                        /**. .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
