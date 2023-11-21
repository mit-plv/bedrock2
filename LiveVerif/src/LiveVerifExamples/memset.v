(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Local Instance BW: .**/
ASSERT_BITWIDTH(32);
/**. constructor. Defined.

Load LiveVerif.

(*
Ltac log_packaged_context P ::=
  lazymatch P with
  | ?f _ _ _ _ => let c := eval cbv beta in (fun measure ti mi li => f measure ti mi li) in
                  idtac c
  end.
*)

#[export] Instance spec_of_Memset: fnspec :=                                    .**/

void Memset(uintptr_t a, uintptr_t b, uintptr_t n) /**#
  ghost_args := bs (R: mem -> Prop);
  requires t m := <{ * array (uint 8) \[n] bs a
                     * R }> m /\
                  \[b] < 2 ^ 8;
  ensures t' m' := t' = t /\
       <{ * array (uint 8) \[n] (List.repeatz \[b] \[n]) a
          * R }> m' #**/                                                   /**.
Derive Memset SuchThat (fun_correct! Memset) As Memset_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t i = 0;                                                         /**.

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
