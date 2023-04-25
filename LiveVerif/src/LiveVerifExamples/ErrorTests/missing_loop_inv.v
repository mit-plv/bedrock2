(* -*- eval: (load-file "../../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Ltac pose_err e ::= pose_err_silent e.

Load LiveVerif.

#[export] Instance spec_of_test_missing_loop_inv: fnspec := .**/

uintptr_t test_missing_loop_inv(uintptr_t px, uintptr_t py) /**#
  ghost_args := (R: mem -> Prop) x1 x2 y1 y2;
  requires t m := <{ * uint 32 (x1 + x2) px
                     * uint 32 (y1 + y2) py
                     * R }> m;
  ensures t' m' retv := t' = t /\
            <{ * uint 32 (x1 + x2) px
               * uint 32 (y1 + y2) py
               * R }> m' #**/                                              /**.
Derive test_missing_loop_inv SuchThat
   (fun_correct! test_missing_loop_inv) As test_missing_loop_inv_ok.            .**/
{                                                                          /**. .**/
  uintptr_t g = 0;                                                         /**. .**/
  uintptr_t i = 0;                                                         /**.

  assert_fails (idtac; .**/
  while (i < 10) /* decreases (10 - \[i]) */ {                             /** ).
  (* TODO also check that the error message makes sense *)
Abort.

End LiveVerif. Comments .**/ //.
