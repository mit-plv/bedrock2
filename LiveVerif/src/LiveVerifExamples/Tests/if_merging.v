(* -*- eval: (load-file "../../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Local Instance BW: .**/
ASSERT_BITWIDTH(32);
/**. constructor. Defined.

Load LiveVerif.

#[export] Instance spec_of_test_if: fnspec :=                                .**/

uintptr_t test_if(uintptr_t px, uintptr_t py) /**#
  ghost_args := (R: mem -> Prop) x1 x2 y1 y2;
  requires t m := <{ * uint 32 (x1 + x2) px
                     * uint 32 (y1 + y2) py
                     * R }> m;
  ensures t' m' retv := t' = t /\
            <{ * uint 32 (x1 + x2) px
               * uint 32 (y1 + y2) py
               * R }> m' #**/                                              /**.
Derive test_if SuchThat (fun_correct! test_if) As test_if_ok.                   .**/
{                                                                          /**. .**/
  uintptr_t r = 0;                                                         /**. .**/
  if (load32(px) < load32(py)) {                                           /**. .**/
    r = load32(px);                                                        /**. .**/
  } else {                                                                 /**. .**/
    r = load32(py);                                                        /**. .**/
  } /**.                                                                        .**/
  return r;                                                                /**. .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
