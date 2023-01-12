(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

#[export] Instance spec_of_swap: fnspec :=                                      .**/

void swap(uintptr_t a_addr, uintptr_t b_addr) /**#
  ghost_args := a b (R: mem -> Prop);
  requires t m := <{ * uint 32 a a_addr
                     * uint 32 b b_addr
                     * R }> m;
  ensures t' m' := t' = t /\
       <{ * uint 32 b a_addr
          * uint 32 a b_addr
          * R }> m' #**/                                                   /**.
Derive swap SuchThat (fun_correct! swap) As swap_ok.                            .**/
{                                                                          /**. .**/
  uintptr_t t = load(a_addr);                                              /**. .**/
  store(a_addr, load(b_addr));                                             /**. .**/
  store(b_addr, t);                                                        /**. .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
