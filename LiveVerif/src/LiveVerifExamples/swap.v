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
  uintptr_t t = load32(a_addr);                                            /**. .**/
  store32(a_addr, load32(b_addr));                                         /**. .**/
  store32(b_addr, t);                                                      /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_swap_words: fnspec :=                                 .**/

void swap_words(uintptr_t a_addr, uintptr_t b_addr) /**#
  ghost_args := a b (R: mem -> Prop);
  requires t m := <{ * uintptr a a_addr
                     * uintptr b b_addr
                     * R }> m;
  ensures t' m' := t' = t /\
       <{ * uintptr b a_addr
          * uintptr a b_addr
          * R }> m' #**/                                                   /**.
Derive swap_words SuchThat (fun_correct! swap_words) As swap_words_ok.          .**/
{                                                                          /**. .**/
  uintptr_t t = load(a_addr);                                              /**.
  (* TODO: a should not get renamed into t, because it appears in pre and post *) .**/
  store(a_addr, load(b_addr));                                             /**. .**/
  store(b_addr, t);                                                        /**. .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
