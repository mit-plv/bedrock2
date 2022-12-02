(* -*- eval: (load-file "../live_verif_setup.el"); -*- *)
Require Import bedrock2Examples.LiveVerif.LiveVerifLib. Load LiveVerif.

#[export] Instance spec_of_u_min: fnspec :=                                     .**/

uintptr_t u_min (uintptr_t a, uintptr_t b) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := R m;
  ensures t' m' retv := t' = t /\ R m' /\
      (\[a] < \[b] /\ retv = a \/ \[b] <= \[a] /\ retv = b) #**/           /**.
Derive u_min SuchThat (fun_correct! u_min) As u_min_ok.                         .**/
{                                                                          /**. .**/
  uintptr_t r = 0;                                                         /**. .**/
  if (a < b) {                                                             /**. .**/
    r = a;                                                                 /**. .**/
  } else {                                                                 /**. .**/
    r = b;                                                                 /**. .**/
  }                                                                        /**. .**/
  return r;                                                                /**. .**/
}                                                                          /**.
Defined.

End LiveVerif. Comments .**/ //.
