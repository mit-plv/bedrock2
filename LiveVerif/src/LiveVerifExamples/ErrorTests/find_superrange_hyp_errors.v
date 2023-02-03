(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Ltac pose_err e ::= pose_err_silent e.

Load LiveVerif.

Record bar_t{n: Z} := {
  barA: uint_t 16;
  barB: uint_t 16;
  barC: word;
  barPayload: array_t (uint_t 32) n;
}.
Arguments bar_t: clear implicits.

Instance bar(n: uint_t 32): RepPredicate (bar_t n) := ltac:(create_predicate).

#[export] Instance spec_of_swap_barAB: fnspec :=                                .**/

void swap_barAB(uintptr_t p) /**#
  ghost_args := n b (R: mem -> Prop);
  requires t m := <{ * bar n b p
                     * R }> m;
  ensures t' m' := t' = t /\
       <{ * bar n b{{ barA := barB b; barB := barA b }} p
          * R }> m' #**/                                                   /**.
Derive swap_barAB SuchThat (fun_correct! swap_barAB) As swap_barAB_ok.          .**/
{                                                                          /**. .**/
  uintptr_t tmp = load16(p+2);                                             /**.

  test_error Error:("Exactly one of the following subrange claims should hold:"
                      [|\[p ^+ /[2] ^- p] + 2 <= 8 + n * 4|]).

  clear Error.
  forget bar as bar'.

  step.
  test_error Error:("typeclasses eauto" "should find" (PredicateSize (bar' n b))).
Abort.

End LiveVerif. Comments .**/ //.
