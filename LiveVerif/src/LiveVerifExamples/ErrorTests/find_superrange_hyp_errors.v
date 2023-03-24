(* -*- eval: (load-file "../../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Ltac pose_err e ::= pose_err_silent e.

Load LiveVerif.

Record bar_t := {
  barA: Z;
  barB: Z;
  barC: word;
  barPayload: list Z;
}.
Arguments bar_t: clear implicits.

Definition bar(n: Z)(b: bar_t): word -> mem -> Prop := record!
  (cons (mk_record_field_description barA (uint 16))
  (cons (mk_record_field_description barB (uint 16))
  (cons (mk_record_field_description barC uintptr)
  (cons (mk_record_field_description barPayload (array (uint 32) n)) nil)))).

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
