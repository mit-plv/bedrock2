(* -*- eval: (load-file "../../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

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

Ltac check_for_warnings_hook ::= continue_if_warning.

#[export] Instance spec_of_superfluous_mem: fnspec :=                                .**/

void superfluous_mem(uintptr_t p) /**#
  ghost_args := n b (R1 R2: mem -> Prop);
  requires t m := <{ * bar n b p
                     * R1
                     * R2 }> m;
  ensures t' m' := t' = t /\
                   <{ * R1
                      * bar n b p
                     (* oops, forgot R2 *) }> m' #**/                      /**.
Derive superfluous_mem SuchThat (fun_correct! superfluous_mem) As
  superfluous_mem_ok.                                                           .**/
{                                                                          /**. .**/
}                                                                          /**.
(* Test that it does not infinitely go back and forth between find_hyp_for_range
   and canceling *)
Abort.

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
  uintptr_t tmp = load16(p-2);                                             /**.

  test_error Error:("Exactly one of the following claims should hold:"
          [|subrange (p ^- /[2]) 2 p (8 + n * 4); inrange p (p ^- /[2]) 2|]).

Abort.

Derive swap_barAB SuchThat (fun_correct! swap_barAB) As swap_barAB_ok.          .**/
{                                                                          /**.

  forget bar as bar'.                                                           .**/

  uintptr_t tmp = load16(p+2);                                             /**.

  lazymatch goal with
  | _: warning_marker (PredicateSize_not_found (bar' _ b)) |- _ => idtac
  end.
  test_error Error:("Exactly one of the following claims should hold:" nil).
Abort.

End LiveVerif. Comments .**/ //.
