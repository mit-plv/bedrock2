(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.swap.

Record foo_t := {
  fieldA: Z;
  fieldB: Z;
  fieldC: Z;
  fieldD: Z;
}.

Load LiveVerif.

Definition foo(r: foo_t): word -> mem -> Prop := record!
  (cons (mk_record_field_description fieldA (uint 32))
  (cons (mk_record_field_description fieldB (uint 32))
  (cons (mk_record_field_description fieldC (uint 32))
  (cons (mk_record_field_description fieldD (uint 32)) nil)))).

#[export] Instance spec_of_swap_bc: fnspec :=                                   .**/

void swap_bc(uintptr_t p) /**#
  ghost_args := f (R: mem -> Prop);
  requires t m := <{ * foo f p
                     * R }> m;
  ensures t' m' := t' = t /\
       <{ * foo f{{fieldB := fieldC f; fieldC := fieldB f}} p
          * R }> m' #**/                                                   /**.
Derive swap_bc SuchThat (fun_correct! swap_bc) As swap_bc_ok.                   .**/
{                                                                          /**. .**/
  swap(p+4, p+8);                                                          /**. .**/
} /**.
reflexivity. (* TODO automate, but don't use reflexivity in the library, because
  especially on unprovable goals with evars, it can run forever *)
Qed.

  (* TODO: example where a loop uses a pointer to an element of an array inside a record
     instead of an index i into the array
     (and compare to VST's record field access automation) *)

End LiveVerif. Comments .**/ //.
