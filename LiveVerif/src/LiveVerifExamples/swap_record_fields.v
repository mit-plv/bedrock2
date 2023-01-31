(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.swap.

Record foo_t := {
  fieldA: uint_t 32;
  fieldB: uint_t 32;
  fieldC: uint_t 32;
  fieldD: uint_t 32;
}.

Load LiveVerif.

Instance foo: RepPredicate foo_t := ltac:(create_predicate).

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
Qed.

  (* TODO: example where a loop uses a pointer to an element of an array inside a record
     instead of an index i into the array
     (and compare to VST's record field access automation) *)

End LiveVerif. Comments .**/ //.
