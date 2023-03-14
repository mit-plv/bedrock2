(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.swap.

Record foo := {
  fieldA: Z;
  fieldB: Z;
  fieldC: Z;
  fieldD: Z;
}.

Load LiveVerif.

Definition foo_t(r: foo): word -> mem -> Prop := .**/
typedef struct __attribute__ ((__packed__)) {
  uint32_t fieldA;
  uint32_t fieldB;
  uint32_t fieldC;
  uint32_t fieldD;
} foo_t;
/**.

#[export] Instance spec_of_swap_bc: fnspec :=                                   .**/

void swap_bc(uintptr_t p) /**#
  ghost_args := f (R: mem -> Prop);
  requires t m := <{ * foo_t f p
                     * R }> m;
  ensures t' m' := t' = t /\
       <{ * foo_t f{{fieldB := fieldC f; fieldC := fieldB f}} p
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
