(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Class malloc_constants := {
  malloc_base: Z;
  malloc_block_size: Z;
}.

Load LiveVerif.

Context {consts: malloc_constants}.

(*Fixpoint fixed_size_free_list(a: word): word -> Prop :=*)

Definition allocator: mem -> Prop. Admitted.
Definition freeable(sz: Z)(a: word): mem -> Prop. Admitted.

#[export] Instance spec_of_malloc: fnspec :=                                    .**/

uintptr_t malloc (uintptr_t n) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * allocator
                     * R }> m;
  ensures t' m' p := t' = t /\
     (p = /[0] /\
      <{ * allocator
         * R }> m') \/
     (p <> /[0] /\ exists bs,
      <{ * allocator
         * array (uint 8) \[n] bs p
         * freeable \[n] p
         * R }> m') #**/                                                   /**.
Derive malloc SuchThat (fun_correct! malloc) As malloc_ok.                  (*  .**/
{                                                                          /**. .**/
  uintptr_t x = malloc_base + b;                                           /**. .**/

  uintptr_t r = u_min(a, b);                                               /**. .**/
  uintptr_t s = u_min(r, c);                                               /**. .**/
  return s;                                                                /**. .**/
}                                                                          /**.
Qed.
*)
Abort.

End LiveVerif. Comments .**/ //.
