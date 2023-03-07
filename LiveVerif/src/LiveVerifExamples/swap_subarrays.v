(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Axiom TODO: False.

#[export] Instance spec_of_swap_16s: fnspec :=                                  .**/

void swap_16s(uintptr_t p1, uintptr_t p2, uintptr_t n) /**#
  ghost_args := (l1 l2: list (uint_t 16)) (R: mem -> Prop);
  requires t m := <{ * array (uint 16) \[n] l1 p1
                     * array (uint 16) \[n] l2 p2
                     * R }> m;
  ensures t' m' := t' = t /\
                  <{ * array (uint 16) \[n] l2 p1
                     * array (uint 16) \[n] l1 p2
                     * R }> m' #**/                                        /**.
Derive swap_16s SuchThat (fun_correct! swap_16s) As swap_16s_ok.                .**/
{                                                                          /**.
Unshelve. all: case TODO.
Qed.

#[export] Instance spec_of_swap_subarrays: fnspec :=                            .**/

void swap_subarrays(uintptr_t p, uintptr_t i, uintptr_t j, uintptr_t count) /**#
  ghost_args := (l: list (uint_t 16)) n (R: mem -> Prop);
  requires t m :=
      \[i] + \[count] <= \[j] /\
      \[j] + \[count] <= n /\
      2 * n < 2 ^ 32 /\ (*  <-- array size fits into a word, TODO add to array definition *)
      <{ * array (uint 16) n l p
         * R }> m;
  ensures t' m' := t' = t /\
                  <{ * R * R (* TODO *) }> m' #**/                         /**.
Derive swap_subarrays SuchThat (fun_correct! swap_subarrays) As
  swap_subarrays_ok.                                                            .**/
{                                                                          /**. .**/
  swap_16s(p + 2 * i, p + 2 * j, count);                                   /**.

  Unshelve.
all: case TODO.
Qed.

End LiveVerif. Comments .**/ //.
