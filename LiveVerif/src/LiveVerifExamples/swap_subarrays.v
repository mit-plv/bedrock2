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
      <{ * array (uint 16) n l p
         * R }> m;
  ensures t' m' := t' = t /\
                  <{ * R * R (* TODO *) }> m' #**/                         /**.
Derive swap_subarrays SuchThat (fun_correct! swap_subarrays) As
  swap_subarrays_ok.                                                            .**/
{                                                                          /**. .**/
  swap_16s(p + 2 * i, p + 2 * j, count);                                   /*?.

  purify_heapletwise_hyps.

  assert (2 * n <= 2 ^ 32) by case TODO.
  assert (\[i] <= n) by ZnWords.
  assert (2 * \[i] <= 2 ^ 32) by (purify_heapletwise_hyps; ZnWords).

  step. step. step. step. step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step.
  step. step. step. step. step. step. step. step. step. step. step. step. step. step.

  lazymatch goal with
  | |- after_command ?fs ?rest ?t ?m ?l ?post =>
      change (wp_cmd fs rest t m l post)
  end.

  assert (\[i] <= n) by ZnWords.

(*clear H4 H2 H8 H5 H11 H6 H0.*)

  purify_heapletwise_hyps.

(* why are we getting these

\[/[2] ^* i] / 2

which can overflow if 2*i=2^width?
Not too bad.
How much is really needed to exclude 2*i=2^width, ie to have 2*i<2^width ?

problem: subarray of length 0 from pastend to pastend

computing the size of an array in bytes, computing the pastend pointer

size of an object should fit into a size_t / width-bit unsigned integer

therefore, need to disallow arrays that take up the whole memory space
*)


  assert (2 * \[i] <= 2 ^ 32) by (purify_heapletwise_hyps; ZnWords).

  (*assert (\[/[2] ^* i] <= n) by ZnWords.*)

  clear H4 H2 H8 H5 H11 H6 H0.


(*
 H10 : len l[\[/[2] ^* i] / 2 : \[/[2] ^* i] / 2 + \[count]] = \[count]
 needs to be simplified more!

Set Ltac Profiling.

Time bottom_up_simpl_in_hyps_and_vars.

Show Ltac Profile.
 *)
  Unshelve.
all: case TODO.
Qed.


End LiveVerif. Comments .**/ //.
