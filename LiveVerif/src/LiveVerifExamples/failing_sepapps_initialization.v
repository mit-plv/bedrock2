(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import LiveVerifExamples.onesize_malloc.

Load LiveVerif.

Context {word_map: map.map word word}.
Context {word_map_ok: map.ok word_map}.

Context {consts: malloc_constants}.

(* This file showcases a scenario where the framework cannot automatically prove
   that we properly initialized a record for which we allocated memory using `Malloc`.

   Inspired by what came up in the crit-bit tree verification. *)

#[export] Instance spec_of_allocate_two: fnspec :=                        .**/

uintptr_t allocate_two( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * allocator * R }> m;
  ensures t' m' res := t' = t
           /\ <{ * (if \[res] =? 0 then
                     allocator_failed_below 8
                    else
                     <{ * allocator
                        * freeable 8 res
                        * <{ + uintptr /[0]
                             + uintptr /[0] }> res }>)
                 * R }> m' #**/                                            /**.
Derive allocate_two SuchThat (fun_correct! allocate_two)
  As allocate_two_ok.                                                           .**/
{                                                                          /**. .**/
  uintptr_t p = Malloc(2 * sizeof(uintptr_t));                             /**. .**/
  if (p == 0) /* split */ {                                                /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**.
  replace \[/[0]] with 0 in * by hwlia.
  change (0 =? 0) with true in *. cbv iota in *. steps. .**/
  else {                                                                   /**.
  replace (\[p] =? 0) with false in * by hwlia. .**/
    store(p, 0);                                                           /**. .**/
    store(p + 4, 0);                                                       /**. .**/
    return p;                                                              /**. .**/
  }                                                                        /**.
  replace (\[p] =? 0) with false in * by hwlia. steps.
  assert_fails (
                                                                                .**/
}                                                                          /**).
Abort.
