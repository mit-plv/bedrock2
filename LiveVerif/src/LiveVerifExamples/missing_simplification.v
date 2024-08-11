(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

Context {word_map: map.map word word}.
Context {word_map_ok: map.ok word_map}.

(* This file showcases scenarios where the framework cannot automatically prove
   something because it misses a simplification involving word and/or Z.

   Inspired by what came up in the crit-bit tree verification. *)

#[export] Instance spec_of_return_zero: fnspec :=                                   .**/

uintptr_t return_zero( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := True;
  ensures t' m' res := t' = t
           /\ <{ * (if \[res] =? 0 then emp True else emp False) * R }> m'
           #**/                         /**.
Derive return_zero SuchThat (fun_correct! return_zero)
  As return_zero_ok.                                                                .**/
{                                                                              /**. .**/
  return 0;                                                                    /**. .**/
}                                                                              /*?.
  step. step. step.

  (* the condition of the `if` should simplify here *)
  assert_fails step.
Abort.

#[export] Instance spec_of_zero_out: fnspec :=                                      .**/

void zero_out(uintptr_t p) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * (if \[p] =? 0 then emp True else EX v, uintptr v p) * R  }> m;
  ensures t' m' := t' = t
           /\ <{ * (if \[p] =? 0 then emp True else uintptr /[0] p)
                 * R }> m' #**/                                                /**.
Derive zero_out SuchThat (fun_correct! zero_out)
  As zero_out_ok.                                                                   .**/
{                                                                              /**. .**/
  if (p != 0) /* split */ {                                                    /**. .**/
    store(p, 0);                                                               /**.
  (* this should actually work without errors *)
  match goal with
  | H: tactic_error _ |- _ => clear H
  end.
  replace (\[p] =? 0) with false in * by hwlia.
  steps. .**/
  }                                                                            /**. .**/
  else {                                                                       /**. .**/
  }                                                                            /**.
  (* this should be immediately `ready` *)
  Fail
    match goal with
    | |- ready => idtac
    end.
  replace (\[p] =? 0) with true in * by hwlia.
  replace (0 =? 0) with true in * by hwlia.
  steps.                                                                            .**/
}                                                                              /**.
Qed.
