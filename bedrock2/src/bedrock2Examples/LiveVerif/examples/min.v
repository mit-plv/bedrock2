(* -*- eval: (load-file "../live_verif_setup.el"); -*- *)
Require Import bedrock2Examples.LiveVerif.LiveVerifLib. Load LiveVerif.

#[export] Instance spec_of_u_min: fnspec :=                                     .**/

uintptr_t u_min (uintptr_t a, uintptr_t b) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := R m;
  ensures t' m' retv := t' = t /\ R m' /\
      (\[a] < \[b] /\ retv = a \/ \[b] <= \[a] /\ retv = b) #**/           /**.
Derive u_min SuchThat (fun_correct! u_min) As u_min_ok.                         .**/
{                                                                          /**. .**/
  uintptr_t r = 0;                                                         /**. .**/
  if (a < b) {                                                             /**. .**/
    r = a;                                                                 /**. .**/
  } else {                                                                 /**. .**/
    r = b;                                                                 /**. .**/
  }                                                                        /**. .**/
  return r;                                                                /**. .**/
}                                                                          /**.
Defined.

Definition minl: list Z -> Z := List.fold_right Z.min 0.

Import LiveSnippet.

#[export] Instance spec_of_u_min3: fnspec :=                                    .**/

uintptr_t u_min3 (uintptr_t a, uintptr_t b, uintptr_t c) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := R m;
  ensures t' m' retv := t' = t /\ R m' /\
      \[retv] = minl [| \[a]; \[b]; \[c] |] #**/                           /**.
Derive u_min3 SuchThat (fun_correct! u_min3) As u_min3_ok.                      .**/
{                                                                          /**. .**/
  uintptr_t r = u_min(a, b);                                               /**.

  clear Error.
  (* TODO make start_canceling work if just one R, or better, specialcase memoryless
     functions with m'=m in postcondition? *)
  ltac1:(lazymatch goal with
         | |- ?F ?m /\ ?Rest =>
             let clauselist := reify_seps F in change (seps clauselist m /\ Rest);
             eapply canceling_start_and; [reflexivity| ]
         end).
  step.
  intros.
  ltac1:(fwd).
  step. step. step.

Abort.

End LiveVerif. Comments .**/ //.
