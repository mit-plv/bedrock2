(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

#[export] Instance spec_of_pass_two: fnspec :=                                  .**/

void pass_two(uintptr_t src) /**#
  ghost_args := (R: mem -> Prop) (w1 w2: word);
  requires t m := <{ * <{ + uintptr (w1 ^+ /[1]) + uintptr w2 }> src
                     * R }> m;
  ensures t' m' := t' = t /\ <{ * <{ + uintptr (w1 ^+ /[1]) + uintptr w2 }> src
                                * R }> m'    #**/                          /**.
Derive pass_two SuchThat (fun_correct! pass_two) As pass_two_ok.                .**/
{                                                                          /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_main: fnspec :=                                      .**/

void main( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * <{ + uintptr /[3] + uintptr /[7] }> /[40000]
                     * <{ + uintptr /[103] + uintptr /[107] }> /[50000]
                     * R }>m;
  ensures t' m' := True #**/                                               /**.
Derive main SuchThat (fun_correct! main) As main_ok.                            .**/
{                                                                          /**. .**/
  pass_two(40000);                                                         /**.
  (* now when the uintptr value in the conclusion isn't a pure evar but instead
     `?evar ^+ /[1]`, we again don't cancel the entire sepapps at once as we'd like to *)

(*

processing the `Admitted.` below causes

Error:
Backtrace:

Backtrace:

Anomaly "in Lemmas.save_lemma_admitted: more than one statement."
Please report at http://coq.inria.fr/bugs/.

(vvvvvvv that one; using `Abort.` instead works)

Admitted.

*)
Abort.


End LiveVerif. Comments .**/ //.
