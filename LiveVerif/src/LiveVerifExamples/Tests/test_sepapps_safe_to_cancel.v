(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

Load LiveVerif.

#[export] Instance spec_of_pass_three: fnspec :=                                .**/

void pass_three(uintptr_t src) /**#
  ghost_args := (R: mem -> Prop) (w2 w3: word);
  (* using (w2 ^+ /[0]) to test the case when the value in a uintptr is not just
     an evar *)
  requires t m := <{ * <{ + uintptr /[42] + uintptr (w2 ^+ /[0]) + uintptr w3 }> src
                     * R }> m;
  ensures t' m' := t' = t /\ <{ * <{ + uintptr /[42] + uintptr w2 + uintptr w3 }> src
                                * R }> m'    #**/                          /**.
Derive pass_three SuchThat (fun_correct! pass_three) As pass_three_ok.                .**/
{                                                                          /**. .**/
}                                                                          /**.
Qed.

#[export] Instance spec_of_main: fnspec :=                                      .**/

void main( ) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := <{ * <{ + uintptr /[42] + uintptr /[7] + uintptr /[4] }> /[40000]
                     * R }> m;
  ensures t' m' := t' = t /\ <{ * <{ + uintptr /[42] + uintptr /[7] + uintptr /[4] }> /[40000]
                                * R }> m' #**/                             /**.
Derive main SuchThat (fun_correct! main) As main_ok.                            .**/
{                                                                          /**. .**/
  pass_three(40000);                                                       /**.
  (* checking that the sepapps in the precondition of pass_three is
     canceled by the caller's sepapps all at once *)
  Fail match goal with
  | H: context [ hole ] |- _ => idtac
  end. .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
