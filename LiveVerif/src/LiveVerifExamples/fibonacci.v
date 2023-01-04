(* -*- eval: (load-file "../live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.
Require Import coqutil.Tactics.let_binding_to_eq.

Load LiveVerif.

Fixpoint fib_nat(n: nat): nat :=
  match n with
  | O => O
  | S m => match m with
           | O => 1
           | S k => fib_nat k + fib_nat m
           end
  end.

Definition fib(n: word): word := /[Z.of_nat (fib_nat (Z.to_nat \[n]))].

Set Default Proof Mode "Classic".

Lemma fib_recursion: forall n,
    0 < \[n] ->
    \[n] + 1 < 2 ^ 32 ->
    fib (n ^+ /[1]) = fib (n ^- /[1]) ^+ fib n.
Proof.
  unfold fib. intros.
  replace (Z.to_nat \[n ^+ /[1]]) with (S (S (pred (Z.to_nat \[n])))) by ZnWords.
  replace (Z.to_nat \[n ^- /[1]]) with (pred (Z.to_nat \[n])) by ZnWords.
  replace (Z.to_nat \[n]) with (S (pred (Z.to_nat \[n]))) at 3 by ZnWords.
  forget (pred (Z.to_nat \[n])) as m.
  change (fib_nat (S (S m))) with (fib_nat m + fib_nat (S m))%nat.
  ZnWords.
Qed.

Set Default Proof Mode "Ltac2".

#[export] Instance spec_of_fibonacci: fnspec :=                                 .**/

uintptr_t fibonacci(uintptr_t n) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := sep (emp True) R m;
  ensures t' m' res := t' = t /\ sep (emp True) R m' /\ res = fib n #**/   /**.
Derive fibonacci SuchThat (fun_correct! fibonacci) As fibonacci_ok.             .**/
{                                                                          /**. .**/
  uintptr_t b = 0;                                                         /**. .**/
  if (n == 0) {                                                            /**. .**/
  } else {                                                                 /**. .**/
    uintptr_t a = 0;                                                       /**. .**/
    b = 1;                                                                 /**. .**/
    uintptr_t i = 1;                                                       /**.

    1: ltac1:(
    let_bindings_to_eqs;
    replace /[0] with (fib (i ^- /[1])) in Ha by
        (subst; unfold fib; bottom_up_simpl_in_goal; reflexivity);
    replace /[1] with (fib i) in Hb by
        (subst; unfold fib; bottom_up_simpl_in_goal; reflexivity);
    assert (1 <= \[i] <= \[n]) by ZnWords;
    eqs_to_let_bindings;
    clearbody i; move b after a).

    loop invariant above i.                                                     .**/

    while (i < n) /* decreases (\[n]-\[i]) */ {                            /**. .**/
      uintptr_t t = a + b;                                                 /**. .**/
      a = b;                                                               /**. .**/
      b = t;                                                               /**. .**/
      i = i + 1;                                                           /**. .**/
    }                                                                      /**.
    1: ltac1:(rewrite fib_recursion by ZnWords; reflexivity).                   .**/
  }                                                                        /**. .**/
  return b;                                                                /**. .**/
}                                                                          /**.
{ unfold fib. ltac1:(bottom_up_simpl_in_goal; reflexivity). }
{ ltac1:(replace i with n by ZnWords). reflexivity. }
Qed.

End LiveVerif. Comments .**/ //.
