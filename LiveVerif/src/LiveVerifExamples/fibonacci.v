(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
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

(* TODO support functions that don't access any memory *)
Definition dummy: mem -> Prop := emp True.

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

(* Tells the proof automation to apply f_equal on goals of shape `fib _ = fib _` *)
#[local] Instance fib_inj: fake_injective fib. Qed.

(* TODO also something like  word.unsigned (if c then a else b) = ... ? *)
Lemma if_to_or: forall (c: bool) (P Q: Prop),
    (if c then P else Q) -> c = true /\ P \/ c = false /\ Q.
Proof. intros. destruct c; auto. Qed.

#[export] Instance spec_of_fibonacci: fnspec :=                                 .**/

uintptr_t fibonacci(uintptr_t n) /**#
  ghost_args := (R: mem -> Prop);
  requires t m := sep dummy R m;
  ensures t' m' res := t' = t /\ sep dummy R m' /\ res = fib n #**/   /**.
Derive fibonacci SuchThat (fun_correct! fibonacci) As fibonacci_ok.             .**/
{                                                                          /**. .**/
  uintptr_t b = 0;                                                         /**. .**/
  if (n == 0) {                                                            /**. .**/
  } else {                                                                 /**. .**/
    uintptr_t a = 0;                                                       /**. .**/
    b = 1;                                                                 /**. .**/
    uintptr_t i = 1;                                                       /**.

    let_bindings_to_eqs.
    replace /[0] with (fib (i ^- /[1])) in Ha by
        (subst; unfold fib; bottom_up_simpl_in_goal; reflexivity).
    replace /[1] with (fib i) in Hb by
        (subst; unfold fib; bottom_up_simpl_in_goal; reflexivity).
    assert (1 <= \[i] <= \[n]) by ZnWords.
    eqs_to_let_bindings.
    clearbody i; move b after a.

    loop invariant above i.                                                     .**/

    while (i < n) /* decreases (\[n]-\[i]) */ {                            /**. .**/
      uintptr_t t = a + b;                                                 /**. .**/
      a = b;                                                               /**. .**/
      b = t;                                                               /**. .**/
      i = i + 1;                                                           /**. .**/
    }                                                                      /**.
    subst a' b' i. rewrite fib_recursion by ZnWords; reflexivity.               .**/
  }                                                                        /**. .**/
  return b;                                                                /**. .**/
}                                                                          /*?.

step. step. step. step. step. step. step. step. step.
unfold ands in H2.
eapply if_to_or in H2.
rewrite __Zdef_c in H2.
zify_hyps.
destruct c; subst_all_let_bound_vars.
{ unfold fib. replace \[n] with 0 by lia. bottom_up_simpl_in_goal. reflexivity. }
{ destruct H2; try lia.
  unfold fib.
  replace \[i] with \[n] by lia. reflexivity. }
Qed.

End LiveVerif. Comments .**/ //.
