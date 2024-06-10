(* -*- eval: (load-file "../LiveVerif/live_verif_setup.el"); -*- *)
Require Import LiveVerif.LiveVerifLib.

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
  replace (Z.to_nat \[n ^+ /[1]]) with (S (S (pred (Z.to_nat \[n])))) by ZnWords.ZnWords.
  replace (Z.to_nat \[n ^- /[1]]) with (pred (Z.to_nat \[n])) by ZnWords.ZnWords.
  replace (Z.to_nat \[n]) with (S (pred (Z.to_nat \[n]))) at 3 by ZnWords.ZnWords.
  forget (pred (Z.to_nat \[n])) as m.
  change (fib_nat (S (S m))) with (fib_nat m + fib_nat (S m))%nat.
  ZnWords.ZnWords.
Qed.

Lemma fib_f_equal: forall x y, safe_implication (x = y) (fib x = fib y).
Proof. unfold safe_implication. intros. subst. reflexivity. Qed.
(* Tells the proof automation to apply f_equal on goals of shape `fib _ = fib _` *)
#[local] Hint Resolve fib_f_equal: safe_implication.

(* TODO also something like  word.unsigned (if c then a else b) = ... ? *)
Lemma if_to_or: forall (c: bool) (P Q: Prop),
    (if c then P else Q) -> c = true /\ P \/ c = false /\ Q.
Proof. intros. destruct c; auto. Qed.

#[export] Instance spec_of_fibonacci: fnspec :=                                 .**/

uintptr_t fibonacci(uintptr_t n) /**#
  requires t m := True;
  ensures t' m' res := t' = t /\ m' = m /\ res = fib n #**/                /**.
Derive fibonacci SuchThat (fun_correct! fibonacci) As fibonacci_ok.             .**/
{                                                                          /**. .**/
  if (n == 0) /* split */ {                                                /**. .**/
    return 0;                                                              /**. .**/
  }                                                                        /**.
    unfold fib. bottom_up_simpl_in_goal. reflexivity.                           .**/
  else {                                                                   /**. .**/
    uintptr_t a = 0;                                                       /**. .**/
    uintptr_t b = 1;                                                       /**. .**/
    uintptr_t i = 1;                                                       /**.

    swap /[0] with (fib (i ^- /[1])) in #(a = /[0]).
    { unfold fib, fib_nat. steps. }
    swap /[1] with (fib i) in #(b = /[1]).
    { unfold fib, fib_nat. steps. }
    prove (1 <= \[i] <= \[n]).
    delete #(i = ??).
    loop invariant above a.                                                     .**/

    while (i < n) /* decreases (\[n]-\[i]) */ {                            /**. .**/
      uintptr_t t = a + b;                                                 /**. .**/
      a = b;                                                               /**. .**/
      b = t;                                                               /**. .**/
      i = i + 1;                                                           /**. .**/
    }                                                                      /**.
    subst a' i. rewrite fib_recursion by steps; reflexivity.                    .**/
    return b;                                                              /**. .**/
  }                                                                        /**. .**/
}                                                                          /**.
Qed.

End LiveVerif. Comments .**/ //.
