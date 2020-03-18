Require Import Coq.Strings.Ascii.
Require Import Coq.Strings.String.
Require Import Coq.Lists.List.
Require Import compiler.util.Common.
Require Import compiler.NameGen.
Require Import Coq.NArith.NArith.
Require Import Coq.Numbers.DecimalString.
Require Import Coq.Numbers.DecimalN.

Local Open Scope string_scope.
Local Open Scope char_scope.
Local Open Scope N_scope.

Local Axiom TODO_someone_freshnames: False.

Definition maxLength: list string -> nat :=
  List.fold_right (fun s res => max res (String.length s)) 0%nat.

Definition N_to_string(n: N): string := DecimalString.NilEmpty.string_of_uint (N.to_uint n).

Lemma string_of_uint_inj: forall ui1 ui2,
    NilEmpty.string_of_uint ui1 = NilEmpty.string_of_uint ui2 -> ui1 = ui2.
Proof.
  intros.
  apply Option.eq_of_eq_Some.
  rewrite <- (NilEmpty.usu ui1), <- (NilEmpty.usu ui2).
  f_equal.
  assumption.
Qed.

Lemma N_to_string_inj: forall n1 n2, N_to_string n1 = N_to_string n2 -> n1 = n2.
Proof.
  unfold N_to_string.
  intros.
  apply Unsigned.to_uint_inj.
  apply string_of_uint_inj.
  assumption.
Qed.

Lemma N_to_uint_nb_digits: forall e n,
    10 ^ N.of_nat e <= n < 10 * 10 ^ N.of_nat e ->
    Decimal.nb_digits (N.to_uint n) = S e.
Proof.
  intros.
  unfold N.to_uint.
  destruct n.
  - apply proj1 in H.
    pose proof (N.pow_nonzero 10 (N.of_nat e)).
    blia.
  - unfold Pos.to_uint.
    replace (Decimal.nb_digits (Decimal.rev (Pos.to_little_uint p))) with
        (Decimal.nb_digits (Pos.to_little_uint p)) by admit.
    revert dependent p.
    induction e; intros.
    + simpl in *.
Abort.

Lemma ten_to_number_of_digits_lower_bound: forall n,
    n < 10 ^ N.of_nat (String.length (N_to_string n)).
Proof.
  unfold N_to_string. intros.
Admitted.

Instance StringNameGen: NameGen string N. refine ({|
  freshNameGenState(l: list string) := (10 ^ (N.of_nat (maxLength l)))%N;
  genFresh(state: N) := (String "x" (N_to_string state), state + 1);
  allFreshVars(state: N) := fun v => exists state', String "x" (N_to_string state') = v /\ state <= state';
|}).
(* TODO abstract proofs *)
all: unfold PropSet.subset, PropSet.elem_of; intros.
- inversion H; subst; clear H. ssplit.
  + eexists. split; reflexivity.
  + intro C. destruct C as [s' [E H]].
    inversion E. clear E.
    apply N_to_string_inj in H1. blia.
  + intros. destruct H as [s' [E H]]. subst x.
    eexists. split; [reflexivity|]. blia.
- intro C. destruct C as [state [E C]]. subst v.
  revert dependent l. induction l; simpl; intros.
  + assumption.
  + destruct H.
    * subst. simpl in *.
      assert (10 ^ (N.of_nat (S (String.length (N_to_string state)))) <= state) as A. {
        eapply N.le_trans. 2: eassumption.
        apply N.pow_le_mono_r; blia.
      }
      replace (N.of_nat (S (String.length (N_to_string state)))) with
          (1 + N.of_nat (String.length (N_to_string state))) in A by blia.
      rewrite N.pow_add_r in A.
      change (10 ^ 1) with 10 in A.
      pose proof (ten_to_number_of_digits_lower_bound state).
      blia.
    * eapply IHl. 1: eassumption.
      eapply N.le_trans. 2: eassumption.
      apply N.pow_le_mono_r; blia.
Defined.
