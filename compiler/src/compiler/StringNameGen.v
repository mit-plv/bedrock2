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

Definition maxLength: list string -> nat :=
  List.fold_right (fun s res => max res (String.length s)) 0%nat.

(* reversed binary string *)
Fixpoint rev_binary_pos(p: positive): string :=
  match p with
  | xH => "1"
  | xO q => String "0" (rev_binary_pos q)
  | xI q => String "1" (rev_binary_pos q)
  end.

Definition rev_binary(n: N): string :=
  match n with
  | N.pos p => rev_binary_pos p
  | N0 => "0"
  end.

Lemma rev_binary_pos_nonempty: forall p,
    rev_binary_pos p <> ""%string.
Proof.
  destruct p; simpl; congruence.
Qed.

Lemma rev_binary_pos_inj: forall p p',
    rev_binary_pos p = rev_binary_pos p' ->
    p = p'.
Proof.
  induction p; intros; destruct p'; simpl in *; inversion H; try f_equal; eauto;
    exfalso; eapply rev_binary_pos_nonempty; try eassumption; symmetry; eassumption.
Qed.

Lemma rev_binary_pos_non_zero: forall p,
    rev_binary_pos p <> "0"%string.
Proof.
  destruct p; simpl; try congruence.
  intro C. inversion C. eapply rev_binary_pos_nonempty. eassumption.
Qed.

Lemma rev_binary_inj: forall n n',
    rev_binary n = rev_binary n' ->
    n = n'.
Proof.
  intros.
  destruct n; destruct n'; simpl in *.
  - try reflexivity.
  - symmetry in H. apply rev_binary_pos_non_zero in H. contradiction.
  - apply rev_binary_pos_non_zero in H. contradiction.
  - apply rev_binary_pos_inj in H. congruence.
Qed.

Lemma rev_binary_nonempty: forall n,
    rev_binary n <> ""%string.
Proof.
  unfold rev_binary. intros. destruct n.
  - congruence.
  - apply rev_binary_pos_nonempty.
Qed.

Lemma two_to_number_of_digits_lower_bound: forall n,
    n < 2 ^ N.of_nat (String.length (rev_binary n)).
Proof.
  intros. remember (rev_binary n) as s. revert dependent n.
  induction s; intros.
  - symmetry in Heqs. apply rev_binary_nonempty in Heqs. contradiction.
  - destruct n.
    + simpl in Heqs. inversion Heqs. subst. cbv. reflexivity.
    + simpl in Heqs. destruct p.
      * simpl in Heqs. inversion Heqs. subst.
        change (String.length (String "1" (rev_binary_pos p))) with
            (1 + (String.length (rev_binary_pos p)))%nat.
        rewrite Nat2N.inj_add.
        rewrite N.pow_add_r.
        change (2 ^ N.of_nat 1) with 2.
        change (N.pos p~1) with (1 + 2 * N.pos p).
        specialize (IHs (N.pos p) eq_refl). blia.
      * simpl in Heqs. inversion Heqs. subst.
        change (String.length (String "0" (rev_binary_pos p))) with
            (1 + (String.length (rev_binary_pos p)))%nat.
        rewrite Nat2N.inj_add.
        rewrite N.pow_add_r.
        change (2 ^ N.of_nat 1) with 2.
        change (N.pos p~1) with (1 + 2 * N.pos p).
        specialize (IHs (N.pos p) eq_refl). blia.
      * simpl in Heqs. inversion Heqs. subst.
        cbv. reflexivity.
Qed.

Definition start_state(l: list string): N := 2 ^ N.of_nat (maxLength l).

Definition fresh_string_var(state: N): string * N :=
  (String "x" (rev_binary state), state + 1).

Definition all_from(state: N): string -> Prop :=
  fun v => exists state', String "x" (rev_binary state') = v /\ state <= state'.

Lemma fresh_string_var_spec: forall (s s' : N) (x : string),
    fresh_string_var s = (x, s') ->
    PropSet.elem_of x (all_from s) /\
    ~ PropSet.elem_of x (all_from s') /\
    PropSet.subset (all_from s') (all_from s).
Proof.
  unfold fresh_string_var, all_from, PropSet.subset, PropSet.elem_of; intros.
  inversion H; subst; clear H. ssplit.
  - eexists. split; reflexivity.
  - intro C. destruct C as [s' [E H]].
    inversion E. clear E.
    apply rev_binary_inj in H1. blia.
  - intros. destruct H as [s' [E H]]. subst x.
    eexists. split; [reflexivity|]. blia.
Qed.

Lemma start_state_spec: forall (l : list string) (v : string),
    In v l -> ~ PropSet.elem_of v (all_from (start_state l)).
Proof.
  unfold fresh_string_var, all_from, start_state, PropSet.subset, PropSet.elem_of; intros.
  intro C. destruct C as [state [E C]]. subst v.
  revert dependent l. induction l; simpl; intros.
  - assumption.
  - destruct H.
    + subst. simpl in *.
      assert (2 ^ (N.of_nat (S (String.length (rev_binary state)))) <= state) as A. {
        eapply N.le_trans. 2: eassumption.
        apply N.pow_le_mono_r; blia.
      }
      replace (N.of_nat (S (String.length (rev_binary state)))) with
          (1 + N.of_nat (String.length (rev_binary state))) in A by blia.
      rewrite N.pow_add_r in A.
      change (2 ^ 1) with 2 in A.
      pose proof (two_to_number_of_digits_lower_bound state).
      blia.
    + eapply IHl. 1: eassumption.
      eapply N.le_trans. 2: eassumption.
      apply N.pow_le_mono_r; blia.
Qed.

#[global] Instance StringNameGen: NameGen string N := {|
  freshNameGenState := start_state;
  genFresh := fresh_string_var;
  allFreshVars := all_from;
  genFresh_spec := fresh_string_var_spec;
  freshNameGenState_spec := start_state_spec;
|}.
