Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import Coq.Lists.List.
Require Import coqutil.Datatypes.ZList.
Import ZList.List.ZIndexNotations. Local Open Scope zlist_scope.
Require Import bedrock2.bottom_up_simpl.

Section WithA.
  Context [A: Type] {inh: inhabited A}.

  Lemma split_rhs: forall (xs ys zs: list A),
      xs = zs[:len xs] ->
      ys = zs[len xs:] ->
      xs ++ ys = zs.
  Proof.
    intros. rewrite H, H0. symmetry. apply List.split_at_index.
  Qed.

  Lemma split_lhs: forall (xs ys zs: list A),
      xs = zs[:len xs] ->
      ys = zs[len xs:] ->
      zs = xs ++ ys.
  Proof. intros. symmetry. eapply split_rhs; assumption. Qed.
End WithA.

Ltac2 Set bottom_up_simpl_sidecond_hook := fun _ =>
  (* Note/TODO: full-fledged bottom_up_simpl_in_goal for sideconditions is a bit overkill,
     we only need push_down_len *)
     bottom_up_simpl_in_goal_nop_ok ();
     lia.

Goal forall (xs ys zs: list bool) i j0 j1 k0 k1,
    0 <= i <= len xs ->
    0 <= j0 + j1 <= len ys ->
    j0 + j1 = k0 + k1 ->
    xs ++ ys ++ (zs ++ xs[:i]) ++ xs[i:] = (xs ++ ys[:j0 + j1]) ++ ys[k0 + k1:] ++ zs ++ xs.
Proof.
  intros.
  eapply split_rhs.
  { bottom_up_simpl_in_goal_nop_ok. reflexivity. }
  { bottom_up_simpl_in_goal_nop_ok.
    eapply split_rhs.
    { bottom_up_simpl_in_goal_nop_ok.
      eapply split_lhs; bottom_up_simpl_in_goal_nop_ok.
      1: reflexivity.
      f_equal. lia. }
    { bottom_up_simpl_in_goal_nop_ok.
Abort.

Goal forall s i j,
    0 < i + j <= 1 ->
    0 < len s ->
    s[:i + j] ++ s[1:] ++ [|0|] = s ++ [|0|].
Proof.
  intros.

  replace (i + j) with 1 by lia.

  eapply split_rhs.
  { bottom_up_simpl_in_goal_nop_ok. reflexivity. }
  { bottom_up_simpl_in_goal_nop_ok. reflexivity. }
Succeed Qed. Abort.
