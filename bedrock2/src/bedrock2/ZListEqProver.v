Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia coqutil.Ltac2Lib.Lia.
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

Ltac list_eq_step :=
  lazymatch goal with
  | |- List.from ?i ?xs = List.from ?j ?xs => f_equal
  | |- List.upto ?i ?xs = List.upto ?j ?xs => f_equal
  | |- List.app _ _ = _ => eapply split_rhs; bottom_up_simpl_in_goal_nop_ok
  | |- _ = List.app _ _ => eapply split_lhs; bottom_up_simpl_in_goal_nop_ok
  end.

Local Ltac t :=
  match goal with
  | |- ?x = ?x => reflexivity
  | |- @eq (list _) _ _ => list_eq_step
  | |- @eq Z _ _ => lia
  end.

Local Set Default Goal Selector "1".

Goal forall (xs ys zs: list bool) i j0 j1 k0 k1,
    0 <= i <= len xs ->
    0 <= j0 + j1 <= len ys ->
    j0 + j1 = k0 + k1 ->
    xs ++ ys ++ (zs ++ xs[:i]) ++ xs[i:] = (xs ++ ys[:j0 + j1]) ++ ys[k0 + k1:] ++ zs ++ xs.
Proof. intros. t. t. t. t. t. t. t. t. t. t. t. t. Succeed Qed. Abort.

Goal forall s i j,
    0 < i + j <= 1 ->
    0 < len s ->
    s[:i + j] ++ s[1:] ++ [|0|] = s ++ [|0|].
Proof. intros. t. t. t. t. t. t. Succeed Qed. Abort.
