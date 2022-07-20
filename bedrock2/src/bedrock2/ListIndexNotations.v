Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.WordSimpl.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Datatypes.Inhabited.

Declare Scope list_index_scope.

(* Note: Using .. instead of : (like Dafny) doesn't seem to work for a[i .. j],
   and `Check (1 .. 2 .. 3)` says `Special token .. is for use in the Notation command`,
   so we use : (like Python).
   Note: Since Coq prints spaces around operators, we also put spaces around :,
   because `a[:i + j]` would suggest `a[(:i) + j]` instead of `a[:(i + j)]`.
   But if the index is just one number or variable, the space looks weird,
   i.e. we want Coq to print `a[:i]` instead of `a[: i]`, and we achieve this by
   adding an extra only printing rule where i is a `name`.
   We would prefer making i a `global`, which in addition to bound names also includes
   globals and number literals, but `i global` is also printed back even if i is an
   arbitrary expression (COQBUG https://github.com/coq/coq/issues/15360), so we use
   `i name` for now. *)
Notation "a [: i ]" := (List.firstn i a)
  (at level 8, i at level 99, left associativity, format "a [:  i ]")
: list_index_scope.
Notation "a [ : i ]" := (List.firstn i a)
  (at level 8, i name, left associativity, format "a [ : i ]", only printing)
: list_index_scope.

Notation "a [ i :]" := (List.skipn i a)
  (at level 8, i at level 99, left associativity, format "a [ i  :]")
: list_index_scope.
Notation "a [ i : ]" := (List.skipn i a)
  (at level 8, i name, left associativity, format "a [ i : ]", only printing)
: list_index_scope.

(* Note: i needs to be at level <= 99 to avoid conflict with type annotation, and all
   other notations starting with `_ [ _` must therefore also put i at that same level. *)
Notation "a [ i : j ]" := (List.skipn i (List.firstn j a))
  (at level 8, i at level 99, left associativity, format "a [ i  :  j ]")
: list_index_scope.

Section Tests.
  Import ListNotations. Local Open Scope list_scope.
  Local Open Scope list_index_scope.
  Local Open Scope Z_scope. (* to test that number literals are still parsed in nat_scope *)

  Context (A: Type) {inh: inhabited A} (xs ys zs: list A) (a b c: A) (i j k: nat)
          (f: A -> A) (g: list A -> list A).

  Goal xs[:2] = xs[:Nat.two]. Abort.
  Goal xs[:j] = xs[i:]. Abort.
  Goal xs[:3] = ys[4:]. (* has a space, not as desired *) Abort.
  Goal xs[: i + j] = ys[i + j : j + k].  Abort.
  Goal xs[i : j] <> nil.
    (* printing no spaces around `:` here would be nice, but is not possible
       because we can't fake a seemingly different parsing rule that prints the same,
       like we can for `_ [ _ :]` vs `_ [ _ : ]` *)
  Abort.
  Goal xs[i : i + j] = xs[i:][:j]. Abort.
  Goal List.upds xs i ys = zs[i:k]. unfold List.upds. Abort.
End Tests.


(* makes expressions a bit more complicated by repeating n, but enables detection
   of merge opportunities around ++ *)
#[export] Hint Rewrite List.firstn_skipn_comm : fwd_rewrites.

#[export] Hint Rewrite List.nth_skipn : fwd_rewrites.
#[export] Hint Rewrite List.nth_firstn using lia : fwd_rewrites.

Module List. Section __.
  Context [A: Type].

  (* Rewrite lemmas to merge patterns similar to `xs[i:j] ++ xs[j:k]` into `xs[i:k]`.
     We could normalize everything into `xs[_:_]` form (instead of also allowing `xs[:_]`
     and `xs[_:]`) and insist on writing `xs ++ ys ++ zs ++ []` instead of just
     `xs ++ ys ++ zs`, which would then only require one merging rewrite lemma, but
     then other ad-hoc rewrites might break this form requirement, so we distinguish
     three dimensions along which the rewrite lemma to merge `xs[i:j] ++ xs[j':k]`
     has to vary:
     - On the left, is there only an end index (0) or both a start+end index (1)?
     - On the right, is there only a start index (0) or both a start+end index (1)?
     - Is the right list the last one (0) or is another one appended to it (1)?
     By "is there a start index", we mean "is it wrapped in a List.skipn", and
     by "is there an end index", we mean "is it wrapped in a List.firstn". *)

  Lemma merge_sublist_000: forall j j' (xs: list A),
      j = j' ->
      List.firstn j xs ++ List.skipn j' xs = xs.
  Proof.
    intros. subst j'. apply List.firstn_skipn.
  Qed.

  Lemma merge_sublist_001: forall j j' (xs ys: list A),
      j = j' ->
      List.firstn j xs ++ List.skipn j' xs ++ ys = xs ++ ys.
  Proof.
    intros. subst j'. rewrite List.app_assoc. f_equal. apply List.firstn_skipn.
  Qed.

  Lemma merge_sublist_010: forall j j' k (xs: list A),
      (j = j' /\ j' <= k)%nat ->
      List.firstn j xs ++ List.skipn j' (List.firstn k xs) = List.firstn k xs.
  Proof.
    intros. destruct H as (? & H). subst j'.
    rewrite <- (List.firstn_skipn j (List.firstn k xs)) at 2.
    f_equal. rewrite List.firstn_firstn. f_equal. lia.
  Qed.

  Lemma merge_sublist_011: forall j j' k (xs ys: list A),
      (j = j' /\ j' <= k)%nat ->
      List.firstn j xs ++ List.skipn j' (List.firstn k xs) ++ ys = List.firstn k xs ++ ys.
  Proof.
    intros. rewrite List.app_assoc. f_equal. apply merge_sublist_010. assumption.
  Qed.

  Lemma merge_sublist_100: forall i j j' (xs: list A),
      (i <= j /\ j = j')%nat ->
      List.skipn i (List.firstn j xs) ++ List.skipn j' xs = List.skipn i xs.
  Proof.
    intros. destruct H as (H & ?). subst j'.
    rewrite <- (List.firstn_skipn (j-i) (List.skipn i xs)).
    rewrite List.firstn_skipn_comm.
    rewrite List.skipn_skipn.
    repeat match goal with
           | |- @eq (list _) _ _ => f_equal
           end.
    all: lia.
  Qed.

  Lemma merge_sublist_101: forall i j j' (xs ys: list A),
      (i <= j /\ j = j')%nat ->
      List.skipn i (List.firstn j xs) ++ List.skipn j' xs ++ ys = List.skipn i xs ++ ys.
  Proof.
    intros. rewrite List.app_assoc. f_equal. apply merge_sublist_100. assumption.
  Qed.

  Lemma merge_sublist_110: forall i j j' k (xs: list A),
      (i <= j /\ j = j' /\ j' <= k)%nat ->
      List.skipn i (List.firstn j xs) ++ List.skipn j' (List.firstn k xs) =
        List.skipn i (List.firstn k xs).
  Proof.
    intros. destruct H as (? & ? & ?). subst j'.
    rewrite <- (List.firstn_skipn (j-i) (List.skipn i (List.firstn k xs))).
    rewrite List.firstn_skipn_comm.
    rewrite List.skipn_skipn.
    rewrite List.firstn_firstn.
    repeat match goal with
           | |- @eq (list _) _ _ => f_equal
           end.
    all: lia.
  Qed.

  Lemma merge_sublist_111: forall i j j' k (xs ys: list A),
      (i <= j /\ j = j' /\ j' <= k)%nat ->
      List.skipn i (List.firstn j xs) ++ List.skipn j' (List.firstn k xs) ++ ys =
        List.skipn i (List.firstn k xs) ++ ys.
  Proof.
    intros. rewrite List.app_assoc. f_equal. apply merge_sublist_110. assumption.
  Qed.

  Import ListNotations. Local Open Scope list_scope.

  Lemma fold_upd: forall (l: list A) i j v,
      (j = i + 1 /\ i < List.length l)%nat ->
      List.firstn i l ++ [v] ++ List.skipn j l = List.upd l i v.
  Proof.
    intros *. intros (? & ?). subst j. unfold upd, upds. cbn [List.length].
    f_equal. f_equal.
    - replace (length l - i)%nat with (S (length l - i - 1)) by lia. cbn.
      rewrite List.firstn_nil. reflexivity.
    - f_equal. lia.
  Qed.
End __. End List.

#[export] Hint Rewrite
  List.merge_sublist_000
  List.merge_sublist_001
  List.merge_sublist_010
  List.merge_sublist_011
  List.merge_sublist_100
  List.merge_sublist_101
  List.merge_sublist_110
  List.merge_sublist_111
using lia : fwd_rewrites.

Ltac list_simpl_in_hyps :=
  unfold List.upd, List.upds in *|-;
  repeat (repeat word_simpl_step_in_hyps;
          repeat match goal with
                 | H:_ |- _ => rewrite_db fwd_rewrites in H
                 end);
  repeat match goal with
         | H: _ |- _ => progress rewrite List.fold_upd in H by lia
         end.

Ltac list_simpl_in_goal :=
  unfold List.upd, List.upds;
  repeat (repeat word_simpl_step_in_goal; try rewrite_db fwd_rewrites);
  rewrite ?List.fold_upd by lia.

Ltac list_simpl_in_all := list_simpl_in_hyps; list_simpl_in_goal.

Require Import coqutil.Datatypes.OperatorOverloading.

Section ListRewriterTests.
  Local Open Scope list_index_scope.
  Local Open Scope oo_scope.

  Goal forall [A: Type] {inh: inhabited A}(f: A -> A) ws,
      (16 <= length ws)%nat ->
      ws[:7] ++ [| f ws[7] |] ++ ws[8:] =
        ws[:2] ++ ws[2:][:5] ++ [| f ws[2:][:10][5] |] ++ ws[2:][6:10] ++ ws[12:].
  Proof.
    intros.
    match goal with
    | |- ?G => assert G
    end.
    { list_simpl_in_goal.
      match goal with
      | |- ?x = ?x => reflexivity
      end. }
    { list_simpl_in_all.
      match goal with
      | H: ?A |- ?A => exact H
      end. }
    all: fail.
  Abort.
End ListRewriterTests.
