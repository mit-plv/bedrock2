Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Z.Lia.

Section ListSet.
  Context {E: Type}.
  Context (eeq: E -> E -> bool).
  Context {eeq_spec: EqDecider eeq}.

  Definition removeb(e: E)(l: list E): list E := filter (fun e' => negb (eeq e e')) l.

  Definition list_union(A B: list E): list E :=
    fold_right (fun a res => if find (eeq a) res then res else a :: res) B A.

  Definition list_intersect(A B: list E): list E :=
    fold_right (fun a res => if find (eeq a) B then a :: res else res) nil A.

  Definition list_diff(A B: list E): list E :=
    fold_left (fun res b => removeb b res) B A.

  Lemma length_list_union_nil_r: forall (l: list E),
      length (list_union l []) <= length l.
  Proof.
    induction l.
    - simpl. reflexivity.
    - simpl. destruct_one_match; simpl; blia.
  Qed.

  Lemma find_list_union_r_cons_None_Some: forall (l1 l2: list E) a a0 e,
      find (eeq a) (list_union l1 (a0 :: l2)) = None ->
      find (eeq a) (list_union l1 l2) = Some e ->
      False.
  Proof.
    induction l1; intros.
    - simpl in *. destr (eeq a a0); congruence.
    - simpl in *.
      destr (find (eeq a) (list_union l1 (a1 :: l2))).
      + destr (find (eeq a) (list_union l1 l2)).
        * eauto.
        * simpl in *. destr (eeq a0 a); [|eauto].
          subst. congruence.
      + simpl in *. destr (eeq a0 a); [discriminate|].
        destr (find (eeq a) (list_union l1 l2)); [eauto|].
        simpl in *.
        destr (eeq a0 a); [congruence|].
        eauto.
  Qed.

  Lemma find_list_union_r_cons_Some_None: forall (l1 l2: list E) a a0 e,
      find (eeq a) (list_union l1 (a0 :: l2)) = Some e ->
      find (eeq a) (list_union l1 l2) = None ->
      a = a0 /\ a = e.
  Proof.
    induction l1; intros.
    - simpl in *. destruct_one_match_hyp.
      + split; congruence.
      + congruence.
    - simpl in *.
      destr (find (eeq a) (list_union l1 (a1 :: l2))).
      + destr (find (eeq a) (list_union l1 l2)).
        * eauto.
        * simpl in *. destr (eeq a0 a); [discriminate|].
          eauto.
      + simpl in *. destr (eeq a0 a).
        * subst. replace e with a in * by congruence. clear e H.
          destr (find (eeq a) (list_union l1 l2)); [exfalso; congruence|].
          simpl in H0.
          destr (eeq a a); exfalso; congruence.
        * destr (find (eeq a) (list_union l1 l2)); eauto.
          simpl in H0.
          destr (eeq a0 a); try congruence. eauto.
  Qed.

  Lemma length_list_union_cons_r: forall (l1 l2: list E) (a: E),
      length (list_union l1 (a :: l2)) <= S (length (list_union l1 l2)).
  Proof.
    induction l1; intros.
    - simpl. reflexivity.
    - simpl. destr (find (eeq a) (list_union l1 l2)).
      + destr (find (eeq a) (list_union l1 (a0 :: l2))).
        * eapply IHl1.
        * exfalso. eapply find_list_union_r_cons_None_Some; eassumption.
      + simpl in *.
        destr (find (eeq a) (list_union l1 (a0 :: l2))).
        * pose proof find_list_union_r_cons_Some_None as P.
          specialize P with (1 := E1) (2 := E0). destruct P. subst.
          specialize (IHl1 l2 e). blia.
        * simpl. apply le_n_S. eapply IHl1.
  Qed.

  Lemma length_list_union: forall (l1 l2: list E),
      (length (list_union l1 l2) <= length l1 + length l2)%nat.
  Proof.
    induction l2.
    - pose proof (length_list_union_nil_r l1). blia.
    - pose proof (length_list_union_cons_r l1 l2 a). simpl. blia.
  Qed.

  Lemma list_union_empty_l: forall l,
      list_union nil l = l.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma list_union_empty_r: forall l,
      NoDup l ->
      list_union l nil = l.
  Proof.
    induction l; intros.
    - reflexivity.
    - simpl. inversion H. subst.
      rewrite IHl by assumption.
      destr (find (eeq a) l); [exfalso|reflexivity].
      apply find_some in E0. destruct E0.
      destr (eeq a e); congruence.
  Qed.

  Lemma union_Forall: forall (P: E -> Prop) (l1 l2: list E),
      Forall P l1 ->
      Forall P l2 ->
      Forall P (list_union l1 l2).
  Proof.
    induction l1; intros; simpl; [assumption|].
    inversion H. subst. clear H. destruct_one_match; eauto.
  Qed.

  Lemma of_list_removeb: forall x A,
      of_list (removeb x A) = diff (of_list A) (singleton_set x).
  Proof.
    unfold of_list, diff, singleton_set, elem_of. intros.
    extensionality e. apply propositional_extensionality. split.
    - induction A; intros.
      + simpl in *. contradiction.
      + simpl in *. destr (eeq x a).
        * subst. simpl in *. intuition idtac.
        * simpl in *. intuition congruence.
    - induction A; intros.
      + simpl in *. intuition idtac.
      + simpl in *. destr (eeq x a).
        * subst. simpl in *. intuition idtac.
        * simpl in *. intuition congruence.
  Qed.

End ListSet.

Lemma remove_In_ne{A: Type}(aeqb: A -> A -> bool){aeqb_spec: EqDecider aeqb}:
  forall (l: list A) (f1 f2: A),
      In f1 l ->
      f1 <> f2 ->
      In f1 (removeb aeqb f2 l).
Proof.
  induction l; intros.
  - inversion H.
  - simpl in *. destruct H.
    + subst a.
      destr (aeqb f2 f1); try congruence. simpl. auto.
    + destr (aeqb f2 a); simpl.
      * subst a. eauto.
      * simpl. eauto.
Qed.

Lemma firstn_skipn_reassemble: forall (T: Type) (l l1 l2: list T) (n: nat),
    List.firstn n l = l1 ->
    List.skipn n l = l2 ->
    l = l1 ++ l2.
Proof.
  intros. subst. symmetry. apply firstn_skipn.
Qed.

Lemma firstn_skipn_nth: forall (T: Type) (i: nat) (L: list T) (d: T),
    (i < length L)%nat ->
    List.firstn 1 (List.skipn i L) = [List.nth i L d].
Proof.
  induction i; intros.
  - simpl. destruct L; simpl in *; try (exfalso; blia). reflexivity.
  - simpl. destruct L; try (simpl in *; exfalso; blia). simpl.
    rewrite <- IHi; [reflexivity|]. simpl in *. blia.
Qed.


Definition listUpdate{E: Type}(l: list E)(i: nat)(e: E): list E :=
  firstn i l ++ [e] ++ skipn (S i) l.

Lemma listUpdate_length: forall E i l (e: E),
  i < length l ->
  length (listUpdate l i e) = length l.
Proof.
  induction i; intros.
  - destruct l; simpl in *; [bomega|reflexivity].
  - destruct l; simpl in *; [bomega|].
    f_equal.
    apply IHi.
    bomega.
Qed.

Definition listUpdate_error{E: Type}(l: list E)(i: nat)(e: E): option (list E) :=
  if Nat.ltb i (length l) then Some (listUpdate l i e) else None.

Lemma listUpdate_error_length: forall E i l l' (e: E),
  listUpdate_error l i e = Some l' ->
  length l' = length l.
Proof.
  intros. unfold listUpdate_error in H. destruct_one_match_hyp; [|discriminate].
  inversion H. apply listUpdate_length. assumption.
Qed.

Lemma nth_error_listUpdate_error_same: forall i E l l' (e e': E),
  listUpdate_error l i e = Some l' ->
  nth_error l' i = Some e' ->
  e' = e.
Proof.
  induction i; intros.
  - unfold listUpdate_error in H.
    destruct_one_match_hyp; [|discriminate].
    destruct l.
    + simpl in *; bomega.
    + unfold listUpdate in H. simpl in *. inversion H. rewrite <- H2 in H0.
      inversion H0. reflexivity.
  - unfold listUpdate_error in H.
    destruct_one_match_hyp; [|discriminate].
    destruct l.
    + simpl in *; bomega.
    + unfold listUpdate in H. simpl in *. inversion H. rewrite <- H2 in H0.
      eapply IHi with (l := l).
      2: eassumption.
      unfold listUpdate_error.
      destr (Nat.ltb i (length l)); [reflexivity|bomega].
Qed.

Lemma nth_error_firstn: forall E i (l: list E) j,
  j < i ->
  nth_error (firstn i l) j = nth_error l j.
Proof.
  induction i; intros.
  - bomega.
  - simpl. destruct l; [reflexivity|].
    destruct j; [reflexivity|].
    simpl.
    apply IHi.
    bomega.
Qed.

Lemma nth_error_skipn: forall E i j (l: list E),
  i <= j ->
  nth_error (skipn i l) (j - i) = nth_error l j.
Proof.
  induction i; intros.
  - replace (j - 0) with j by bomega. reflexivity.
  - simpl. destruct l.
    * destruct j; simpl; [reflexivity|].
      destruct (j - i); reflexivity.
    * simpl. destruct j; [bomega|].
      replace (S j - S i) with (j - i) by bomega.
      rewrite IHi by bomega.
      reflexivity.
Qed.

Lemma nth_error_listUpdate_error_diff: forall E l l' i j (e: E),
  listUpdate_error l i e = Some l' ->
  j <> i ->
  nth_error l' j = nth_error l j.
Proof.
  intros. unfold listUpdate_error in H.
  destruct_one_match_hyp; [|discriminate].
  assert (j < i \/ i < j < length l \/ length l <= j) as C by bomega.
  destruct C as [C|[C|C]].
  - inversion H. clear H. subst l'. unfold listUpdate.
    rewrite nth_error_app1.
    + apply nth_error_firstn. assumption.
    + pose proof (@firstn_length_le _ l i). bomega.
  - inversion H. subst l'. unfold listUpdate.
    pose proof (firstn_le_length i l).
    rewrite nth_error_app2 by bomega.
    rewrite nth_error_app2 by (simpl; bomega).
    rewrite firstn_length_le by bomega.
    change (length [e]) with 1.
    replace (j - i -1) with (j - (S i)) by bomega.
    apply nth_error_skipn.
    bomega.
  - inversion H.
    pose proof (nth_error_None l j) as P.
    destruct P as [_ P]. rewrite P by assumption.
    apply nth_error_None.
    rewrite listUpdate_length; assumption.
Qed.
