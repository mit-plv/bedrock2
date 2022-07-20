Require Coq.Lists.List. Import List.ListNotations. Open Scope list_scope.

Section MergingLists.
  Context [A: Type].

  Lemma push_if_app_l: forall (b: bool) (l1 l2 r: list A),
      (if b then (l1 ++ l2) else r) =
        (if b then l1 else List.firstn (List.length l1) r) ++
        (if b then l2 else List.skipn (List.length l1) r).
  Proof.
    intros. destruct b. 1: reflexivity. symmetry. apply List.firstn_skipn.
  Qed.

  Lemma push_if_app_r: forall (b: bool) (l r1 r2: list A),
      (if b then l else (r1 ++ r2)) =
        (if b then List.firstn (List.length r1) l else r1) ++
        (if b then List.skipn (List.length r1) l else r2).
  Proof.
    intros. destruct b. 2: reflexivity. symmetry. apply List.firstn_skipn.
  Qed.

  Lemma push_if_singleton: forall (b: bool) (a1 a2: A),
      (if b then [a1] else [a2]) = [if b then a1 else a2].
  Proof. intros. destruct b; reflexivity. Qed.

  Lemma pull_if_firstn: forall (b: bool) (l1 l2: list A) n,
      List.firstn n (if b then l1 else l2) =
        if b then List.firstn n l1 else List.firstn n l2.
  Proof. intros. destruct b; reflexivity. Qed.

  Lemma pull_if_skipn: forall (b: bool) (l1 l2: list A) n,
      List.skipn n (if b then l1 else l2) =
        if b then List.skipn n l1 else List.skipn n l2.
  Proof. intros. destruct b; reflexivity. Qed.

  Lemma pull_if_length: forall (b: bool) (l1 l2: list A),
      List.length (if b then l1 else l2) = if b then List.length l1 else List.length l2.
  Proof. intros. destruct b; reflexivity. Qed.

  Lemma if_same(b: bool)(a: A): (if b then a else a) = a.
  Proof. destruct b; reflexivity. Qed.
End MergingLists.
