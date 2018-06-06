
Lemma distr_if_over_app: forall T U P1 P2 (c: sumbool P1 P2) (f1 f2: T -> U) (x: T),
    (if c then f1 else f2) x = if c then f1 x else f2 x.
Proof. intros. destruct c; reflexivity. Qed.

Lemma pair_eq_acc: forall T1 T2 (a: T1) (b: T2) t,
    t = (a, b) -> a = fst t /\ b = snd t.
Proof. intros. destruct t. inversion H. subst. simpl. auto. Qed.

Lemma let_pair_rhs_eq: forall {A B R} (c1 c2: A * B) (f: A -> B -> R),
    c1 = c2 ->
    (let (a, b) := c1 in f a b) = (let (a, b) := c2 in f a b).
Proof. intros. subst. reflexivity. Qed.

Lemma elim_then_true_else_false: forall P Q (c: {P} + {Q}) A (v1 v2: A),
    (if if c then true else false then v1 else v2)
    = (if c then v1 else v2).
Proof.
  intros. destruct c; reflexivity.
Qed.
