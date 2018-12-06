Require Setoid. Require Import bedrock2.Map. Import map.

Section Decomp.
  Context {key value} {map : map key value} {ok : ok map}.

  Lemma union_spec m1 m2 k :
    (exists v, get m2 k = Some v /\ get (union m1 m2) k = Some v) \/
    (get m2 k = None /\ get (union m1 m2) k = get m1 k).
  Proof.
    destruct (get m2 k) eqn:?HH; [left | right ].
    { exists v. split. reflexivity. erewrite get_union_right; eauto. }
    { split. reflexivity. rewrite get_union_left; eauto. }
  Qed.
  
  Lemma union_comm x y : disjoint x y -> union x y = union y x.
  Proof.
    cbv [disjoint]; intros; eapply map_ext; intros.
    destruct (get x k) eqn:Hl, (get y k) eqn:Hr;
      repeat ((erewrite get_union_left by eauto)
              || (erewrite get_union_right by eauto));
      firstorder congruence.
  Qed.

  Lemma union_assoc x y z
    : disjoint x y -> disjoint y z -> disjoint x z ->
      union x (union y z) = union (union x y) z.
  Proof.
    cbv [disjoint]; intros; eapply map_ext; intros.
    destruct (union_spec x (union y z) k);
    destruct (union_spec (union x y) z k);
    destruct (union_spec y z k);
    destruct (union_spec x y k);
    destruct (get x k) as [?vx|] eqn:?Hx;
    destruct (get y k) as [?vy|] eqn:?Hy;
    destruct (get z k) as [?vz|] eqn:?Hz;
    firstorder congruence.
  Qed.

  Lemma union_empty_r x : union x empty = x.
  Proof. eapply map_ext; intros; rewrite get_union_left; eauto using get_empty. Qed.
  Lemma union_empty_l x : union empty x = x.
  Proof. rewrite (union_comm empty x); destruct ok; eauto || congruence. Qed.
  Lemma empty_union m1 m2 : union m1 m2 = empty <-> (m1 = empty /\ m2 = empty).
  Proof. split; intros; try split; eapply map_ext; intros k;
    destruct (union_spec m1 m2 k); destruct (get m1 k) eqn:?; firstorder congruence.
  Qed.
                            
  Lemma disjoint_empty_l x : disjoint empty x. destruct ok; repeat intro; congruence. Qed.
  Lemma disjoint_empty_r x : disjoint x empty. destruct ok; repeat intro; congruence. Qed.
  Lemma disjoint_comm m1 m2 : disjoint m1 m2 <-> disjoint m2 m1.
  Proof. cbv [disjoint]. firstorder idtac. Qed.
  Lemma disjoint_union_r x y z : disjoint x (union y z) <-> (disjoint x y /\ disjoint x z).
  Proof.
    cbv [disjoint]; repeat (split || intros);
      destruct (union_spec y z k);
      destruct (get x k) as [?vx|] eqn:?Hx;
      destruct (get y k) as [?vy|] eqn:?Hy;
      destruct (get z k) as [?vz|] eqn:?Hz;
      firstorder congruence.
  Qed.
  Lemma disjoint_union_l x y z : disjoint (union x y) z <-> (disjoint x z /\ disjoint y z).
  Proof. rewrite disjoint_comm. rewrite disjoint_union_r. rewrite 2(disjoint_comm z). reflexivity. Qed.
  Lemma split_comm m m1 m2 : split m m1 m2 <-> split m m2 m1.
  Proof. cbv [split]. pose proof disjoint_comm m1 m2. intuition idtac. all:rewrite union_comm; eauto. Qed.

  Lemma split_disjoint_union : forall x y, disjoint x y -> split (union x y) x y.
  Proof. cbv [split]; intuition eauto. Qed.

  Lemma split_empty_r m1 m2 : split m1 m2 empty <-> m1 = m2.
  Proof. cbv [split]. erewrite union_empty_r. intuition eauto using disjoint_empty_r. Qed.
  Lemma split_empty_l m1 m2 : split m1 empty m2 <-> m1 = m2.
  Proof. rewrite split_comm. eapply split_empty_r. Qed.
  Lemma split_empty m1 m2 : split empty m1 m2 <-> (m1 = empty /\ m2 = empty).
  Proof.
    cbv [split].
    unshelve erewrite (_:forall a b, a=b<->b=a); [intuition congruence|].
    rewrite empty_union.
    intuition idtac. subst. eapply disjoint_empty_l.
  Qed.

  Lemma get_split k m m1 m2 (H : split m m1 m2) :
    (get m k = get m1 k /\ get m2 k = None) \/ (get m k = get m2 k /\ get m1 k = None).
  Proof.
    destruct H as [?Hm H]; subst m.
    destruct (get m1 k) eqn:?; [ left | right ];
      destruct (get m2 k) eqn:?; [ solve[edestruct H; eauto] | | | ];
      erewrite ?get_union_left, ?get_union_right by eauto; eauto.
  Qed.
End Decomp.