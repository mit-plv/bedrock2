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

  Ltac t :=
    repeat match goal with
    | _ => progress subst
    | H:_ /\ _ |- _ => destruct H
    | H:exists _, _ |- _ => destruct H
    | H:disjoint (union _ _) _ |- _ => eapply disjoint_union_l in H; destruct H
    | H:disjoint _ (union _ _) |- _ => eapply disjoint_union_r in H; destruct H
    | _ => progress intuition idtac
    end.

  Ltac carve_comm_t := repeat match goal with
    | _ => progress t
    | |- union (union ?a ?b) ?c = union (union ?a ?c) ?b  =>
      rewrite <-2union_assoc by eauto using (fun m1 m2 => proj2 (disjoint_comm m1 m2));
      rewrite (union_comm b c) by eauto using ((fun m1 m2 m3 => proj2 (disjoint_union_r m1 m2 m3)));
      reflexivity
    | _ => solve [eauto using ((fun m1 m2 m3 => proj2 (disjoint_union_r m1 m2 m3))), (fun m1 m2 => proj2 (disjoint_comm m1 m2))]
    | _ => solve [eapply union_comm; eauto using ((fun m1 m2 m3 => proj2 (disjoint_union_r m1 m2 m3))), (fun m1 m2 => proj2 (disjoint_comm m1 m2))]
  end.
  
  Lemma carve_comm x y m l :
    carve y m (fun m_y : rep => carve x m_y (fun m_xy : rep => splits m_xy l)) <->
    carve x m (fun m_x : rep => carve y m_x (fun m_xy : rep => splits m_xy l)).
  Proof.
    cbv [carve split]; split; intros (? & (? & (? & ? & ?)) );
      match goal with M : rep, z : rep |- _ => solve [exists (union M z); carve_comm_t] end.
  Qed.

  Require Import Permutation.
  Require Import Coq.Classes.Morphisms.
  Global Instance splits_Permutation m : Proper (@Permutation _ ==> iff) (splits m).
  Proof.
    cbv [Proper respectful]; intros x y H; revert m; induction H; intros;
      try solve [ eapply carve_comm | firstorder idtac ].
  Qed.
End Decomp.