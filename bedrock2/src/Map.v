Module map.
  Class map {key value : Type} := {
    rep : Type;
     
    empty : rep;
    get : rep -> key -> option value;
    put : rep -> key -> value -> rep;
    union : rep -> rep -> rep; (* rightmost takes priority *)
  }.
  Arguments map : clear implicits.

  Section ListOperations.
    Context {key value} {map : map key value}.
    Fixpoint putmany (keys : list key) (values : list value) (m : rep) {struct keys} : option rep :=
      match keys, values with
      | nil, nil => Some m
      | cons b binders, cons v values =>
        putmany binders values (put m b v)
      | _, _ => None
      end.
  End ListOperations.

  Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
  Section Properties.
    (* FIXME: move proofs to a different file *)
    Context {key value} {map : map key value}.
    Context (map_ext : forall m1 m2, (forall k, get m1 k = get m2 k) -> m1 = m2).
    Context (union_None : forall m1 m2 k, get m2 k = None -> get (union m1 m2) k = get m1 k).
    Context (union_Some : forall m1 m2 k v, get m2 k = Some v -> get (union m1 m2) k = Some v).
    
    Definition disjoint (a b : rep) : Prop :=
      forall k v1 v2, get a k = Some v1 -> get b k = Some v2 -> False.

    Lemma union_spec m1 m2 k :
      (exists v, get m2 k = Some v /\ get (union m1 m2) k = Some v) \/
      (get m2 k = None /\ get (union m1 m2) k = get m1 k).
    Proof.
      destruct (get m2 k) eqn:?HH; [left | right ].
      { exists v. split. reflexivity. erewrite union_Some; eauto. }
      { split. reflexivity. rewrite union_None; eauto. }
    Qed.

    Lemma union_comm x y : disjoint x y -> union x y = union y x.
    Proof.
      cbv [disjoint]; intros; eapply map_ext; intros.
      destruct (get x k) eqn:Hl, (get y k) eqn:Hr;
        repeat ((erewrite union_None by eauto) || (erewrite union_Some by eauto));
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
    
    Definition split m m1 m2 : Prop :=
      m = (union m1 m2) /\ disjoint m1 m2.
    Definition carve m1 m P2 : Prop :=
      exists m2, split m m1 m2 /\ P2 m2.
    Fixpoint splits m ms : Prop :=
      match ms with
      | nil => m = empty
      | cons m0 ms' => carve m0 m (fun m => splits m ms')
      end.
                              
    Lemma disjoint_comm m1 m2 : disjoint m1 m2 <-> disjoint m2 m1.
    Proof. cbv [disjoint]. firstorder idtac. Qed.
    Lemma disjoint_union_r x y z : disjoint x (union y z) <-> (disjoint x y /\ disjoint x z).
    Proof.
      cbv [disjoint].
      pose proof (union_spec y z) as HH.
      repeat split; intros; specialize (HH k);
        repeat (dintuition idtac; repeat match goal with H: exists _, _ |- _ => destruct H end).
      eapply (H k); eauto.
      eapply (H k); eauto; erewrite union_None; eauto.
      eapply (H k); eauto.
      eapply (H k); eauto.
      eapply (H3 k); eauto; erewrite union_None; eauto.
      eapply (H2 k); eauto. erewrite union_None in *; eauto.
    Qed.
    Lemma disjoint_union_l x y z : disjoint (union x y) z <-> (disjoint x z /\ disjoint y z).
    Proof. rewrite disjoint_comm. rewrite disjoint_union_r. rewrite 2(disjoint_comm z). reflexivity. Qed.
    Lemma split_comm m m1 m2 : split m m1 m2 <-> split m m2 m1.
    Proof. cbv [split]. pose proof disjoint_comm m1 m2. intuition idtac. all:rewrite union_comm; eauto. Qed.

    Lemma split_disjoint_union : forall x y, disjoint x y -> split (union x y) x y.
    Proof. cbv [split]; intuition eauto. Qed.
    Lemma carve_comm x y m l :
      carve y m (fun m_y : rep => carve x m_y (fun m_xy : rep => splits m_xy l)) <->
      carve x m (fun m_x : rep => carve y m_x (fun m_xy : rep => splits m_xy l)).
    Proof.
      cbv [carve].
      split; [ intros (m_y & (? & (m_yx & ? & ?)) ) | intros (m_x & (? & (m_xy & ? & ?)) ) ].
      { exists (union m_yx y). split.
        cbv [split] in *; intuition idtac. rewrite H2. rewrite H.
        { rewrite H in *; clear H. clear H1 H2.
          eapply disjoint_union_r in H3; destruct H3.
          rewrite (union_assoc x).
          3,4: eapply disjoint_comm; eauto.
          2: eauto.
          rewrite union_comm. 2:eapply disjoint_union_r; eauto.
          reflexivity. }
        { clear H2. rewrite H in *; clear H. eapply disjoint_union_r in H3; destruct H3.
          eapply disjoint_union_r. split. eauto. eapply disjoint_comm. eauto. }
        exists m_yx. split. eapply split_comm, split_disjoint_union.
        { cbv [split] in *; intuition idtac. clear H2. rewrite H in *.
          rewrite disjoint_union_r in H3; destruct H3. eapply disjoint_comm. eauto. }
        assumption. }
      { exists (union m_xy x). split.
        cbv [split] in *; intuition idtac. rewrite H2.
        { rewrite H in *; clear H. clear H1 H2.
          eapply disjoint_union_r in H3; destruct H3.
          rewrite (union_assoc y).
          2,3,4: eauto || eapply disjoint_comm; eauto.
          rewrite union_comm. 2: eapply disjoint_union_r; eauto.
          reflexivity. }
        { clear H2. rewrite H in *; clear H. eapply disjoint_union_r in H3; destruct H3.
          eapply disjoint_union_r. split. eauto. eapply disjoint_comm. eauto. }
        exists m_xy. split. eapply split_comm, split_disjoint_union.
        { cbv [split] in *; intuition idtac. clear H2. rewrite H in *.
          rewrite disjoint_union_r in H3; destruct H3. eapply disjoint_comm. eauto. }
        assumption. }
    Qed.

    Require Import Permutation.
    Require Import Coq.Classes.Morphisms.
    Lemma splits_Permutation m : Proper (@Permutation _ ==> iff) (splits m).
    Proof.
      cbv [Proper respectful]; intros x y H; revert m; induction H; intros;
        try solve [ eapply carve_comm | firstorder idtac ].
    Qed.

    Definition subsumes_using_split a b : Prop := exists c : rep, split a b c.
    Definition subsumes a b := forall k v, get b k = Some v -> get a k = Some v.
  End Properties.
  
End map. Notation map := map.map.
Global Coercion map.rep : map >-> Sortclass.