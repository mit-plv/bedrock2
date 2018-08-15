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
    Context (get_empty : forall k, get empty k = None).
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

    Lemma union_empty_r x : union x empty = x.
    Proof. eapply map_ext; intros; rewrite union_None; eauto. Qed.
    Lemma union_empty_l x : union empty x = x.
    Proof. rewrite (union_comm empty x) by congruence; eapply union_empty_r. Qed.
    
    Definition split m m1 m2 : Prop :=
      m = (union m1 m2) /\ disjoint m1 m2.
    Definition carve m1 m P2 : Prop :=
      exists m2, split m m2 m1 /\ P2 m2.
    Fixpoint splits m ms : Prop :=
      match ms with
      | nil => m = empty
      | cons m0 ms' => carve m0 m (fun m => splits m ms')
      end.
                              
    Lemma disjoint_empty_l x : disjoint empty x. repeat intro; congruence. Qed.
    Lemma disjoint_empty_r x : disjoint x empty. repeat intro; congruence. Qed.
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

    Definition impl1 {T} (P Q:_->Prop) : Prop := forall x:T, P x -> Q x.
    Global Instance Transitive_impl1 T : Transitive (@impl1 T). firstorder idtac. Qed.
    Global Instance Reflexive_impl1 T : Reflexive (@impl1 T). firstorder idtac. Qed.
    Global Instance Proper_impl1_impl1 T : Proper (Basics.flip impl1 ==> impl1 ==> Basics.impl) (@impl1 T). firstorder idtac. Qed.
    Definition iff1 {T} (P Q:_->Prop) : Prop := forall x:T, P x <-> Q x.
    Global Instance subrelation_iff1_impl1 T : subrelation (@iff1 T) (@impl1 T). firstorder idtac. Qed.
    Global Instance Equivalence_iff1 T : Equivalence (@iff1 T). firstorder idtac. Qed.
    Global Instance Proper_iff1_iff1 T : Proper (iff1 ==> iff1 ==> iff) (@iff1 T). firstorder idtac. Qed.
    Global Instance Proper_iff1_impl1 T : Proper (Basics.flip impl1 ==> impl1 ==> Basics.impl) (@impl1 T). firstorder idtac. Qed.
    Global Instance Proper_impl1_iff1 T : Proper (iff1 ==> iff1 ==> iff) (@impl1 T). firstorder idtac. Qed.
    Definition emp (P : Prop) := fun m => m = empty /\ P.
    Global Instance Proper_emp_iff : Proper (iff ==> iff1) emp. firstorder idtac. Qed.
    Global Instance Proper_emp_impl : Proper (Basics.impl ==> impl1) emp. firstorder idtac. Qed.
    Definition sep (p q : rep -> Prop) m :=
      exists mp mq, split m mp mq /\ p mp /\ q mq.
    Local Infix "*" := sep.
    Global Instance Proper_sep_iff1 : Proper (iff1 ==> iff1 ==> iff1) sep. firstorder idtac. Qed.
    Global Instance Proper_sep_impl1 : Proper (impl1 ==> impl1 ==> impl1) sep. firstorder idtac. Qed.
    Definition ptsto k v := fun m => m = put empty k v.
    Definition exi {T} (P : T -> rep -> Prop) := fun m => exists x:T, P x m.
    Global Instance Proper_exi_iff1 T : Proper (pointwise_relation _ iff1 ==> iff1) (@exi T). firstorder idtac. Qed.
    Global Instance Proper_exi_impl1 T : Proper (pointwise_relation _ impl1 ==> impl1) (@exi T). firstorder idtac. Qed.
    Definition read k (P : value -> rep -> Prop) := (exi (fun v => ptsto k v * P v)).
    

    Lemma sep_comm p q : iff1 (p*q) (q*p).
    Proof. cbv [iff1 sep split]; firstorder (subst; eauto using union_comm). Qed.
    Lemma sep_assoc p q r : iff1 ((p*q)*r) (p*(q*r)).
    Proof. cbv [iff1 sep split]; split; t;
           eauto 15 using eq_sym, union_assoc, ((fun m1 m2 m3 => proj2 (disjoint_union_l m1 m2 m3))), ((fun m1 m2 m3 => proj2 (disjoint_union_r m1 m2 m3))).
    Qed.
    Lemma sep_cancel (p1 p2 q1 q2:_->Prop) (_:impl1 p1 p2) (_:impl1 q1 q2) : impl1 (p1*q1) (p2*q2).
    Proof. cbv [impl1 sep]; firstorder idtac. Qed.
    Lemma sep_emp_emp p q : iff1 (sep (emp p) (emp q)) (emp (p /\ q)).
    Proof. cbv [iff1 sep emp split]; t; intuition eauto 20 using union_empty_l, disjoint_empty_l. Qed.
    Lemma sep_exi_r {T} p q : iff1 (p * @exi T q) (exi (fun h => p * q h)).
    Proof. cbv [exi sep]; firstorder idtac. Qed.
    Lemma sep_exi_l {T} p q : iff1 (@exi T q * p) (exi (fun h => q h * p)).
    Proof. rewrite sep_comm. rewrite sep_exi_r. setoid_rewrite (sep_comm p). reflexivity. Qed.
    Lemma impl1_exi_l {T} p q : impl1 (exi p) q <-> (forall x:T, impl1 (p x) q).
    Proof. cbv [exi sep impl1]; firstorder idtac. Qed.
    Lemma impl1_exi_r {T} p q (x:T) : impl1 p (q x) -> impl1 p (exi q).
    Proof. cbv [exi sep impl1]; firstorder idtac. Qed.

    Lemma sep_213 B A C : iff1 (A * (B * C)) (B * (A * C)).
    Proof. rewrite <-(fun a b => sep_assoc a B b), (fun a => sep_comm a B), sep_assoc. reflexivity. Qed.
    Lemma sep_emp_r a b : iff1 (a * emp b) (emp b * a). eapply sep_comm. Qed.
    Lemma sep_emp_2 a b c : iff1 (a * (emp b * c)) (emp b * (a * c)).
    Proof. rewrite <-sep_assoc. rewrite (sep_comm a). rewrite sep_assoc. reflexivity. Qed.
    Lemma sep_emp_12 a b c : iff1 (emp a * (emp b * c)) (emp (a /\ b) * c).
    Proof. rewrite <-sep_assoc. rewrite sep_emp_emp. reflexivity. Qed.

    Lemma impl1_l_sep_emp (a:Prop) b c : impl1 (emp a * b) c <-> (a -> impl1 b c).
    Proof.
      cbv [impl1 emp sep split]. firstorder idtac; subst; rewrite ?union_empty_l; eauto.
      eapply H. exists empty, x.  rewrite union_empty_l. repeat split; eauto using disjoint_empty_l.
    Qed.

    Lemma impl1_r_sep_emp a b c : (b /\ impl1 a c) -> impl1 a (emp b * c).
    Proof.
      cbv [impl1 emp sep split]. firstorder idtac; subst.
      exists empty, x. rewrite union_empty_l. repeat split; eauto using disjoint_empty_l.
    Qed.

    Ltac set_evars := repeat match goal with |- context[?e] => is_evar e; set e end.
    Ltac subst_evars := repeat match goal with x := ?e |- _ => is_evar e; subst x end.
    Ltac normalize :=
      set_evars;
      repeat (rewrite_strat (bottomup (terms @sep_emp_emp @sep_emp_r @sep_emp_12 @sep_emp_2 @sep_exi_l @sep_exi_r @sep_assoc)));
      subst_evars.
    Ltac cancel_atom_goal1 P :=
      (* COQBUG: if I use fresh here, rewrite_strat fails *)
      pose proof (sep_213 P) as _cancel_atom_goal1_ASDA;
      (rewrite_strat (try (bottomup (terms _cancel_atom_goal1_ASDA))));
      clear _cancel_atom_goal1_ASDA.
    Ltac cancel_atom P :=
      eapply Proper_impl1_impl1; [ cbv [Basics.flip]; cancel_atom_goal1 P; eapply (Proper_sep_impl1 P _ (reflexivity _)) | reflexivity | reflexivity ].
    Ltac cancel :=
      lazymatch goal with |- impl1 _ (_ * _) => idtac end;
      set_evars;
      repeat match goal with |- impl1 _ (?P * _) => cancel_atom P end;
      subst_evars.

    Goal forall A B C D E, exists R, impl1 (A*emp True*B*exi(fun x:unit => C*(exi (fun v : value => (emp (x = x)* emp(v =v))*E v x)))*D) (A * exi (fun n => C * emp (1=n)) * R).
    Proof.
      intros.
      normalize.
      eexists ?[R].
      eapply impl1_exi_r.
      eapply impl1_r_sep_emp.
      split. reflexivity.
      apply impl1_exi_l. intros.
      apply impl1_exi_l. intros.
      apply impl1_l_sep_emp. intros.
      cancel.
      instantiate (1 := exi (fun x0 => exi (fun x => (B * (E x0 x * D))))).
      eapply impl1_exi_r.
      eapply impl1_exi_r.
      reflexivity.
    Qed.
  End Properties.
  
End map. Notation map := map.map.
Global Coercion map.rep : map >-> Sortclass.