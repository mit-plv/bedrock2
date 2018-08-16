Module map.
  Class map {key value : Type} := {
    rep : Type;
     
    empty : rep;
    get : rep -> key -> option value;
    put : rep -> key -> value -> rep;
    union : rep -> rep -> rep; (* rightmost takes priority *)
  }.
  Arguments map : clear implicits.

  Class ok {key value} (map : map key value) := {
    map_ext : forall m1 m2, (forall k, get m1 k = get m2 k) -> m1 = m2;
    get_empty : forall k, get empty k = None;
    get_put_same : forall m k v, get (put m k v) k = Some v;
    get_put_diff : forall m k v k', k <> k' -> get (put m k' v) k = get m k;
    get_union_left : forall m1 m2 k, get m2 k = None -> get (union m1 m2) k = get m1 k;
    get_union_right : forall m1 m2 k v, get m2 k = Some v -> get (union m1 m2) k = Some v;
  }.

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

  Section Decomp.
    Context {key value} {map : map key value}.
    Definition disjoint (a b : rep) : Prop :=
      forall k v1 v2, get a k = Some v1 -> get b k = Some v2 -> False.
    Definition split m m1 m2 : Prop :=
      m = (union m1 m2) /\ disjoint m1 m2.
    Definition carve m1 m P2 : Prop :=
      exists m2, split m m2 m1 /\ P2 m2.
    Fixpoint splits m ms : Prop :=
      match ms with
      | nil => m = empty
      | cons m0 ms' => carve m0 m (fun m => splits m ms')
      end.
  End Decomp.

  Require Import Coq.Setoids.Setoid Coq.Classes.Morphisms.
  Section Properties.
    (* FIXME: move proofs to a different file *)
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
  End Properties.

  Section Lift1Prop.
    Definition impl1 {T} (P Q:_->Prop) : Prop := forall x:T, P x -> Q x.
    Definition iff1 {T} (P Q:_->Prop) : Prop := forall x:T, P x <-> Q x.
    Definition ex1 {A B} (P : A -> B -> Prop) := fun (b:B) => exists a:A, P a b.
    Global Instance Transitive_impl1 T : Transitive (@impl1 T). firstorder idtac. Qed.
    Global Instance Reflexive_impl1 T : Reflexive (@impl1 T). firstorder idtac. Qed.
    Global Instance Proper_impl1_impl1 T : Proper (Basics.flip impl1 ==> impl1 ==> Basics.impl) (@impl1 T). firstorder idtac. Qed.
    Global Instance subrelation_iff1_impl1 T : subrelation (@iff1 T) (@impl1 T). firstorder idtac. Qed.
    Global Instance Equivalence_iff1 T : Equivalence (@iff1 T). firstorder idtac. Qed.
    Global Instance Proper_iff1_iff1 T : Proper (iff1 ==> iff1 ==> iff) (@iff1 T). firstorder idtac. Qed.
    Global Instance Proper_iff1_impl1 T : Proper (Basics.flip impl1 ==> impl1 ==> Basics.impl) (@impl1 T). firstorder idtac. Qed.
    Global Instance Proper_impl1_iff1 T : Proper (iff1 ==> iff1 ==> iff) (@impl1 T). firstorder idtac. Qed.
    Global Instance Proper_ex1_iff1 A B : Proper (pointwise_relation _ iff1 ==> iff1) (@ex1 A B). firstorder idtac. Qed.
    Global Instance Proper_ex1_impl1 A B : Proper (pointwise_relation _ impl1 ==> impl1) (@ex1 A B). firstorder idtac. Qed.
    Lemma impl1_ex1_l {A B} p q : impl1 (@ex1 A B p) q <-> (forall x, impl1  (p x) q).
    Proof. firstorder idtac. Qed.
    Lemma impl1_ex1_r {A B} p q x : impl1 p (q x) -> impl1 p (@ex1 A B q).
    Proof. firstorder idtac. Qed.
  End Lift1Prop.

  Section Sep.
    Context {key value} {map : map key value}.
    Definition emp (P : Prop) := fun m => m = empty /\ P.
    Definition sep (p q : rep -> Prop) m :=
      exists mp mq, split m mp mq /\ p mp /\ q mq.
    Definition ptsto k v := fun m => m = put empty k v.
    Definition read k (P : value -> rep -> Prop) := (ex1 (fun v => sep (ptsto k v) (P v))).
  End Sep.

  Section SepProperties.
    Context {key value} {map : map key value} {ok : ok map}.
    Local Infix "*" := sep.

    Global Instance Proper_emp_iff : Proper (iff ==> iff1) emp. firstorder idtac. Qed.
    Global Instance Proper_emp_impl : Proper (Basics.impl ==> impl1) emp. firstorder idtac. Qed.
    Global Instance Proper_sep_iff1 : Proper (iff1 ==> iff1 ==> iff1) sep. firstorder idtac. Qed.
    Global Instance Proper_sep_impl1 : Proper (impl1 ==> impl1 ==> impl1) sep. firstorder idtac. Qed.

    Ltac t :=
      repeat match goal with
      | _ => progress subst
      | H:_ /\ _ |- _ => destruct H
      | H:exists _, _ |- _ => destruct H
      | H:disjoint (union _ _) _ |- _ => eapply disjoint_union_l in H; destruct H
      | H:disjoint _ (union _ _) |- _ => eapply disjoint_union_r in H; destruct H
      | _ => progress intuition idtac
      end.

    (* sep and sep *)
    Lemma sep_comm p q : iff1 (p*q) (q*p).
    Proof. cbv [iff1 sep split]; t; eauto 10 using union_comm, (fun m1 m2 => proj2 (disjoint_comm m1 m2)). Qed.
    Lemma sep_assoc p q r : iff1 ((p*q)*r) (p*(q*r)).
    Proof. cbv [iff1 sep split]; t; eauto 15 using eq_sym, union_assoc, ((fun m1 m2 m3 => proj2 (disjoint_union_l m1 m2 m3))), ((fun m1 m2 m3 => proj2 (disjoint_union_r m1 m2 m3))). Qed.
    Lemma sep_213 B A C : iff1 (A * (B * C)) (B * (A * C)).
    Proof. rewrite <-(sep_assoc _ B), (sep_comm _ B), sep_assoc. reflexivity. Qed.

    (* sep and ex1 *)
    Lemma sep_ex1_r {T} p (q:T->_) : iff1 (p * ex1 q) (ex1 (fun h => p * q h)).
    Proof. firstorder idtac. Qed.
    Lemma sep_ex1_l {T} p (q:T->_) : iff1 (ex1 q * p) (ex1 (fun h => q h * p)).
    Proof. rewrite sep_comm. rewrite sep_ex1_r. setoid_rewrite (sep_comm p). reflexivity. Qed.

    (* sep and emp *)
    Lemma sep_emp_emp p q : iff1 (sep (emp p) (emp q)) (emp (p /\ q)).
    Proof. cbv [iff1 sep emp split]; t; intuition eauto 20 using union_empty_l, disjoint_empty_l. Qed.
    Lemma sep_emp_r a b : iff1 (a * emp b) (emp b * a). eapply sep_comm. Qed.
    Lemma sep_emp_2 a b c : iff1 (a * (emp b * c)) (emp b * (a * c)).
    Proof. rewrite <-sep_assoc. rewrite (sep_comm a). rewrite sep_assoc. reflexivity. Qed.
    Lemma sep_emp_12 a b c : iff1 (emp a * (emp b * c)) (emp (a /\ b) * c).
    Proof. rewrite <-sep_assoc. rewrite sep_emp_emp. reflexivity. Qed.

    (* impl1 and emp *)
    Lemma impl1_l_sep_emp (a:Prop) b c : impl1 (emp a * b) c <-> (a -> impl1 b c).
    Proof. cbv [impl1 emp sep split]; t; rewrite ?union_empty_l; eauto 10 using union_empty_l, disjoint_empty_l. Qed.
    Lemma impl1_r_sep_emp a b c : (b /\ impl1 a c) -> impl1 a (emp b * c).
    Proof. cbv [impl1 emp sep split]; t; eauto 10 using union_empty_l, disjoint_empty_l. Qed.

    Ltac set_evars := repeat match goal with |- context[?e] => is_evar e; set e end.
    Ltac subst_evars := repeat match goal with x := ?e |- _ => is_evar e; subst x end.
    Ltac normalize :=
      set_evars;
      (* COQBUG? Why is the repeat necessary? Why does it not work inside rewrite_strat? *)
      repeat (rewrite_strat (bottomup (terms @sep_emp_emp @sep_emp_r @sep_emp_12 @sep_emp_2 @sep_ex1_l @sep_ex1_r @sep_assoc)));
      subst_evars.
    Ltac cancel_atom_goal1 P :=
      (* COQBUG: if I use fresh here, rewrite_strat fails *)
      pose proof (sep_213 P) as __PRIVATE_cancel_atom_goal1_ASDA;
      (rewrite_strat (try (bottomup (terms __PRIVATE_cancel_atom_goal1_ASDA))));
      clear __PRIVATE_cancel_atom_goal1_ASDA.
    Ltac cancel_atom P :=
      eapply Proper_impl1_impl1; [ cbv [Basics.flip]; cancel_atom_goal1 P; eapply (Proper_sep_impl1 P _ (reflexivity _)) | reflexivity | reflexivity ].
    Ltac cancel :=
      lazymatch goal with |- impl1 _ (_ * _) => idtac end;
      set_evars;
      repeat match goal with |- impl1 _ (?P * _) => cancel_atom P end;
      subst_evars.

    Goal forall A B C D E, exists R, impl1 (A*emp True*B*ex1(fun x:unit => C*(ex1 (fun v : value => (emp (x = x)* emp(v =v))*E v x)))*D) (A * ex1 (fun n => C * emp (1=n)) * R).
    Proof.
      intros.
      normalize.
      eexists ?[R].
      eapply impl1_ex1_r.
      eapply impl1_r_sep_emp.
      split. reflexivity.
      apply impl1_ex1_l. intros.
      apply impl1_ex1_l. intros.
      apply impl1_l_sep_emp. intros.
      cancel.
      (* packaging up the context: *)
      instantiate (1 := ex1 (fun x0 => ex1 (fun x => (B * (E x0 x * D))))).
      eapply impl1_ex1_r.
      eapply impl1_ex1_r.
      reflexivity.
    Qed.
  End SepProperties.
  
End map. Notation map := map.map.
Global Coercion map.rep : map >-> Sortclass.