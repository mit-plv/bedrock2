Require Import Coq.Classes.Morphisms.
Require Import bedrock2.Map bedrock2.Map.Decomp bedrock2.Lift1Prop bedrock2.Map.Separation. Import map.
Require Coq.Lists.List.

Section SepProperties.
  Context {key value} {map : map key value} {ok : ok map}.
  Local Infix "*" := sep.

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

  Lemma get_ptsto k v m (H : ptsto k v m) : get m k = Some v.
  Proof. rewrite H, get_put_same; trivial. Qed.
  Lemma get_sep k v R m (H : sep (ptsto k v) R m) : get m k = Some v.
  Proof.
    destruct H as (mk&mR&H&Hp&HR); eapply get_ptsto in Hp; subst.
    destruct (get_split k _ _ _ H) as [[]|[]]; congruence.
  Qed.
  Lemma sep_put (key_eq_dec : forall k1 k2 : key, k1 = k2 \/ k1 <> k2)
        k v m v_old R (H : sep (ptsto k v_old) R m) : sep (ptsto k v) R (put m k v).
  Proof.
    eapply sep_comm in H; eapply sep_comm.
    destruct H as (mR&mk&[Heq Hd]&HR&Hp); cbv [ptsto] in Hp; subst mk; subst m.
    exists mR, (put empty k v); split; [|solve[repeat split; trivial]]; split.
    { eapply map_ext; intro k'; destruct (key_eq_dec k' k); try subst k';
        rewrite ?get_put_same, ?get_put_diff by trivial.
      { erewrite get_union_right; trivial. rewrite get_put_same; trivial. }
      { rewrite 2get_union_left; trivial. all:rewrite get_put_diff, get_empty; trivial. } }
    { intros k' ? ? ? Hget; intros; destruct (key_eq_dec k' k); try subst k'.
      { eapply Hd; eauto using get_put_same. }
      { rewrite get_put_diff, get_empty in Hget by trivial; inversion Hget. } }
  Qed.

  Lemma iff1_sep_cancel P Q1 Q2 (H : iff1 Q1 Q2) : iff1 (P * Q1) (P * Q2).
  Proof. exact (Proper_sep_iff1 _ _ (reflexivity _) _ _ H). Qed.

  (* More Conntectives *)
  Global Instance Proper_emp_iff : Proper (iff ==> iff1) emp. firstorder idtac. Qed.
  Global Instance Proper_emp_impl : Proper (Basics.impl ==> impl1) emp. firstorder idtac. Qed.

  (* sep and emp *)
  Lemma sep_emp_emp p q : iff1 (sep (emp p) (emp q)) (emp (p /\ q)).
  Proof. cbv [iff1 sep emp split]; t; intuition eauto 20 using union_empty_l, disjoint_empty_l. Qed.
  Lemma sep_comm_emp_r a b : iff1 (a * emp b) (emp b * a). eapply sep_comm. Qed.
  Lemma sep_emp_2 a b c : iff1 (a * (emp b * c)) (emp b * (a * c)).
  Proof. rewrite <-sep_assoc. rewrite (sep_comm a). rewrite sep_assoc. reflexivity. Qed.
  Lemma sep_emp_12 a b c : iff1 (emp a * (emp b * c)) (emp (a /\ b) * c).
  Proof. rewrite <-sep_assoc. rewrite sep_emp_emp. reflexivity. Qed.

  Lemma sep_emp_l a b m : sep (emp a) b m <-> a /\ b m.
  Proof.
    split.
    { intros (?&?&(?&?)&(?&?)&?); subst; rewrite union_empty_l; auto. }
    { intros (?&?). exists empty, m.
      cbv [emp]; edestruct split_empty_l; intuition eauto. }
  Qed.
  Lemma sep_emp_r a b m : sep a (emp b) m <-> a m /\ b.
  Proof.
    setoid_rewrite (and_comm _ b).
    setoid_rewrite sep_comm || (etransitivity; [eapply sep_comm|]). (* WHY? *)
    eapply sep_emp_l.
  Qed.
  Lemma sep_emp_True_l p : iff1 (sep (emp True) p) p.
  Proof. intros m; rewrite sep_emp_l; intuition idtac. Qed.
  Lemma sep_emp_True_r p : iff1 (sep p (emp True)) p.
  Proof. intros m; rewrite sep_emp_r; intuition idtac. Qed.

  (* sep and ex1 *)
  Lemma sep_ex1_r {T} p (q:T->_) : iff1 (p * ex1 q) (ex1 (fun h => p * q h)).
  Proof. firstorder idtac. Qed.
  Lemma sep_ex1_l {T} p (q:T->_) : iff1 (ex1 q * p) (ex1 (fun h => q h * p)).
  Proof. rewrite sep_comm. rewrite sep_ex1_r. setoid_rewrite (sep_comm p). reflexivity. Qed.

  (* impl1 and emp *)
  Lemma impl1_l_sep_emp (a:Prop) b c : impl1 (emp a * b) c <-> (a -> impl1 b c).
  Proof. cbv [impl1 emp sep split]; t; rewrite ?union_empty_l; eauto 10 using union_empty_l, disjoint_empty_l. Qed.
  Lemma impl1_r_sep_emp a b c : (b /\ impl1 a c) -> impl1 a (emp b * c).
  Proof. cbv [impl1 emp sep split]; t; eauto 10 using union_empty_l, disjoint_empty_l. Qed.

  (* shallow reflection from a list of predicates *)
  Fixpoint seps' (xs : list (rep -> Prop)) : rep -> Prop :=
    match xs with
    | cons x xs => sep x (seps' xs)
    | nil => emp True
    end.
  Lemma seps'_iff1_seps xs : iff1 (seps' xs) (seps xs).
  Proof.
    induction xs; [exact (reflexivity _)|].
    destruct xs; [solve[eauto using sep_emp_True_r]|].
    eapply Proper_sep_iff1, IHxs.
    exact (reflexivity _).
  Qed.

  Let nth n xs := List.hd (emp True) (List.skipn n xs).
  Let remove_nth n (xs : list (rep -> Prop)) :=
    (List.firstn n xs ++ List.tl (List.skipn n xs))%list.
  Lemma seps_nth_to_head n xs : iff1 (sep (nth n xs) (seps (remove_nth n xs))) (seps xs).
  Proof.
    cbv [nth remove_nth].
    pose proof (List.firstn_skipn n xs).
    set (xsr := List.skipn n xs) in *; clearbody xsr.
    set (xsl := List.firstn n xs) in *; clearbody xsl.
    subst xs.
    setoid_rewrite <-seps'_iff1_seps.
    destruct xsr.
    { cbn [seps']; rewrite sep_emp_True_l, 2List.app_nil_r; exact (reflexivity _). }
    cbn [List.hd List.tl].
    induction xsl; cbn; [exact (reflexivity _)|].
    rewrite <-IHxsl; clear IHxsl.
    rewrite (sep_comm _ (seps' _)), <-(sep_assoc _ (seps' _)), <-(sep_comm _ (_ * seps' _)).
    exact (reflexivity _).
  Qed.
  Lemma cancel_seps_at_indices i j xs ys
        (Hij : iff1 (nth i xs) (nth j ys))
        (Hrest : iff1 (seps (remove_nth i xs)) (seps (remove_nth j ys)))
    : iff1 (seps xs) (seps ys).
  Proof.
    rewrite <-(seps_nth_to_head i xs), <-(seps_nth_to_head j ys), Hij, Hrest.
    exact (reflexivity _).
  Qed.
End SepProperties.

Require Import bedrock2.Tactics.syntactic_unify.

Notation "X '========' 'seps' 'iff' '========' Y" :=
  (Lift1Prop.iff1 (seps X) (seps Y))
    (at  level 200, no associativity,
     format "X '//' '========'  'seps'  'iff'  '========' '//' Y").

Ltac reify e :=
  lazymatch e with
  | seps ?xs => xs
  | @sep ?key ?value ?map ?a ?b =>
    let b := reify b in
    uconstr:(@cons (@map.rep key value map -> Prop) a b)
  | ?a => uconstr:(cons a nil)
  end.

Ltac reify_goal :=
  lazymatch goal with
  | |- Lift1Prop.iff1 ?LHS ?RHS =>
    let LHS := reify LHS in
    let RHS := reify RHS in
    change (Lift1Prop.iff1 (seps LHS) (seps RHS))
  | |- Lift1Prop.impl1 ?LHS ?RHS =>
    let LHS := reify LHS in
    let RHS := reify RHS in
    change (Lift1Prop.impl1 (seps LHS) (seps RHS))
  end.

Ltac index_and_element_of xs :=
  multimatch xs with
  | cons ?x _ => constr:((0%nat, x))
  | cons _ ?xs =>
    let r := index_and_element_of xs in
    multimatch r with
    | (?i, ?y) => constr:((S i, y))
    end
  end.

Ltac find_syntactic_unify xs y :=
  multimatch xs with
  | cons ?x _ => constr:(ltac:(syntactic_unify x y; exact 0%nat))
  | cons _ ?xs => let i := find_syntactic_unify xs y in constr:(S i)
  end.

Ltac ecancel :=
  reify_goal;
  repeat (
      let RHS := lazymatch goal with |- Lift1Prop.iff1 _ (seps ?RHS) => RHS end in
      let jy := index_and_element_of RHS in
      let j := lazymatch jy with (?i, _) => i end in
      let y := lazymatch jy with (_, ?y) => y end in
      assert_fails (is_evar y);

      let LHS := lazymatch goal with |- Lift1Prop.iff1 (seps ?LHS) _ => LHS end in
      let i := find_syntactic_unify LHS y in

      simple refine (cancel_seps_at_indices i j _ _ _ _);
      cbn [List.firstn List.skipn List.app List.hd List.tl];
      [exact (RelationClasses.reflexivity _)|]);
  cbn [seps]; try exact (RelationClasses.reflexivity _).
