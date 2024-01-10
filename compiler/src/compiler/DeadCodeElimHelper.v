Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Require Import coqutil.Map.MapEauto.
Open Scope Z_scope.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Datatypes.ListSet.
Local Notation var := String.string (only parsing).
Require Import compiler.util.Common.
Require Import bedrock2.MetricLogging.
Require Import coqutil.Tactics.fwd.
(*  below only for of_list_list_diff *)
Require Import Coq.Logic.PropExtensionality.
Require Import Coq.Logic.FunctionalExtensionality.

Section WithArguments0.
  Lemma existsb_eqb_in:
    forall x (l: list string),
      In x l <-> (existsb (eqb x) l = true).
  Proof.
    intros.
    unfold iff.
    split.
    - intros. eapply List.existsb_exists. exists x; split.
      + assumption.
      + eapply eqb_refl.
    - intros. apply List.existsb_exists in H.
      fwd. assumption.
  Qed.

  Lemma subset_of_list_cons:
    forall h t l,
      PropSet.subset (PropSet.of_list (h::t)) (PropSet.of_list l) <->
      existsb (eqb h) l = true /\ PropSet.subset (PropSet.of_list t) (PropSet.of_list l).
  Proof.
    intros.
    unfold iff.
    split.
    - rewrite of_list_cons. unfold add, subset, elem_of, union.
      propositional idtac.
      + specialize (Hyp h); unfold elem_of, singleton_set in *.
        eapply existsb_exists.
        eexists h.
        split.
        * unfold of_list in Hyp.
          eapply Hyp. left. reflexivity.
        * eapply eqb_eq. reflexivity.
      + eapply Hyp.
        right. unfold elem_of; auto.
    - intros.
      rewrite of_list_cons.
      unfold add, subset, elem_of, union.
      intros. propositional idtac.
      + unfold elem_of, singleton_set in H0. rewrite <- H0.
        eapply existsb_exists in H_l.
        destr H_l. destr H.
        eapply eqb_eq in H1.
        rewrite H1.
        unfold of_list. assumption.
      + eapply H_r, H0.
  Qed.


  Lemma subset_of_list_removeb:
    forall (l: list string) s,
      PropSet.subset (PropSet.of_list (List.removeb eqb s l))
        (PropSet.of_list (l)).
  Proof.
    intros. rewrite of_list_removeb.
    unfold PropSet.subset.
    intros.
    unfold PropSet.elem_of in H.
    unfold PropSet.diff in H.
    destr H.
    eapply H.
  Qed.

  Lemma subset_of_list_diff:
    forall  l' (l: list string),
      PropSet.subset (PropSet.of_list (list_diff eqb l l'))
        (PropSet.of_list l).
  Proof.
    intros.
    unfold subset.
    intros.
    unfold elem_of in *.
    unfold of_list in *.
    eapply In_list_diff_weaken.
    eapply H.
  Qed.


  Lemma superset_of_list_cons:
    forall h t l,
      PropSet.subset (PropSet.of_list l) (PropSet.of_list (h :: t)) <->
      forallb (fun x => ((eqb h x) || (existsb (eqb x) t))%bool) l = true.
  Proof.
    intros.
    unfold iff.
    split.
    - induction l.
      + simpl in *. eauto.
      + simpl in *. intros.
        apply subset_of_list_cons in H.
        destr H.
        simpl in H.
        apply andb_true_intro.
        split.
        * rewrite eqb_sym. eapply H.
        * eauto.
    - induction l.
      + simpl in *. intro. unfold PropSet.subset.
        intros.
        unfold PropSet.elem_of, PropSet.of_list in H0.
        inversion H0.
      + simpl. intros.
        apply andb_prop in H.
        destr H.
        apply subset_of_list_cons.
        split.
        * simpl. rewrite eqb_sym. eapply H.
        * eauto.
  Qed.

  Lemma forallb_implies:
    forall (l: list string) (f: string -> bool) (g: string -> bool),
      forallb f l = true ->
      (forall s, f s = true -> g s = true) ->
      forallb g l = true.
  Proof.
    induction l.
    - simpl. auto.
    - simpl. intros.
      apply andb_prop in H.
      destr H.
      apply andb_true_intro.
      split.
      + eauto.
      + eauto.
  Qed.

  Lemma superset_of_list_tail:
    forall h t (l: list string),
      PropSet.subset (PropSet.of_list l) (PropSet.of_list (t))
      -> PropSet.subset (PropSet.of_list l) (PropSet.of_list (h :: t)).
  Proof.
    intros.
    unfold subset.
    intros. unfold elem_of, of_list.
    eapply in_cons, H, H0.
  Qed.

  Lemma subset_of_list_tail:
    forall h (l1 l2: list string),
      PropSet.subset (PropSet.of_list l1) (PropSet.of_list l2) ->
      PropSet.subset (PropSet.of_list (h :: l1)) (PropSet.of_list (h :: l2)).
  Proof.
    unfold subset. intros.
    unfold elem_of in *.
    eapply in_inv in H0; destr H0.
    - rewrite H0. unfold of_list. eapply in_eq.
    - unfold of_list. eapply in_cons. unfold of_list in H. eauto.
  Qed.

  Lemma find_eqb:
    forall (l: list string) s s',
      find (eqb s) l = Some s' -> s = s'.
  Proof.
    induction l; simpl in *.
    - intros.
      inversion H.
    - intros. destr ((s =? a)%string).
      + inversion H. reflexivity.
      + eapply IHl in H. eapply H.
  Qed.

  Lemma existsb_find_some:
    forall (l: list string) s s',
      (find (eqb s) l = Some s') -> existsb (eqb s) l = true.
  Proof.
    intros.
    induction l.
    + simpl in *.
      inversion H.
    + simpl in H.
      destr (s =? a)%string.
      * inversion H. simpl in *.
        rewrite eqb_refl. eapply Bool.orb_true_l.
      * apply IHl in H. simpl.
        rewrite H.
        eapply Bool.orb_true_r.
  Qed.

  Lemma subset_of_list_split_union:
    forall s1 s1' s2 s2',
      subset (of_list s1) (of_list s1')
      -> subset (of_list s2) (of_list s2')
      -> subset (of_list (list_union eqb s1 s2)) (of_list (list_union eqb s1' s2')).
  Proof.
    intros. repeat rewrite of_list_list_union.
    eapply subset_union_l.
    - eapply subset_union_rl. assumption.
    - eapply subset_union_rr. assumption.
  Qed.

  Lemma subset_of_list_union:
    forall s1a s1b s2,
      subset (of_list s1a) (of_list s2) ->
      subset (of_list s1b) (of_list s2) ->
      subset (of_list (list_union eqb s1a s1b)) (of_list s2).
  Proof.
    intros. rewrite of_list_list_union.
    eapply subset_union_l; assumption.
  Qed.

  Lemma subset_of_list_union_inv:
    forall s1a s1b s2,
      subset (of_list (list_union eqb s1a s1b)) (of_list s2) ->
      subset  (of_list s1a) (of_list s2) /\
        subset (of_list s1b) (of_list s2).
  Proof.
    intros.
    rewrite of_list_list_union in H.
    split.
    - unfold subset, union in *.
      unfold elem_of in *.
      intros. eapply H.
      eauto.
    - unfold subset, union in *.
      unfold elem_of in *.
      intros. eapply H.
      eauto.
  Qed.

  Lemma superset_of_list_union_l:
    forall s1 s2a s2b,
      subset (of_list s1) (of_list s2a) ->
      subset (of_list s1) (of_list (list_union eqb s2a s2b)).
  Proof.
    intros. rewrite of_list_list_union. eapply subset_union_rl; assumption.
  Qed.

  Lemma superset_of_list_union_r:
    forall s1 s2a s2b,
      subset (of_list s1) (of_list s2b) ->
      subset (of_list s1) (of_list (list_union eqb s2a s2b)).
  Proof.
    intros. rewrite of_list_list_union. eapply subset_union_rr; assumption.
  Qed.

  Lemma superset_of_list_union_comm:
    forall s1 s2a s2b,
      subset (of_list s1) (of_list (list_union eqb s2a s2b)) ->
      subset (of_list s1) (of_list (list_union eqb s2b s2a)).
  Proof.
    intros.
    rewrite of_list_list_union in *.
    eapply subset_trans.
    - eassumption.
    - eapply union_comm.
  Qed.


  Lemma superset_of_list_union_assoc:
    forall s1 s2a s2b s2c,
      subset (of_list s1) (of_list (list_union eqb (list_union eqb s2a s2b) s2c)) ->
      subset (of_list s1) (of_list (list_union eqb s2a (list_union eqb s2b s2c))).
  Proof.
    intros.
    repeat rewrite of_list_list_union in *.
    eapply subset_trans.
    - eassumption.
    - eapply union_assoc.
  Qed.

  Lemma subset_of_list_find_removeb:
    forall a x l,
      subset
        (of_list
           (if find (eqb a) (List.removeb eqb x l)
            then List.removeb eqb x l
            else a :: List.removeb eqb x l))
        (of_list (if find (eqb a) l then l else a :: l)).
  Proof.
    intros.
    destr (find (eqb a) l).
    - destr (find (eqb a) (List.removeb eqb x l)).
      + eapply subset_of_list_removeb.
      + eapply subset_of_list_cons.
        split.
        * eapply existsb_find_some.
          eassumption.
        * eapply subset_of_list_removeb.
    - destr (find (eqb a) (List.removeb eqb x l)).
      + eapply superset_of_list_tail.
        eapply subset_of_list_removeb.
      + eapply subset_of_list_tail.
        eapply subset_of_list_removeb.
  Qed.



  Lemma In_list_diff_spec:
   forall {E : Type} {eeq : E -> E -> bool},
     EqDecider eeq ->
     forall (l1 l2 : list E) (x : E),
       In x (list_diff eeq l1 l2) <-> In x l1 /\ (~ In x l2).
  Proof.
    induction l1.
    - simpl.
      intros.
      rewrite list_diff_empty_l.
      unfold iff.
      propositional idtac.
    - simpl. intros.
      rewrite list_diff_cons.
      destr (find (eeq a) l2).
      + unfold iff.
        split.
        * intros. eapply IHl1 in H0.
          propositional idtac.
        * intros.
          propositional idtac.
          2: { eapply IHl1.
               propositional idtac. }
          eapply find_some in E0.
          propositional idtac.
          destr (eeq x e).
          -- exfalso; auto.
          -- inversion E0_r.
      + unfold iff.
        split.
        * intros. specialize (find_none (eeq a) l2).
          intros.
          assert (forall x : E, In x l2 -> eeq a x = false).
          { eauto. }
          inversion H0.
          -- propositional idtac; eauto.
             eapply H1 in H3.
             destr (eeq x x).
             ++ inversion H3.
             ++ eapply E1. reflexivity.
          -- eapply IHl1 in H3.
             propositional idtac.
        * intros.
          propositional idtac.
          -- eapply in_eq.
          -- eapply in_cons. eapply IHl1. propositional idtac.
  Qed.

  Lemma of_list_list_diff :
    forall {E : Type} {eeq : E -> E -> bool},
      EqDecider eeq ->
      forall l1 l2 : list E,
        of_list (list_diff eeq l1 l2) = diff (of_list l1) (of_list l2).
  Proof.
    intros.
    extensionality e. apply propositional_extensionality.
    unfold of_list, diff, elem_of.
    eapply In_list_diff_spec.
    assumption.
  Qed.

  Ltac subset_union_solve :=
    match goal  with
    | |- subset (union _ _) _  => eapply subset_union_l; subset_union_solve
    | |- subset _ (union _ _)  =>
        try solve [ eapply subset_union_rl; subset_union_solve ]; try solve [ eapply subset_union_rr; subset_union_solve ]; idtac
    | |- subset ?x ?x => solve [ eapply subset_refl ]
    | |- _ => fail
    end.

  Ltac listset_to_set :=
    match goal with
    | H: context[of_list (ListSet.list_union _ _ _)] |- _ => rewrite ListSet.of_list_list_union in H
    | H: context[of_list (ListSet.list_diff _ _ _)] |- _ =>
        rewrite of_list_list_diff in H;
        try match goal with
          | |- EqDecider String.eqb => eapply String.eqb_spec
          end
    | H: context[of_list (List.removeb _ _ _)] |- _ =>
        rewrite ListSet.of_list_removeb in H
    end.

   Lemma sameset_union:
    forall (s1 s2 s1' s2': set string),
      sameset s1 s1' ->
      sameset s2 s2' ->
      sameset (union s1 s2) (union s1' s2').
  Proof.
    intros.
    unfold sameset, union.
    split.
    - unfold sameset, subset in *.
      propositional idtac.
      assert (x \in s1 \/ x \in s2) by auto.
      cut (x \in s1' \/ x \in s2'); [ auto |  ].
      destr H.
      + left; eauto.
      + right; eauto.
    - unfold sameset, subset in *.
      propositional idtac.
      assert (x \in s1' \/ x \in s2') by auto.
      cut (x \in s1 \/ x \in s2); [ auto |  ].
      destr H.
      + left; eauto.
      + right; eauto.
  Qed.

  Lemma agree_on_cons:
    forall {var: Type} {var_eqb: var -> var -> bool},
      EqDecider var_eqb ->
      forall {val: Type} {map': map.map var val},
        map.ok map' ->
         forall (k: var) ks (m1 m2: map'),
      map.agree_on (of_list (k :: ks)) m1 m2 ->
        map.agree_on (of_list ks) m1 m2 /\
          map.get m1 k = map.get m2 k.
  Proof.
    unfold map.agree_on, of_list, elem_of in *.
    propositional idtac; eauto using in_cons, in_eq.
  Qed.

  Lemma agree_on_getmany:
    forall {var: Type} {var_eqb: var -> var -> bool},
      EqDecider var_eqb ->
      forall {val: Type} {map': map.map var val},
        map.ok map' ->
    forall ks (m1 m2: map'),
      map.agree_on (of_list ks) m1 m2 ->
      map.getmany_of_list m1 ks =
        map.getmany_of_list m2 ks.
  Proof.
    intros.
    unfold map.getmany_of_list, map.agree_on.
    induction ks.
    - simpl. reflexivity.
    - simpl.
      pose proof H as H'.
      unfold map.agree_on in H.
      assert (map.get m1 a = map.get m2 a).
      { eapply agree_on_cons in H1.
        - destr H1. eassumption.
        - eapply H'.
        - eassumption. }
      rewrite H2.
      rewrite IHks.
      + reflexivity.
      + eapply agree_on_cons in H1.
        2-3: eassumption. propositional idtac.
  Qed.


  Lemma agree_on_subset:
    forall {var: Type} {var_eqb: var -> var -> bool},
      EqDecider var_eqb ->
      forall {val: Type} {map': map.map var val},
        map.ok map' ->
    forall ks ks' (m1 m2: map'),
      subset ks' ks ->
      map.agree_on ks m1 m2 ->
      map.agree_on ks' m1 m2.
  Proof.
    intros.
    unfold map.agree_on, subset in *.
    intros.
    eapply H2.
    eapply H1.
    eassumption.
  Qed.

  Lemma agree_on_comm :
    forall {var: Type} {var_eqb: var -> var -> bool},
      EqDecider var_eqb ->
      forall {val: Type} {map': map.map var val},
        map.ok map' ->
    forall ks (m1 m2: map'),
      map.agree_on ks m1 m2 ->
      map.agree_on ks m2 m1.
  Proof.
    intros.
    unfold map.agree_on in *.
    intros.
    symmetry.
    eauto.
  Qed.
  Ltac agree_on_solve :=
    match goal with
    | H: map.agree_on ?s ?x ?y |-
        map.agree_on _ ?x ?y =>
        eapply agree_on_subset with (ks := s);
        [ subset_union_solve | eapply H]
    | H: map.agree_on ?s ?x ?y |-
        map.agree_on _ ?y ?x =>
        eapply agree_on_comm; agree_on_solve
    | _ => idtac
    end.

  Lemma agree_on_union:

    forall {var: Type} {var_eqb: var -> var -> bool},
      EqDecider var_eqb ->
      forall {val: Type} {map': map.map var val},
        map.ok map' ->
        forall s0 s1 (m0 m1: map'),
      map.agree_on (union s0 s1) m0 m1
      <-> map.agree_on s0 m0 m1 /\ map.agree_on s1 m0 m1.
  Proof.
    intros.
    unfold iff; split; unfold map.agree_on in *.
    - split; intros; cut (s0 k \/ s1 k); auto.
    - intros; destr H1; cut (s0 k \/ s1 k); auto.
      intros; destr H4; auto.
  Qed.

  Lemma agree_on_sameset:

    forall {var: Type} {var_eqb: var -> var -> bool},
      EqDecider var_eqb ->
      forall {val: Type} {map': map.map var val},
        map.ok map' ->
        forall s1 s2 (m1 m2: map'),
      map.agree_on s2 m1 m2 ->
      sameset s1 s2 ->
      map.agree_on s1 m1 m2.
  Proof.
    intros.
    eapply agree_on_subset; eauto; eapply H2.
  Qed.


  Lemma sameset_union_diff_of_list:
     forall {var: Type} {var_eqb: var -> var -> bool},
      EqDecider var_eqb -> forall (l1 l2: list var),
      sameset (union (of_list l1) (of_list l2)) (union (diff (of_list l1) (of_list l2) ) (of_list l2)).
  Proof.
    intros.
    unfold sameset, of_list, subset, union, diff, elem_of.
    split; intros; unfold elem_of in *.
    - propositional idtac.

    assert (In x l2 \/ ~ (In x l2)).
    { eapply ListDec.In_decidable. unfold ListDec.decidable_eq.
      intros. destr (var_eqb x0 y).
      - unfold Decidable.decidable. left. reflexivity.
      - unfold Decidable.decidable. right. eassumption.
    }
    propositional idtac.
    - propositional idtac.
  Qed.

    Lemma agree_on_put:
     forall {var: Type} {var_eqb: var -> var -> bool},
      EqDecider var_eqb ->
      forall {val: Type} {map': map.map var val},
        map.ok map' -> forall a r s (mH mL: map')  mH' mL',
      map.agree_on s mH mL ->
      map.put mH a r = mH' ->
      map.put mL a r = mL' ->
      map.agree_on (union s (singleton_set a)) mH' mL'.
  Proof.
    intros.
    eapply agree_on_union; try solve [eassumption].
    split.
    - unfold map.agree_on in *.
      intros.
      eapply H1 in H4.
      subst.
      destr (var_eqb a k).
      + repeat rewrite map.get_put_same; reflexivity.
      + repeat rewrite map.get_put_diff; eauto.
    - unfold map.agree_on.
      intros.
      cut (a = k).
      + intros. subst.
        repeat rewrite map.get_put_same; reflexivity.
      + assert (singleton_set a k) by auto.
        unfold singleton_set in *; assumption.
  Qed.

  Lemma agree_on_diff_put:
     forall {var: Type} {var_eqb: var -> var -> bool},
      EqDecider var_eqb ->
      forall {val: Type} {map': map.map var val},
        map.ok map' ->
    forall a r s (mH mL: map'),
      map.agree_on (diff (of_list s) (singleton_set a)) mH mL ->
                    map.agree_on (of_list s)  (map.put mH a r) (map.put mL a r).
   Proof.
     intros.
     eapply agree_on_subset; try solve [eassumption].
     2: {
      eapply agree_on_put; try solve [eassumption].
      2: reflexivity.
      reflexivity.
     }

     replace (singleton_set a) with (of_list [a]).

     2: { erewrite singleton_set_eq_of_list. reflexivity. }
     eapply subset_trans.
     2: eapply sameset_union_diff_of_list.
     2: eassumption.
     subset_union_solve.
   Qed.

   Lemma agree_on_putmany_of_list_zip:

     forall {var: Type} {var_eqb: var -> var -> bool},
      EqDecider var_eqb ->
      forall {val: Type} {map': map.map var val},
        map.ok map' ->    forall (lk0: list var) lv s (mH mL: map') mH' mL',
      map.agree_on s mH mL ->
      map.putmany_of_list_zip lk0 lv mH = Some mH' ->
      map.putmany_of_list_zip lk0 lv mL = Some mL' ->
      map.agree_on (union s (of_list lk0)) mH' mL'.
  Proof.
    induction lk0.
    - intros. simpl in *.
      destr lv; [ | discriminate ].
      eapply agree_on_union; try solve [eassumption].
      split.
      + fwd; eassumption.
      + unfold map.agree_on.
        fwd. intros. inversion H2.
    - intros. destr lv; [ discriminate | ].
      simpl in *.
      cut (map.agree_on (union s (singleton_set a))
             (map.put mH a v) (map.put mL a v)).
      + intros.
        eapply IHlk0 in H2.
        2: { eapply agree_on_comm; eassumption. }
        2: eassumption.
        eapply agree_on_sameset.
        * eassumption.
        * eassumption.
        * eapply agree_on_comm.
          -- eassumption.
          -- eassumption.
          -- eassumption.
        * erewrite of_list_cons. unfold add. unfold sameset; split; subset_union_solve.
      + eapply agree_on_put; try solve [eassumption]; reflexivity.
  Qed.


  Lemma agree_on_diff_putmany_of_list_zip :

     forall {var: Type} {var_eqb: var -> var -> bool},
      EqDecider var_eqb ->
      forall {val: Type} {map': map.map var val},
        map.ok map' -> forall o1 o2 v (l l': map') lL lL',
      map.agree_on (diff (of_list o1) (of_list o2)) l lL
      -> map.putmany_of_list_zip o2 v l = Some l'
      -> map.putmany_of_list_zip o2 v lL = Some lL'
      -> map.agree_on (of_list o1) l' lL'.
  Proof.
    intros.
    eapply agree_on_subset.
    1-2: eassumption.
    2: {
      eapply agree_on_putmany_of_list_zip.
      all: eassumption.

    }
    eapply subset_trans.
    2: { eapply sameset_union_diff_of_list; eassumption. }
    subset_union_solve.
  Qed.

  Lemma agree_on_find:
 forall {val: Type} {map': map.map string val},
        map.ok map' ->
    forall s l (m1 m2: map'),
      map.agree_on (of_list (if (find (eqb s) l)
                    then l
                    else s :: l)) m1 m2
      -> map.agree_on (of_list [s]) m1 m2 /\
           map.agree_on (of_list l) m1 m2.
  Proof.
    intros.
    destr (find (eqb s) l).
    - split.
      + unfold map.agree_on.
        intros.
        rewrite H0.
        * reflexivity.
        * inversion H1.
          -- rewrite <- H2.
             eapply find_some in E.
             destr E.
             rewrite eqb_eq in H4.
             rewrite  H4.
             unfold elem_of, of_list.
             eapply H3.
          -- inversion H2.
      + eassumption.
    - eapply agree_on_cons in H0.
      3: assumption.
      + destr H0.
        split.
        * unfold map.agree_on.
          intros.
          unfold elem_of in H2; inversion H2.
          2: { inversion H3. }
          rewrite <- H3. eassumption.
        * eapply H0.
      + eapply String.eqb_spec.
  Qed.


  Lemma agree_on_refl :
    forall (val: Type) (map': map.map string val),
      map.ok map' ->
    forall keySet (m : map'),
      map.agree_on keySet m m.
  Proof.
    intros.
    unfold map.agree_on.
    intros.
    reflexivity.
  Qed.

Lemma existsb_of_list :
    forall k keySet,
      existsb (eqb k) keySet = true <-> k \in of_list keySet.
  Proof.
    intros.
    simpl.
    unfold iff.
    propositional idtac.
    - induction keySet.
      + simpl in Hyp. discriminate.
      + simpl in Hyp.
        apply Bool.orb_prop in Hyp.
        destr Hyp.
        * eapply of_list_cons.
          unfold add.
          eapply in_union_l.
          eapply eqb_eq in H.
          rewrite H.
          unfold singleton_set.
          constructor.
        * eapply of_list_cons.
          unfold add.
          eapply in_union_r.
          eauto.
    - induction keySet.
      +  unfold of_list in Hyp. simpl in Hyp.
         auto.
      + simpl.
        inversion Hyp.
        * rewrite H.
          rewrite eqb_refl.
          eapply Bool.orb_true_l.
        * rewrite IHkeySet.
          -- eapply Bool.orb_true_r.
          -- assumption.
  Qed.


  Lemma agree_on_not_in:
    forall (val: Type) (locals: map.map string val),
    map.ok locals -> forall keySet (m: locals) x,
      existsb (String.eqb x) keySet = false ->
      forall y,
        map.agree_on (PropSet.of_list keySet) (map.put m x y) m.
  Proof.
    intros.
    unfold map.agree_on.
    intros.
    rewrite map.get_put_dec.
    destr (x =? k)%string.
    - apply existsb_of_list in H1. exfalso. rewrite H1 in H0. discriminate.
    - reflexivity.
  Qed.

  Lemma agree_on_put_not_in :
    forall (val: Type) (locals: map.map string val),
      map.ok locals -> forall x l (m1 m2: locals),
      map.agree_on (of_list l) m1 m2
      -> existsb (eqb x) l = false
      -> forall v,
          map.agree_on (of_list l) (map.put m1 x v) m2.
  Proof.
    intros.
    unfold map.agree_on.
    intros.
    erewrite agree_on_not_in.
    - rewrite H0.
      + reflexivity.
      + assumption.
    - eapply H.
    - eapply H1.
    - eapply H2.
  Qed.

End WithArguments0.
