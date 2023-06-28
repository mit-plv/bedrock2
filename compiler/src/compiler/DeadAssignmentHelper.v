Require Import compiler.util.Common.
Require Import compiler.FlatImp.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.Syntax.
Require Import coqutil.Tactics.fwd.
Require Import String.
Require Import compiler.DeadAssignmentDef.
Require Import bedrock2.MetricLogging.
Require Import coqutil.Datatypes.PropSet.

Local Notation var := String.string (only parsing).

Section WithArguments.
  Context {width : Z}.
  Context {BW :  Bitwidth.Bitwidth width }.
  Context {word :  word width } {word_ok : word.ok word}.
  Context {locals :  map.map string word } {locals_ok: map.ok locals}.

  Lemma putmany_Some' :
    forall  (lk: list string) lv  (m: locals),
      (exists m', map.putmany_of_list_zip lk lv m = Some m')
      <-> Datatypes.length lk = Datatypes.length lv.
  Proof.
    induction lk.
    - simpl. intros. destr lv.
      + simpl.
        unfold iff; split.
        * intros. reflexivity.
        * intros. eauto.
      + simpl.
        unfold iff; split.
        * intros. destr H. discriminate.
        * intros. discriminate.
    - intros. destr lv.
      + simpl.
        unfold iff; split.
        * intros. destr H. discriminate.
        * intros. discriminate.
      + simpl.
        unfold iff; split.
        * intros. apply eq_S.
          eapply IHlk.
          eapply H.
        * intros. apply eq_add_S in H.
          eapply IHlk in H.
          eapply H.
  Qed.

  Lemma putmany_Some:
    forall  (lk: list string) lv  (m0: locals) m1,
      map.putmany_of_list_zip lk lv m0 = Some m1
      -> (forall (m: locals),
             (exists m', map.putmany_of_list_zip lk lv m = Some m')).
  Proof.
    intros.
    eapply putmany_Some'.
    eapply putmany_Some'.
    eexists.
    eapply H.
  Qed.

  Lemma agree_on_union:
    forall (s0 s1: set string) (m0 m1: locals),
      map.agree_on (union s0 s1) m0 m1
      <-> map.agree_on s0 m0 m1 /\ map.agree_on s1 m0 m1.
  Proof.
    intros.
    unfold iff; split.
    - unfold map.agree_on in *.
      split; intros; cut (s0 k \/ s1 k); auto.
    - unfold map.agree_on in *.
      intros.
      destr H.
      cut (s0 k \/ s1 k).
      + intros. destr H2; auto.
      + auto.
  Qed.

  Lemma agree_on_refl :
    forall keySet (m : locals),
      map.agree_on keySet m m.
  Proof.
    intros.
    unfold map.agree_on.
    intros.
    reflexivity.
  Qed.


  Lemma sameset_in:
    forall (s1 s2: set string),
      sameset s1 s2 ->
      forall k, k \in s1 <-> k \in s2.
  Proof.
    intros.
    unfold iff.
    propositional idtac.
    - unfold sameset in H.
      destruct H.
      unfold subset in H.
      eauto.
    - unfold sameset in H.
      destruct H.
      unfold subset in H0.
      eauto.
  Qed.

  Lemma union_iff:
    forall {E: Type} (s1 s2: set E) (x : E),
      union s1 s2 x <-> s1 x \/ s2 x.
  Proof.
    intros.
    unfold iff.
    propositional idtac.
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
      + eapply sameset_in.
        * eapply of_list_cons.
        * unfold add. eapply union_iff.
          simpl in Hyp.
          apply Bool.orb_prop in Hyp.
          destruct Hyp.
          -- left. unfold singleton_set.  eapply eqb_eq. rewrite eqb_sym. assumption.
          -- right. eapply IHkeySet. eassumption.
    - induction keySet.
      +  unfold of_list in Hyp. simpl in Hyp.
         auto.
      + simpl. assert (sameset (of_list (a :: keySet)) (add (of_list keySet) a) ) by apply of_list_cons.
        assert (k \in (add (of_list keySet) a)).
        { eapply sameset_in; eauto. }
        unfold add in H0.
        eapply union_iff in H0. destruct H0.
        * unfold singleton_set in H0. rewrite H0.
          rewrite eqb_refl.
          rewrite Bool.orb_true_l.
          reflexivity.
        * assert (existsb (eqb k) keySet = true).
          -- eapply IHkeySet. eapply H0.
          -- rewrite H1. rewrite Bool.orb_true_r. reflexivity.
  Qed.



  Lemma agree_on_not_in:
    forall keySet (m: locals) x,
      existsb (String.eqb x) keySet = false ->
      forall y,
        map.agree_on (PropSet.of_list keySet) (map.put m x y) m.
  Proof.
    intros.
    unfold map.agree_on.
    intros.
    rewrite map.get_put_dec.
    destr (x =? k)%string.
    - apply existsb_of_list in H0.
      rewrite H in H0. discriminate.
    - reflexivity.
  Qed.


  Lemma agree_on_subset:
    forall s1 s2 (m1 m2: locals),
      map.agree_on s2 m1 m2 ->
      subset s1 s2 ->
      map.agree_on s1 m1 m2.
  Proof.
    intros.
    unfold map.agree_on in *.
    intros.
    unfold subset in *.
    eauto.
  Qed.

  Lemma sameset_implies_subset:
    forall (s1 s2: set string),
      sameset s1 s2 ->
      subset s1 s2.
  Proof.
    unfold sameset, subset.
    intros. destr H; auto.
  Qed.

  Lemma agree_on_sameset:
    forall s1 s2 (m1 m2: locals),
      map.agree_on s2 m1 m2 ->
      sameset s1 s2 ->
      map.agree_on s1 m1 m2.
  Proof.
    intros.
    eauto using agree_on_subset, sameset_implies_subset.
  Qed.

  Lemma agree_on_cons:
    forall (h: string) t (m1 m2: locals),
      map.agree_on (of_list (h :: t)) m1 m2
      -> map.get m1 h = map.get m2 h /\
         map.agree_on (of_list t) m1 m2.
  Proof.
    intros.
    eapply agree_on_sameset in H.
    2: { eapply sameset_sym. eapply of_list_cons. }
    unfold add in H.
    split.
    - assert (map.agree_on (singleton_set h) m1 m2).
      {
        eapply agree_on_subset.
        - eapply H.
        - eapply subset_union_rl.
          eapply sameset_implies_subset.
          eapply sameset_ref.
      }
      unfold map.agree_on in H0.
      eapply H0.
      unfold singleton_set.
      eapply eq_refl.
    - eapply agree_on_subset.
      + eapply H.
      + eapply subset_union_rr.
        eapply sameset_implies_subset.
        eapply sameset_ref.
  Qed.

  Lemma agree_on_getmany :
    forall rets (x st1 : locals),
      map.agree_on (of_list rets) x st1 ->
      map.getmany_of_list x rets =  map.getmany_of_list st1 rets.
  Proof.
    intros.
    unfold map.getmany_of_list.
    induction rets; simpl; [ reflexivity | ].
    eapply agree_on_cons in H.
    destr H.
    rewrite H.
    destr (map.get st1 a); [ | reflexivity ].
    eapply IHrets in H0.
    rewrite H0.
    reflexivity.
  Qed.


  Lemma subset_diff :
    forall  (s1 s2 s3: set string),
      subset s1 s2 ->
      subset (diff s1 s3) (diff s2 s3).
  Proof.
    intros.
    unfold subset, diff.
    intros.
    assert (x \in s1 /\ ~ (x \in s3)).
    { assert ((fun x : string => x \in s1 /\ ~ x \in s3) x) by exact H0.
      simpl in H1.
      assumption.
    }
    assert ((x \in s2) /\ (~x \in s3) ->  x \in (fun x0 : string => x0 \in s2 /\ ~ x0 \in s3)).
    { auto. }
    eapply H2.
    destr H1. split; eauto.
  Qed.

   Lemma sameset_diff :
    forall  (s1 s2 s3: set string),
      sameset s1 s2 ->
      sameset (diff s1 s3) (diff s2 s3).
  Proof.
    intros.
    unfold sameset in *.
    destr H.
    split; eauto using subset_diff.
  Qed.

  Lemma sameset_diff_not_in:
    forall (s: list string) x,
      existsb (eqb x) s = false ->
      sameset (diff (of_list s) (singleton_set x))
        (of_list s).
  Proof.
    intros.
    unfold sameset; split.
    * unfold subset; simpl.
      intros.
      unfold diff in H.
      assert (x0 \in of_list s /\ ~ x0 \in singleton_set x) by auto.
      destr H0; assumption.
    * unfold subset; simpl.
      intros.
      unfold diff.
      cut (x0 \in of_list s /\ ~ x0 \in singleton_set x); [ auto | ].
      split; [ assumption | ].
      eapply existsb_of_list in H0.
      assert (x = x0 -> False).
      { intros; subst. rewrite H0 in H. discriminate. }
      auto.
  Qed.


  Lemma diff_subset:
    forall s1 s2: set string,
      subset (diff s1 s2) s1.
  Proof.
    intros.
    unfold subset.
    intros.
    unfold diff in H.
    assert (s1 x /\ ~ (s2 x)) by auto.
    cut (s1 x).
    { auto. }
    destr H0; auto.
  Qed.

  Lemma existsb_removeb_None:
    forall (s: string) l,
      existsb (eqb s) l = false ->
      List.removeb eqb s l = l.
  Proof.
    intros. induction l.
    - simpl; reflexivity.
    - simpl in H.
      apply Bool.orb_false_elim in H.
      destr H.
      eapply IHl in H0.
      simpl.
      rewrite H.  simpl.
      rewrite H0.
      reflexivity.
  Qed.
  Lemma in_singleton :
    forall (x: string) (s: list string),
      In x s ->
      subset (singleton_set x) (of_list s).
  Proof.
    intros.
    unfold subset, singleton_set.
    intros.
    assert (eq x x0) by auto.
    subst.
    propositional idtac.
  Qed.

  Lemma of_list_list_diff:
    forall l1 l2 : list string,
      of_list (ListSet.list_diff eqb l1 l2) =
        diff (of_list l1) (of_list l2).
  Proof.
    intros.
    induction l2.
    (* PR for this lemma being proved in coqutil exists;
       unsure how to prove it without the assumptions
       in the file that ListSet.of_list_list_union
       is proven in  *)
  Admitted.


  Lemma agree_on_put:
    forall a r s (mH mL: locals)  mH' mL',
      map.agree_on s mH mL ->
      map.put mH a r = mH' ->
      map.put mL a r = mL' ->
      map.agree_on (union s (singleton_set a)) mH' mL'.
  Proof.
    intros.
    apply agree_on_union.
    split.
    - unfold map.agree_on in *.
      intros.
      eapply H in H2.
      subst.
      destr (eqb a k).
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

  Lemma union_sameset:
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

  Lemma agree_on_putmany:
    forall (lk0: list string) lv s (mH mL: locals)  mH' mL',
      map.agree_on s mH mL ->
      map.putmany_of_list_zip lk0 lv mH = Some mH' ->
      map.putmany_of_list_zip lk0 lv mL = Some mL' ->
      map.agree_on (union s (of_list lk0)) mH' mL'.
  Proof.
    induction lk0.
    - intros. simpl in *.
      destr lv; [ | discriminate ].
      apply agree_on_union.
      split.
      + inversion H0.
        inversion H1.
        subst; eauto.
      + unfold map.agree_on.
        intros.
        cut (of_list [] k).
        * unfold of_list.
          intros.
          exfalso.
          eauto using in_nil.
        * auto.
    - intros. destr lv; [ discriminate | ].
      simpl in *.
      cut (map.agree_on (union s (singleton_set a))
             (map.put mH a r) (map.put mL a r)).
      + intros.
        eapply IHlk0 in H2.
        2-3: eassumption.
        eapply agree_on_sameset.
        * eassumption.
        * eapply sameset_trans.
          2: { eapply union_assoc. }
          apply union_sameset;
            [ eapply sameset_ref | eapply of_list_cons ].
      + eapply agree_on_put.
        2-3: reflexivity.
        eassumption.
  Qed.


  Lemma sameset_union_diff_oflist:
    forall (l1 l2: list string),
      sameset (union (of_list l1) (of_list l2)) (union (diff (of_list l1) (of_list l2) ) (of_list l2)).
  Proof.
    intros.
    unfold sameset, of_list, subset, union, diff.

    assert (forall x, In x l2 \/ ~ (In x l2)).
    { intro. eapply ListDec.In_decidable. unfold ListDec.decidable_eq.
      intros. destr (eqb x0 y).
      - unfold Decidable.decidable. left. reflexivity.
      - unfold Decidable.decidable. right. eassumption.
    }

    split.
    - intros.
      cut ((fun x : string =>
              x \in (fun e : string => In e l1) \/
                      x \in (fun e : string => In e l2)) x); [ simpl; intro | auto ].
      cut ((In x l1) \/ (In x l2)); [ simpl; intro | auto ].
      cut ((fun x0 : string =>
              x0 \in
              (fun x1 : string =>
                 x1 \in (fun e : string => In e l1) /\
                          ~ x1 \in (fun e : string => In e l2)) \/
                x0 \in (fun e : string => In e l2)) x); [ simpl; intro; auto | ].
      simpl.
      assert (In x l2 \/ ~ In x l2) by eapply H.
      destr H3.
      + right. auto.
      + propositional idtac. left.
        cut ((fun x1 : string =>
   x1 \in (fun e : string => In e l1) /\
            ~ x1 \in (fun e : string => In e l2)) x); [ simpl; intro; auto | ].
        simpl.
        split; auto.
    - intros.
      cut ((fun x : string =>
        x \in
        (fun x0 : string =>
         x0 \in (fun e : string => In e l1) /\
         ~ x0 \in (fun e : string => In e l2)) \/
          x \in (fun e : string => In e l2)) x); [ | auto ].
      simpl. intro.
      destr H1.
      + cut ((fun x0 : string =>
        x0 \in (fun e : string => In e l1) /\
                 ~ x0 \in (fun e : string => In e l2)) x); [ simpl; intro | auto ].
        cut ((fun x0 : string =>
   x0 \in (fun e : string => In e l1) \/
            x0 \in (fun e : string => In e l2)) x); [ simpl; intro; auto | ].
        simpl.
        destr H2. left. assumption.
      + cut ((fun x0 : string =>
   x0 \in (fun e : string => In e l1) \/
            x0 \in (fun e : string => In e l2)) x); [ simpl; intro; auto | ].
        simpl.
        right. assumption.
  Qed.

  Lemma sameset_diff_singleton:
    forall (l: list string) x,
      sameset (diff (of_list l) (of_list [x])) (diff (of_list l) (singleton_set x)).
  Proof.
    intros.
    unfold diff.
    unfold sameset.
    split; unfold subset; intros.
    - cut ((fun x0 : string =>
              x0 \in of_list l /\ ~ x0 \in of_list [x]) x0); [ | auto ].
      simpl.
      intros.
      cut ((fun x1 : string =>
              x1 \in of_list l /\ ~ x1 \in singleton_set x)  x0); [ auto | ].
      simpl.
      destr H0.
      split.
      + assumption.
      + unfold singleton_set, of_list in *.
        destr (eqb x x0).
        * assert (~ (In x0 [x0])) by auto.
          assert (In x0 [x0]) by eapply in_eq.
          eapply H2 in H3.
          exfalso; auto.
        * eauto.
    - cut ((fun x0 : string =>
              x0 \in of_list l /\ ~ x0 \in of_list [x]) x0); [ auto | ].
      simpl.
      cut ((fun x1 : string =>
              x1 \in of_list l /\ ~ x1 \in singleton_set x)  x0); [ | auto ].
      simpl.
      intro.
      destr H0.
      split.
      + assumption.
      + unfold singleton_set, of_list in *.
        cut ((fun e : string => In e [x]) x0 -> False); [ auto | ].
        simpl.
        intros.
        destr H2; [ | assumption ].
        subst.
        assert (eq x0 x0) by auto.
        assert (eq x0 x0 -> False) by auto.
        auto.
  Qed.

  Lemma agree_on_find:
    forall s l (m1 m2: locals),
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
        assert (k = s).
        { cut (of_list [s] k); auto.
          intros. destr H1; auto.
          inversion H1.
        }
        rewrite H1 in *; clear H1.
        apply find_some in E.
        destr E.
        apply eqb_eq in H2.
        rewrite H2 in *.
        eauto.
      + assumption.
    - eapply agree_on_sameset in H.
      2: eapply sameset_sym; eapply of_list_cons.
      unfold add in H.
      apply agree_on_union in H.
      propositional idtac.
      unfold map.agree_on in H_l.
      assert (map.get m1 s = map.get m2 s). {
        apply H_l.
        unfold singleton_set.
        cut (eq s s); auto.
      }
      unfold map.agree_on.
      intros.
      assert (k = s).
      { cut (of_list [s] k); auto.
        intros. destr H1; auto.
        inversion H1.
      }
      rewrite H1.
      assumption.
  Qed.

  Lemma agree_on_put_not_in :
    forall x l (m1 m2: locals),
      map.agree_on (of_list l) m1 m2
      -> existsb (eqb x) l = false
      -> forall v,
          map.agree_on (of_list l) (map.put m1 x v) m2.
  Proof.
    intros.
    unfold map.agree_on.
    intros.
    rewrite <- H.
    2: eassumption.
    erewrite agree_on_not_in.
    3: eassumption.
    2: eassumption.
    reflexivity.
  Qed.

End WithArguments.
