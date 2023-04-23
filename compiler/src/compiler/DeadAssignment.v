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
  Context {env :  map.map string (list var * list var * stmt var) } {env_ok : map.ok env}.
  Context {mem :  map.map word (Init.Byte.byte : Type) } {mem_ok: map.ok mem}.
  Context {locals :  map.map string word } {locals_ok: map.ok locals}.
  Context {ext_spec : Semantics.ExtSpec} {ext_spec_ok: Semantics.ext_spec.ok ext_spec}.

  Local Hint Constructors exec: core.
(* claim that
- after-optimization program assigns less than before-optimization (in locals)
- but return values always the same? as fxn of inputs? *)
  (* after-optimization contain all before-optimization variables that were live *)

  (* old lemma breaks if post checks dead variables *)
  (* Hint Resolve : map_hints. Copy style from FlatToRiscvFunctions *)
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
    apply H0 in H1.
    eapply H.
    eassumption.
  Qed.



  Lemma deadassignment_correct_aux:
    forall eH eL,
       deadassignment_functions eH = Success eL ->
       forall sH t m mcH lH postH,
         exec eH sH t m lH mcH postH ->
         forall used_after lL,
           map.agree_on (of_list (live sH used_after)) lH lL
           -> exec eL (deadAssignment used_after sH) t m lH mcH
                (fun t' m' lL' mcL' =>
                   exists lH' mcH',
                     map.agree_on (PropSet.of_list used_after) lH' lL'
                     /\ postH t' m' lH' mcH' ).
  Proof.
    induction 2.
    9: { simpl; eauto.
         intros. destr (existsb (eqb x) (used_after)).
         all: simpl.
         - eapply @exec.set; eauto.
           eexists. eexists.
           split.
           2: eassumption. apply agree_on_refl.
         - eapply @exec.skip; eauto.
           eexists. eexists.
           split.
           2: eassumption.
           eapply agree_on_not_in.
           assumption.
    }
    { simpl.
      intros.
      eapply @exec.interact; eauto.
      intros. apply H3 in H5.
      destruct H5. destruct H5.
      eexists. split.
      * eassumption.
      * intros. eapply H6 in H7.
        eexists. eexists.
        split.
        2: { eapply H7. }
        apply agree_on_refl.
    }
    { simpl. intros.
      all: admit.
      (*
      eapply @exec.call; eauto.
      * unfold deadassignment_functions in H.
        unfold deadassignment_function in H.
        simpl in H.
        eapply map.try_map_values_fw in H.
        2: { eapply H0. }
        destruct H.
        destruct H.
        inversion H.
        rewrite <- H8 in H6.
        apply H6.
      * admit.
      * admit. *)
    }
    { simpl. intros.
      eapply @exec.load; eauto.
      destr (find (eqb a) (List.removeb eqb x used_after)).
      * eexists. eexists.
        split.
        2: { eassumption. }
        apply agree_on_refl.
      * eexists. eexists. split.
        2: { eassumption. }
        apply agree_on_refl.
    }
    { simpl. intros.
      destr (find (eqb v) (used_after)).
      - destr (find (eqb a) (used_after)).
        * eapply @exec.store; eauto.
          eexists. eexists. split. 2: eassumption.
          apply agree_on_refl.
        * eapply @exec.store; eauto.
          eexists. eexists. split. 2: eassumption.
          apply agree_on_refl.
      - destr (find (eqb a) (v :: used_after)).
        * eapply @exec.store; eauto.
          eexists. eexists. split. 2: eassumption.
          apply agree_on_refl.
        * eapply @exec.store; eauto.
          eexists. eexists. split. 2: eassumption.
          apply agree_on_refl.
    }
    { simpl. intros.
      eapply @exec.inlinetable; eauto.
      eexists. eexists. split. 2: eassumption.
      apply agree_on_refl.
    }
    { simpl. intros.
      apply @exec.stackalloc; auto.
      simpl. intros.
      eapply @exec.weaken.
      -- eapply H2.
         ++ eassumption.
         ++ eassumption.
         ++ eapply agree_on_refl.
      -- simpl. intros.
         propositional idtac.
    }
    { simpl. intros.
      destr (existsb (eqb x) used_after).
      -- eapply @exec.lit; eauto.
         eexists. eexists. split.
         2: eassumption.
         apply agree_on_refl.
      -- eapply @exec.skip; eauto.
         eexists. eexists. split.
         2: eassumption.
         eapply agree_on_not_in.
         assumption.
    }
    { simpl. intros.
      destr (existsb (eqb x) used_after).
      -- eapply @exec.op; eauto.
         eexists. eexists. split.
         2: eassumption.
         apply agree_on_refl.
      -- eapply @exec.skip; eauto.
         eexists. eexists. split.
         2: eassumption.
         eapply agree_on_not_in.
         assumption.
    }
    { simpl. intros.
      eapply @exec.if_true; eauto.
      eapply IHexec.
      all: eauto.
      eapply agree_on_subset.
      -- eapply H2.
      -- unfold subset. intros.
         rewrite ListSet.of_list_list_union.
         apply in_union_l.
         rewrite ListSet.of_list_list_union.
         apply in_union_l.
         assumption.
    }
    { simpl. intros.
      eapply @exec.if_false; eauto.
      eapply IHexec.
      all: eauto.
      eapply agree_on_subset.
      -- eapply H2.
      -- unfold subset. intros.
         rewrite ListSet.of_list_list_union.
         apply in_union_l.
         rewrite ListSet.of_list_list_union.
         apply in_union_r.
         assumption.
    }
    { simpl. intros.
      (* exec.loop *)
      all: admit.
    }
    { simpl.
      intros.
      all: admit.
      (* exec.seq *)
    }
    { simpl.
      intros.
      eapply @exec.skip; eauto.
      eexists. eexists.
      split.
      2: eassumption.
      apply agree_on_refl.
    }
    all: admit.
    Admitted.
End WithArguments.
