Require Import riscv.Utility.runsToNonDet.
Require Import coqutil.sanity coqutil.Byte.
Require Import bedrock2.MetricLeakageSemantics.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Print runsTo.
Section step.
  Context (State : Type) (step : State -> (State -> Prop) -> Prop).
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.

  Definition State' : Type := State * AEP.
  Inductive step' : State' -> (State' -> Prop) -> Prop :=
  | step_usual s1 aep P : step s1 (fun s2 => P (s2, aep)) ->
                          step' (s1, aep) P
  | step_A s aep P : (forall x, P (s, aep x)) ->
                     step' (s, AEP_A aep) P
  | step_E s aep P : (exists x, P (s, aep x)) ->
                     step' (s, AEP_E aep) P.

  Fixpoint post_of aep :=
    match aep with
    | AEP_A aep' => fun post => fun s => forall n, runsTo step s (post_of (aep' n) post)
    | AEP_E aep' => fun post => fun s => exists n, runsTo step s (post_of (aep' n) post)
    | AEP_P X => fun post => fun s' => post X s'
    end.

  Lemma step_impl_step' s aep post :
    runsTo step s post ->
    runsTo step' (s, aep) (fun '(s', aep') => post s' /\ aep' = aep).
  Proof.
    intros H. induction H.
    - apply runsToDone. auto.
    - eapply runsTo_weaken.
      { apply runsToStep_cps. apply step_usual. eapply weaken_step. 2: eassumption.
        eassumption. }
      simpl. auto.
  Qed.
  
  Lemma step'_to_step s aep post : runsTo step' (s, aep)
                                (fun '(s', aep') =>
                                   match aep' with
                                   | AEP_P P => post P s'
                                   | _ => False
                                   end) <->
                                runsTo step s (post_of aep post).
  Proof.
    split.
    - intros H. remember (fun _ => _) as post'.
      eassert (forall s, post' s -> _) as X.
      { intros. subst. apply H0. }
      clear Heqpost'. revert X.
      remember (s, aep) as s_aep. replace s with (fst s_aep) by (subst; reflexivity).
      replace aep with (snd s_aep) by (subst; reflexivity). clear Heqs_aep.
      induction H; intros X.
      + destruct initial. apply X in H. destruct a; try solve [destruct H]. simpl.
        apply runsToDone. assumption.
      + destruct initial. specialize H1 with (2 := X). clear X.
        simpl. inversion H; subst.
        -- eapply runsToStep. 1: eassumption. simpl. intros. apply H1 in H2. apply H2.
        -- apply runsToDone. simpl. intros. specialize (H5 n). apply H1 in H5. apply H5.         -- apply runsToDone. destruct H5 as [x H5]. simpl. exists x. apply H1 in H5. apply H5.
    - intros H. remember (post_of _ _) as post'.
      assert (Hpost' : forall s, post' s -> post_of aep post s) by (subst; auto).
      clear Heqpost'. revert aep Hpost'. induction H; intros aep Hpost.
      + apply Hpost in H. clear Hpost P. induction aep.
        -- apply runsToStep_cps. apply step_A. intros x. simpl in H. specialize (H x).
           specialize (H0 x). apply runsTo_trans_cps. apply runsTo_weaken. apply step_impl_step'. apply step_A. intros. apply H0. simpl in *.
