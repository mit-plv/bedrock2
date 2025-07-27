Require Import riscv.Utility.runsToNonDet.
Require Import BinIntDef.
Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.ClassicalFacts.
Require Import Lia.

Section step.
  Context (T : Type).
  Context (State : Type) (step : State -> (State -> Prop) -> Prop).

  Inductive AEP :=
  | AEP_A (U : Type) : (U -> AEP) -> AEP
  | AEP_E (U : Type) : (U -> AEP) -> AEP
  | AEP_P : T -> AEP.

  Definition State' : Type := State * AEP.
  Inductive step' : State' -> (State' -> Prop) -> Prop :=
  | step_usual s aep mid P : step s mid ->
                          (forall s', mid s' -> P (s', aep)) -> 
                          step' (s, aep) P
  | step_A s U aep P : (forall x, P (s, aep x)) ->
                     step' (s, AEP_A U aep) P
  | step_E s U aep P : (exists x, P (s, aep x)) ->
                     step' (s, AEP_E U aep) P.

  Lemma step_usual_cps s aep P :
    step s (fun s' => P (s', aep)) ->
    step' (s, aep) P.
  Proof. eauto using step_usual. Qed.
  
  Lemma runsToStep'_of_step initial aep midset P :
    step initial midset ->
    (forall mid, midset mid -> runsTo step' (mid, aep) P) ->
    runsTo step' (initial, aep) P.
  Proof.
    intros. apply runsToStep_cps. eapply step_usual; eauto.
  Qed.

  Lemma step_impl_step' s aep post P :
    runsTo step s post ->
    (forall s', post s' -> P (s', aep)) ->
    runsTo step' (s, aep) P.
  Proof.
    intros H. induction H.
    - intros. apply runsToDone. auto.
    - intros. apply runsToStep_cps. eapply step_usual. 1: eassumption. eauto.
  Qed.

  Lemma step_impl_step'_cps s aep P :
    runsTo step s (fun s' => P (s', aep)) ->
    runsTo step' (s, aep) P.
  Proof. eauto using step_impl_step'. Qed.

  Lemma runsTo_trans'_of_step initial aep midset P :
    runsTo step initial midset ->
    (forall middle, midset middle -> runsTo step' (middle, aep) P) ->
    runsTo step' (initial, aep) P.
  Proof.
    intros. apply runsTo_trans_cps. eapply step_impl_step'; eauto.
  Qed.

  Fixpoint post_of aep :=
    match aep with
    | AEP_A U aep' => fun post => fun s => forall n, runsTo step s (post_of (aep' n) post)
    | AEP_E U aep' => fun post => fun s => exists n, runsTo step s (post_of (aep' n) post)
    | AEP_P P => fun post => fun s' => post P s'
    end.

  Lemma step'_iff_step s aep post : runsTo step' (s, aep)
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
        -- eapply runsToStep. 1: eassumption. intros. apply H6 in H2. apply H1 in H2. apply H2.
        -- apply runsToDone. simpl. intros. specialize (H5 n). apply H1 in H5. apply H5.         -- apply runsToDone. destruct H5 as [x H5]. simpl. exists x. apply H1 in H5. apply H5.
    - intros H. remember (post_of _ _) as post'.
      assert (Hpost' : forall s, post' s -> post_of aep post s) by (subst; auto).
      clear Heqpost'. revert aep Hpost'. induction H; intros aep Hpost.
      + apply Hpost in H. clear Hpost P. revert initial H.
        induction aep; intros initial Haep.
        -- apply runsToStep_cps. apply step_A. intros x.
           simpl in Haep. specialize (Haep x).
           apply runsTo_trans_cps. eapply step_impl_step'. 1: eassumption.
           intros ? H1. specialize H with (1 := H1). apply H.
        -- apply runsToStep_cps. apply step_E.
           simpl in Haep. destruct Haep as [x Haep]. exists x.
           apply runsTo_trans_cps. eapply step_impl_step'. 1: eassumption.
           intros ? H1. specialize H with (1 := H1). apply H.
        -- apply runsToDone. simpl in Haep. apply Haep.
      + apply runsToStep_cps. eapply step_usual. 1: eassumption. intros s' Hs'.
        specialize H1 with (1 := Hs') (2 := Hpost). apply H1.
  Qed.

  Inductive inputs :=
  | inp_nil
  | inp_E U : U -> inputs -> inputs
  | inp_A U : (U -> inputs) -> inputs.

  Inductive compat : AEP -> inputs -> Prop :=
  | comp_nil aep : compat aep inp_nil
  | comp_A U aep inp : (forall x, compat (aep x) (inp x)) ->
                     compat (AEP_A U aep) (inp_A U inp)
  | comp_E U aep inp x : compat (aep x) inp ->
                       compat (AEP_E U aep) (inp_E U x inp).

  Inductive goes_to : AEP -> inputs -> AEP -> Prop :=
  | gt_nil : forall aep, goes_to aep inp_nil aep
  | gt_A : forall U aep inp aep' x,
      goes_to (aep x) (inp x) aep' ->
      goes_to (AEP_A U aep) (inp_A U inp) aep'
  | gt_E : forall U aep inp aep' x,
      goes_to (aep x) inp aep' ->
      goes_to (AEP_E U aep) (inp_E U x inp) aep'.

  (*requires some quantifiers to be nonvacuous*)
  (* Lemma goes_to_something aep inp : *)
  (*   compat aep inp -> *)
  (*   exists aep', goes_to aep inp aep'. *)
  (* Proof. *)
  (*   intros H. induction H. *)
  (*   - eexists; econstructor; eauto. *)
  (*   - specialize (H0 _ O). fwd. eexists. econstructor. eassumption. *)
  (*   - fwd. eexists. econstructor. eassumption. *)
  (* Qed. *)

  Require Import Coq.Program.Equality.
  Lemma inp_works inp aep s post :
    compat aep inp ->
    (forall aep',
        goes_to aep inp aep' ->
        runsTo step' (s, aep') post) ->
    runsTo step' (s, aep) post.
  Proof.
    intros Hcom Haep. revert aep Hcom Haep. induction inp; intros aep Hcom Haep.
    - apply Haep. constructor.
    - apply runsToStep_cps. dependent destruction Hcom.
      apply step_E. exists u. eapply IHinp; try eassumption. intros. apply Haep. constructor.
      assumption.
    - apply runsToStep_cps. dependent destruction Hcom. apply step_A. intros x. eapply H; eauto. intros. apply Haep. econstructor.
      eassumption.
  Qed.
  Print Assumptions inp_works.
End step.

Section streams.
  Context (State : Type) (might_step : State -> State -> Prop).
  
  CoInductive stream (T : Type) :=
  | scons (a : T) (rest : stream T).
  
  Fixpoint nth {T : Type} (n : nat) (s : stream T) : T :=
    match s, n with
    | scons _ a rest, S n' => nth n' rest
    | scons _ a rest, O => a
    end.

  Fixpoint firstn {T : Type} (n : nat) (s : stream T) : list T :=
    match s, n with
    | scons _ a rest, S n' => a :: firstn n' rest
    | scons _ a rest, O => nil
    end.

  Fixpoint lfirstn {T : Type} (n : nat) (l : list T) : list T :=
    match l, n with
    | cons a rest, S n' => a :: lfirstn n' rest
    | _, _ => nil
    end.
  
  Lemma length_lfirstn {T : Type} (n : nat) (l : list T) :
    length (lfirstn n l) = Nat.min n (length l).
  Proof.
    revert l. induction n; intros l.
    - destruct l; reflexivity.
    - destruct l; try reflexivity. simpl in *. f_equal. apply IHn.
  Qed.
  
  Fixpoint skipn {T : Type} (n : nat) (s : stream T) : stream T :=
    match n with
    | O => s
    | S n' =>
        match s with
        | scons _ a rest => skipn n' rest
        end
    end.

  Lemma nth_skipn {T : Type} (n m : nat) (s : stream T) :
    nth n (skipn m s) = nth (m + n) s.
  Proof.
    revert s. induction m; [reflexivity|]. simpl. destruct s. apply IHm.
  Qed.

  CoInductive possible : stream State -> Prop :=
  | poss a b rest : might_step a b ->
                    possible (scons _ b rest) ->
                    possible (scons _ a (scons _ b rest)).

  Inductive lpossible : list State -> Prop :=
  | lposs_nil : lpossible nil
  | lposs_one a : lpossible (cons a nil)
  | lposs_cons a b rest : might_step a b ->
                          lpossible (cons b rest) ->
                          lpossible (cons a (cons b rest)).
  
  Lemma naen (A : Type) (P : A -> _) :
    excluded_middle ->
    ~(forall y, P y) ->
    exists y, ~P y.
  Proof.
    intros em. clear -em. intros H. assert (H1 := em (exists y, ~P y)).
    destruct H1 as [H1|H1].
    - assumption.
    - exfalso. apply H. clear H. intros y. assert (H2 := em (P y)).
      destruct H2 as [H2|H2].
      + assumption.
      + exfalso. apply H1. exists y. assumption.
  Qed.

  Lemma enna (A : Type) (P : A -> _) :
    (exists y, ~P y) ->
    ~(forall y, P y).
  Proof. intros [y H]. auto. Qed.

  CoFixpoint stream_of {T : Type} (start : T) (step : T -> T) :=
    scons _ start (stream_of (step start) step).

  Lemma stream_of_eq T (start : T) step_ :
    stream_of start step_ = scons _ start (stream_of (step_ start) step_).
  Proof. replace (stream_of start step_) with (match stream_of start step_ with
                                               | scons _ hd tl => scons _ hd tl
                                               end).
         { reflexivity. }
         destruct (stream_of _ _). reflexivity.
  Qed.

  (*taken from https://github.com/OwenConoly/semantics_relations/blob/master/equiv/EquivProof.v*)
  Lemma chains_finite_implies_Acc x :
    excluded_middle ->
    FunctionalChoice_on State State ->
    (forall str, nth O str = x -> possible str -> False) ->
    Acc (fun x y => might_step y x) x.
  Proof.
    intros em choice H. cbv [FunctionalChoice_on] in choice.
    set (R := fun x y => might_step y x).
    specialize (choice (fun x y => ~Acc R x -> ~Acc R y /\ R y x)). destruct choice as [f H'].
    { clear -em. intros x. cbv [excluded_middle] in em.
      assert (H1 := em (forall y, R y x -> Acc R y)). destruct H1 as [H1|H1].
      - exists x. intros H. exfalso. apply H. constructor. assumption.
      - assert (H2 := naen). specialize H2 with (1 := em) (2 := H1).
        simpl in H2. destruct H2 as [y H2]. exists y. intros _. split.
        + intros H. apply H2. intros. assumption.
        + assert (H3 := em (R y x)). destruct H3 as [H3|H3].
          -- assumption.
          -- exfalso. apply H2. intros. exfalso. apply H3. apply H. }
    assert (H1 := em (Acc R x)). destruct H1 as [H1|H1].
    - assumption.
    - specialize (H (stream_of x f) eq_refl). exfalso.
      exfalso. apply H. clear H. revert x H1. cofix Hcofix. intros x H.
      specialize (H' x H). do 2 rewrite stream_of_eq. destruct H'.
      constructor; [assumption|]. rewrite <- stream_of_eq. apply Hcofix. assumption.
  Qed.
End streams.

Section omni_trad.
  Context (State : Type) (might_step : State -> State -> Prop).
  
  Definition step x (P : _ -> Prop) :=
    forall y, might_step x y -> P y.

  Fixpoint lnth {T : Type} (n : nat) (l : list T) : option T :=
    match n, l with
    | S n', cons a l' => lnth n' l'
    | O, cons a l' => Some a
    | _, _ => None
    end.

  Lemma lnth_firstn {T : Type} n n1 (t : stream T) :
    n < n1 /\ lnth n (firstn n1 t) = Some (nth n t) \/ n >= n1 /\ lnth n (firstn n1 t) = None.
  Proof.
    clear. revert n t. induction n1; intros.
    - right. split; [lia|]. simpl. destruct t. destruct n; reflexivity.
    - simpl. destruct t. destruct n; simpl.
      + left. split; [lia|]. reflexivity.
      + specialize (IHn1 n t). destruct IHn1 as [(H1&H2)|(H1&H2)]; [left|right]; split; try lia;  assumption.
  Qed.
  
  Definition last_elt {T : Type} (l : list T) := lnth (length l - 1) l.
  
  Lemma possible_weaken {U : Type} str (R1 : U -> U -> Prop) :
    possible U R1 str ->
    forall R2,
    (forall x y, R1 x y -> R2 x y) ->
    possible U R2 str.
  Proof.
    intros H' R2 H. revert str H'. cofix Hstr. intros str H'. inversion H'. subst.
    clear H'. constructor. 1: auto. apply Hstr. assumption.
  Qed.

  Lemma possible_nth {U : Type} str (R : U -> U -> Prop) n :
    possible U R str ->
    R (nth n str) (nth (S n) str).
  Proof.
    revert str. induction n.
    - intros str H. inversion H. subst. simpl. assumption.
    - intros str H. inversion H. subst. simpl. apply IHn. assumption.
  Qed.

  Lemma possible_skipn {U : Type} str (R : U -> U -> Prop) n :
    possible U R str ->
    possible U R (skipn n str).
  Proof.
    revert str. induction n.
    - intros str H. inversion H. subst. simpl. assumption.
    - intros str H. inversion H. subst. simpl. apply IHn. assumption.
  Qed.

  Lemma lpossible_firstn {U : Type} str (R : U -> U -> Prop) n :
    possible U R str ->
    lpossible U R (firstn n str).
  Proof.
    revert str. induction n.
    - intros. destruct str. simpl. constructor.
    - intros. destruct str. simpl. inversion H. subst. destruct n.
      1: constructor. constructor; auto. apply IHn in H3. simpl in H3.
      apply H3.
  Qed.

  Fixpoint and_then {U : Type} (l : list U) (s : stream U) : stream U :=
    match l with
    | nil => s
    | cons a l' => scons _ a (and_then l' s)
    end.

  Lemma length_firstn {A : Type} n (s : stream A) : length (firstn n s) = n.
  Proof.
    revert s. induction n; destruct s; [reflexivity|]. simpl. rewrite IHn. reflexivity.
  Qed.

  Lemma nth_andthen {U : Type} (l : list U) (s : stream U) n :
    n < length l /\ Some (nth n (and_then l s)) = lnth n l \/
      length l <= n /\ nth n (and_then l s) = nth (n - length l) s.
  Proof.
    revert n. induction l.
    - simpl. right. split; [lia|]. f_equal. lia.
    - simpl. intros n. destruct n.
      + left. split; [lia|]. simpl. reflexivity.
      + specialize (IHl n). destruct IHl as [(H1&H2)|(H1&H2)].
        -- left. split; [lia|]. simpl. assumption.
        -- right. split; [lia|]. simpl. assumption.
  Qed.

  Lemma last_elt_cons_cons {U : Type} (a b : U) l :
    last_elt (cons a (cons b l)) = last_elt (cons b l).
  Proof. cbv [last_elt]. simpl. f_equal. lia. Qed.

  Lemma possible_andthen {U : Type} l str (R : U -> U -> Prop) :
    lpossible _ R l ->
    match last_elt l with
    | None => True
    | Some x => R x (nth O str)
    end ->
    possible _ R str ->
    possible _ R (and_then l str).
  Proof.
    intros H1 H2 H3. revert H1 H2. induction l; intros H1 H2.
    - simpl. assumption.
    - simpl. destruct l.
      + simpl. destruct str. simpl in H2. constructor; [assumption|].
        apply IHl. 1: constructor. simpl. constructor.
      + simpl. inversion H1. subst. constructor; [assumption|].
        apply IHl. 1: assumption. rewrite last_elt_cons_cons in H2. apply H2.
  Qed.

  Lemma skipn_andthen {U : Type} (l : list U) s :
    skipn (length l) (and_then l s) = s.
  Proof. revert s. induction l; auto. Qed.         
  
  Lemma runsTo_iff_trace_pred s P :
    excluded_middle ->
    FunctionalChoice_on State State ->
    runsTo step s P <-> (forall str, possible _ might_step str ->
                               nth O str = s ->
                               exists n, P (nth n str)).
  Proof.
    intros em choice. split; intros H.
    - induction H.
      + intros. destruct str; inversion H1. subst. exists O. simpl. assumption.
      + intros. inversion H2. subst. clear H2. simpl in H. cbv [step] in H.
        edestruct H1 as [n Hn].
        -- apply H. eassumption.
        -- eassumption.
        -- reflexivity.
        -- exists (S n). simpl. assumption.
    - set (R := fun x y => might_step y x /\ ~P y).
      assert (Hyp: forall str, nth O str = s -> possible _ (fun x y => R y x) str -> False).
      { intros str HO Hsteps. subst. eassert _ as Hn.
        { apply H. 2: reflexivity. eapply possible_weaken. 1: eassumption.
          subst R. simpl. intros ? ? [? ?]. assumption. }
        destruct Hn as [n Hn]. apply (possible_nth _ _ n) in Hsteps. subst R.
        simpl in Hsteps. destruct Hsteps as [_ ?]. auto. }
      apply chains_finite_implies_Acc in Hyp; [|assumption|assumption].
      induction Hyp. assert (H' := em (P x)). destruct H' as [H'|H'].
      { apply runsToDone. assumption. }
      subst R. simpl in *. apply runsToStep_cps. intros y Hy. eapply H1; eauto.
      intros str. specialize (H (scons _ x str)). intros Hstr ?. destruct str. subst.
      specialize (H ltac:(econstructor; eauto) eq_refl). destruct H as [n Hn].
      destruct n as [|n].
      { simpl in Hn. exfalso. auto. }
      exists n. simpl in Hn. apply Hn.
  Qed.
End omni_trad.

Section more_omni_trad.
  Context (State : Type) (might_step : State -> State -> Prop).
  Notation step := (step _ might_step).
  Notation step' := (step' _ State step).
  
  Fixpoint interp_aep {U : Type} (aep : AEP (U -> Prop))
    (sp : stream U -> Prop) : Prop :=
    match aep with
    | AEP_A _ _ aep' =>
        forall s,
          sp s ->
          exists n,
          forall x, interp_aep (aep' x)
                 (fun sfx => nth O sfx = nth n s /\
                            sp (and_then (firstn n s) sfx))
    | AEP_E _ _ aep' =>
        forall s,
          sp s ->
          exists n,
          exists x, interp_aep (aep' x)
                 (fun sfx => nth O sfx = nth n s /\
                            sp (and_then (firstn n s) sfx))

    | AEP_P _ P =>
        forall s,
          sp s ->
          exists n,
            P (nth n s)
    end.

  Lemma interp_aep_weaken {U : Type} (aep : AEP (U -> Prop)) (sp1 sp2 : stream U -> Prop) :
    (forall str, sp2 str -> sp1 str) ->
    interp_aep aep sp1 ->
    interp_aep aep sp2.
  Proof.
    revert sp1 sp2. induction aep; cbn -[nth] in *; intros.
    - apply H0 in H2. apply H1 in H2. destruct H2 as [n Hn]. exists n. intros x.
      specialize (Hn x). eapply H; try apply Hn. intros ? (?&?). auto.
    - apply H0 in H2. apply H1 in H2. destruct H2 as [n Hn]. exists n.
      destruct Hn as [x Hn]. exists x. eapply H; try apply Hn. intros ? (?&?). auto.
    - auto.
  Qed.
  
  Lemma runsTo_iff_trace_pred' s aep :
    excluded_middle ->
    FunctionalChoice_on State State ->
    runsTo step s (post_of _ State step aep (fun P s => P s)) <->
      interp_aep aep (fun str => possible _ might_step str /\ nth O str = s).
  Proof.
    intros em choice. revert s. induction aep; intros s.
    - rewrite runsTo_iff_trace_pred by assumption. split.
      + intros H'. cbn [interp_aep]. intros s0 (H1&H2). specialize (H' s0 H1 H2).
        destruct H' as [n Hn]. exists n. intros x. simpl in Hn. specialize (Hn x).
        apply H in Hn. eapply interp_aep_weaken. 2: eassumption. cbv beta.
        intros ? (H3&H4&H5). split; [|assumption]. Check possible_skipn.
        eapply possible_skipn in H4. rewrite skipn_andthen in H4 by reflexivity.
        assumption.
      + cbn -[nth]. intros. specialize (H0 str (conj H1 H2)).
        destruct H0 as [n Hn]. exists n. intros x. specialize (Hn x). apply H.
        eapply interp_aep_weaken. 2: eassumption. cbv beta. intros ? (?&?).
        split; [assumption|]. split.
        -- apply possible_andthen.
           ++ apply lpossible_firstn. assumption.
           ++ destruct n.
              --- destruct str. simpl. constructor.
              --- cbv [last_elt]. rewrite length_firstn.
                  epose proof lnth_firstn as lfn.
                  edestruct lfn as [(?&Hlfn)|(?&?)]; [rewrite Hlfn|lia].
                  rewrite H3. cbn -[nth]. rewrite PeanoNat.Nat.sub_0_r.
                  apply possible_nth. assumption.
           ++ assumption.
        -- destruct n.
           ++ destruct str. cbn -[nth]. rewrite H3. assumption.
           ++ destruct str. simpl. apply H2.
    - rewrite runsTo_iff_trace_pred by assumption. split.
      + intros H'. cbn [interp_aep]. intros s0 (H1&H2). specialize (H' s0 H1 H2).
        destruct H' as [n Hn]. exists n. destruct Hn as [x Hn]. exists x.
        apply H in Hn. eapply interp_aep_weaken. 2: eassumption. cbv beta.
        intros ? (H3&H4&H5). split; [|assumption]. Check possible_skipn.
        eapply possible_skipn in H4. rewrite skipn_andthen in H4 by reflexivity.
        assumption.
      + cbn -[nth]. intros. specialize (H0 str (conj H1 H2)).
        destruct H0 as [n Hn]. exists n. destruct Hn as [x Hn]. exists x. apply H.
        eapply interp_aep_weaken. 2: eassumption. cbv beta. intros ? (?&?).
        split; [assumption|]. split.
        -- apply possible_andthen.
           ++ apply lpossible_firstn. assumption.
           ++ destruct n.
              --- destruct str. simpl. constructor.
              --- cbv [last_elt]. rewrite length_firstn.
                  epose proof lnth_firstn as lfn.
                  edestruct lfn as [(?&Hlfn)|(?&?)]; [rewrite Hlfn|lia].
                  rewrite H3. cbn -[nth]. rewrite PeanoNat.Nat.sub_0_r.
                  apply possible_nth. assumption.
           ++ assumption.
        -- destruct n.
           ++ destruct str. cbn -[nth]. rewrite H3. assumption.
           ++ destruct str. simpl. apply H2.
    - cbn -[nth]. rewrite runsTo_iff_trace_pred by assumption. split; intros; auto.
      destruct H0. auto.
  Qed.

  Lemma aep_to_trad s aep :
    excluded_middle ->
    FunctionalChoice_on State State ->
    runsTo step' (s, aep) (fun '(s', aep') =>
                             match aep' with
                             | AEP_P _ P => P s'
                             | _ => False
                             end) <->
      interp_aep aep (fun str => possible _ might_step str /\ nth O str = s).
  Proof. rewrite step'_iff_step. apply runsTo_iff_trace_pred'. Qed.
End more_omni_trad.

Section post_of_surj.
  Context (Event : Type) (State : Type) (st : State).
  Context (might_step : State -> State -> Prop).
  Notation step := (step _ might_step).

  (*a formula stating a predicate about event streams*)
  Inductive sformula :=
  | sforall (U : Type) (u : U) : (U -> sformula) -> sformula
  | sexists (U : Type) (u : U) : (U -> sformula) -> sformula
  (*assertion about the nth element of the stream*)
  | sasstn (n : nat) : (State -> sformula) -> sformula
  (*base case: a prop*)
  | spropn : Prop -> sformula.

  Fixpoint sinterp (f : sformula) (t : stream State) : Prop :=
    match f with
    | sforall U u f' => forall n, sinterp (f' n) t
    | sexists U u f' => exists n, sinterp (f' n) t
    | sasstn n f' => sinterp (f' (nth n t)) t
    | spropn P => P
    end.
  Axiom definable : (stream State -> Prop) -> Prop.
  Axiom definable_characterization :
    forall P, definable P ->
         exists f, forall t, P t <-> sinterp f t.

  (*about lists*)
  Inductive lformula :=
  | lforall (U : Type) (u : U) : (U -> lformula) -> lformula
  | lexists (U : Type) (u : U) : (U -> lformula) -> lformula
  | lpropn : (list State -> Prop) -> lformula.

  Fixpoint linterp (f : lformula) (t : stream State) : Prop :=
    match f with
    | lforall U _ f' => forall n, linterp (f' n) t
    | lexists U _ f' => exists n, linterp (f' n) t
    | lpropn P => exists n, forall l, P (firstn n t ++ l)%list
    end.

  (*about single states, or 'atoms'.  (i used 's' already, so i guess i'll use 'a')*)
  Inductive aformula :=
  | aforall (U : Type) (u : U) : (U -> aformula) -> aformula
  | aexists (U : Type) (u : U) : (U -> aformula) -> aformula
  | apropn : (State -> Prop) -> aformula.

  Fixpoint ainterp (f : aformula) (t : stream State) : Prop :=
    match f with
    | aforall U _ f' => forall n, ainterp (f' n) t
    | aexists U _ f' => exists n, ainterp (f' n) t
    | apropn P => exists n, forall n0, n <= n0 -> P (nth n0 t)
    end.

  Lemma firstn_split {T : Type} n m (t : stream T) :
    n <= m ->
    firstn m t = (firstn n t ++ (firstn (m - n) (skipn n t)))%list.
  Proof.
    revert n t. induction m; intros n t Hn.
    - destruct n; [|lia]. destruct t. reflexivity.
    - destruct n.
      + destruct t. simpl. reflexivity.
      + destruct t. simpl. f_equal. apply IHm. lia.
  Qed.

  Lemma lnth_app_r {T : Type} n l l0 (x : T) :
    lnth n l = Some x ->
    lnth n (l ++ l0) = Some x.
  Proof.
    revert l. induction n; intros l H; (destruct l; simpl in *; [congruence|]); auto.
  Qed.
  
  Lemma assert_nth s n lf :
    excluded_middle ->
    (forall U, FunctionalChoice_on U lformula) ->
    exists lf', forall t, linterp lf' t <-> (linterp lf t /\ nth n t = s).
  Proof.
    clear. intros em choice. induction lf.
    - eassert (H': exists l', _).
      { apply choice. intros x. specialize (H x). destruct H as [lf' H]. exists lf'. exact H. }
      clear H. destruct H' as [l' H']. exists (lforall _ u l'). intros. simpl. split.
      + intros. (*hmm here we use that quantfiers are not vacuous.  relevant?*)
        assert (HO := H u). rewrite H' in HO. destruct HO as [_ HO].
        split; [|assumption]. intros n0. specialize (H n0). rewrite H' in H.
        destruct H. assumption.
      + intros H0 n0. rewrite H'. destruct H0. auto.
    - eassert (H': exists l', _).
      { apply choice. intros x. specialize (H x). destruct H as [lf' H]. exists lf'. exact H. }
      clear H. destruct H' as [l' H']. exists (lexists _ u l'). intros. simpl. split.
      + intros [n0 Hn0]. rewrite H' in Hn0. intuition eauto.
      + intros ([n0 H0] & H1). eexists. rewrite H'. eauto.
    - exists (lpropn (fun l => P l /\ lnth n l = Some s)). intros t. simpl. split.
      + intros [n0 H]. assert (HO := H nil). destruct HO as [_ HO].
        epose proof lnth_firstn as H'. rewrite List.app_nil_r in HO.
        edestruct H' as [(_&H'')|(_&H'')]; [rewrite H'' in HO|]; clear H'.
        -- inversion HO. subst. split; [|reflexivity]. exists n0. intros l.
           specialize (H l). destruct H. assumption.
        -- congruence.
      + intros [(n0&Hn0) ?]. subst. exists (Nat.max (S n) n0). intros l.
        rewrite firstn_split with (n := n0) by lia. rewrite <- List.app_assoc.
        split; [apply Hn0|]. rewrite List.app_assoc. rewrite <- firstn_split by lia.
        epose proof (lnth_firstn n (Nat.max (S n) n0)) as H'.
        edestruct H' as [(_&H'')|H'']; [|destruct H''; lia].
        clear H'. apply lnth_app_r. eassumption.
  Qed.
  
  Lemma finite_prefixes_enough f :
    excluded_middle ->
    (forall U, FunctionalChoice_on U lformula) ->
    exists lf, forall t, sinterp f t <-> linterp lf t.
  Proof.
    clear -st. intros em choice. induction f.
    - eassert (H': exists P, _).
      { apply choice. intros x. specialize (H x). destruct H as [P H]. exists P. exact H. }
      clear H. destruct H' as [P H']. exists (lforall _ u P). intros t.
      split.
      + simpl. intros. apply H'. auto.
      + simpl. intros. apply H'. auto.
    - eassert (H': exists P, _).
      { apply choice. intros x. specialize (H x). destruct H as [P H]. exists P. exact H. }
      clear H. destruct H' as [P H']. exists (lexists _ u P). intros t.
      split.
      + simpl. intros [n H]. exists n. apply H'. auto.
      + simpl. intros [n H]. exists n. apply H'. auto.
    - simpl. eassert (exists f, _).
      { apply choice. intros x. specialize (H x). destruct H as [lf H].
        pose proof assert_nth as H'. specialize H' with (1 := em) (2 := choice).
        specialize (H' x n lf). destruct H' as [lf' H']. exists lf'.
        eassert (H'': forall t, _).
        { intros t. specialize (H t). specialize (H' t). rewrite <- H in H'. exact H'. }
        exact H''. }
      clear H. destruct H0 as [f H]. exists (lexists _ st f). intros. simpl. split.
      + intros H'. eexists. rewrite H. split; [eassumption|]. reflexivity.
      + intros [n0 H']. rewrite H in H'. destruct H' as [H' ?]. subst. assumption.
    - simpl. Print lformula. eexists (lpropn (fun _ => P)). simpl. split.
      + intros. exists O. auto.
      + intros (?&H). apply H. exact nil.
  Qed.
End post_of_surj.

Section OK_execution.
  Context (State : Type).
  Context (Event : Type) (ev : Event) (trace : State -> list Event).

  Definition trace_gets_longer (sp : _ -> Prop) :=
    forall s, sp s ->
         forall n, exists tr', trace (nth (S n) s) = List.app (trace (nth n s)) tr'.

  Lemma trace_longer_trans sp s :
    trace_gets_longer sp ->
    sp s ->
    forall n1 n2,
      n1 <= n2 ->
      exists tr', trace (nth n2 s) = List.app (trace (nth n1 s)) tr'.
  Proof.
    intros tgl H. specialize (tgl _ H). clear H. intros n1 n2 H.
    replace n2 with ((n2 - n1) + n1) by lia. clear H. remember (n2 - n1) as n.
    clear Heqn n2. induction n.
    - exists nil. rewrite List.app_nil_r. reflexivity.
    - destruct IHn as [tr' IHn]. specialize (tgl (n + n1)).
      destruct tgl as [tr'' tgl]. cbn -[nth]. rewrite tgl, IHn.
      rewrite <- List.app_assoc. eexists. reflexivity.
  Qed.

  Definition has_inf_trace (ex : stream State) (tr : stream Event) :=
    forall n, exists m, lfirstn n (trace (nth m ex)) = firstn n tr.

  Definition OK (ex : stream State) := exists tr, has_inf_trace ex tr.

  Fixpoint linterp_lol (f : lformula Event) (t : stream State) : Prop :=
    match f with
    | lforall _ U _ f' => forall n, linterp_lol (f' n) t
    | lexists _ U _ f' => exists n, linterp_lol (f' n) t
    | lpropn _ P => exists n, forall l, P (List.app (trace (nth n t)) l)
    end.

  Fixpoint aep_of (tgt : stream Event) (lf : lformula Event) : AEP (State -> Prop) :=
    match lf with
    | lforall _ U u af' => AEP_A _ _ (fun x => aep_of tgt (af' x))
    | lexists _ U u af' => AEP_E _ _ (fun x => aep_of tgt (af' x))
    | lpropn _ P => AEP_P _ (fun s => (forall l, P (trace s ++ l)%list) \/ (trace s) <> firstn (length (trace s)) tgt)
    end.

  Lemma linterp_lol_skipn lf n sp s :
    trace_gets_longer sp ->
    sp s ->
    linterp_lol lf (skipn n s) <-> linterp_lol lf s.
  Proof.
    intros tgl Hsp. induction lf; simpl; split; intros H'.
    - intros. apply H. apply H'.
    - intros. apply H. apply H'.
    - destruct H' as [n0 Hn0]. exists n0. apply H. apply Hn0.
    - destruct H' as [n0 Hn0]. exists n0. apply H. apply Hn0.
    - destruct H' as [n0 H']. exists (n + n0). intros.
      pose proof trace_longer_trans as H. specialize H with (1 := tgl).
      specialize (H s Hsp). rewrite nth_skipn in H'. apply H'.
    - destruct H' as [n0 H']. exists n0. intros.
      pose proof trace_longer_trans as H. specialize H with (1 := tgl).
      specialize (H s Hsp). specialize (H n0 (n + n0) ltac:(lia)).
      destruct H as [tr' Htr']. rewrite nth_skipn. rewrite Htr'.
      rewrite <- List.app_assoc. apply H'.
  Qed.

  Lemma firstns_something {T : Type} n m (l : list T) s : 
    m <= n ->
    lfirstn n l = firstn n s ->
    lfirstn m l = firstn m s.
  Proof.
    revert n m s. induction l; intros n m s Hmn H.
    - destruct s. destruct n; [|discriminate H]. replace m with 0 by lia. reflexivity.
    - destruct s. destruct m; [reflexivity|]. destruct n; [lia|]. simpl in H.
      inversion H. subst. clear H. simpl. f_equal. eapply IHl. 2: eassumption. lia.
  Qed.

  Lemma tail_has_inf_trace a s tr :
    has_inf_trace (scons State a s) tr <->
    has_inf_trace s tr.
  Proof.
    split; cbv [has_inf_trace]; intros H' n.
    - specialize (H' (n + S (length (trace a)))). destruct H' as [m H'].
      destruct m.
      + simpl in H'. eassert (forall x y, length x <> length y -> x <> y).
        2: { exfalso. eapply H. 2: exact H'. rewrite length_firstn.
             rewrite length_lfirstn. lia. }
        intros. intros H''. apply H. subst. reflexivity.
      + exists m. simpl in H'. eapply firstns_something. 2: eassumption. lia.
    - specialize (H' n). destruct H' as [m H']. exists (S m). simpl. assumption.
  Qed.
      
  Lemma has_inf_trace_skipn n s tr :
    has_inf_trace s tr <-> has_inf_trace (skipn n s) tr.
  Proof.
    revert s. induction n; simpl; split; intros H'; try assumption.
    - destruct s. rewrite <- IHn. eapply tail_has_inf_trace. eassumption.
    - destruct s. rewrite <- IHn in H'. apply tail_has_inf_trace. apply H'.
  Qed.

  Lemma has_inf_trace_andthen l s tr :
    has_inf_trace s tr <-> has_inf_trace (and_then l s) tr.
  Proof.
    replace (has_inf_trace s tr) with 
      (has_inf_trace (skipn (length l) (and_then l s)) tr).
    { split; apply has_inf_trace_skipn. }
    f_equal. rewrite skipn_andthen. reflexivity.
  Qed.

  Lemma andthen_firstn_skipn {T : Type} (s : stream T) n :
    and_then (firstn n s) (skipn n s) = s.
  Proof.
    revert s. induction n.
    - destruct s. reflexivity.
    -  intros. simpl. destruct s. simpl. f_equal. apply IHn.
  Qed.
  
  Lemma trace_gets_longer_preserved sp1 sp2 l :
    trace_gets_longer sp1 ->
    (forall s, sp2 s -> sp1 (and_then l s)) ->
    trace_gets_longer sp2.
  Proof.
    cbv [trace_gets_longer]. cbn -[nth]. intros H Hsp s Hs n.
    apply Hsp in Hs. specialize H with (1 := Hs). specialize (H (length l + n)).
    destruct H as [tr' H]. epose proof nth_andthen as H'.
    edestruct H' as [(?&H1)|(?&H1)]; [|rewrite H1 in H]. 1: lia.
    edestruct H' as [(?&H2)|(?&H2)]; [|rewrite H2 in H]. 1: lia.
    replace _ with (S n) in H by lia. replace (_ - _) with n in H by lia.
    eexists. exact H.
  Qed.

  Lemma lfirstn_app_r {T : Type} (l1 l2 : list T) :
    lfirstn (length l1) (l1 ++ l2) = l1.
  Proof.
    induction l1.
    - destruct l2; reflexivity.
    - simpl. f_equal. assumption.
  Qed.
      
  Lemma lfirstn_all {T : Type} (l1 : list T) :
    lfirstn (length l1) l1 = l1.
  Proof.
    rewrite <- lfirstn_app_r with (l2 := nil). rewrite List.app_nil_r. reflexivity.
  Qed.

  Lemma firstn_inf_trace sp n ex tr :
    trace_gets_longer sp ->
    sp ex ->
    has_inf_trace ex tr ->
    firstn (length (trace (nth n ex))) tr = trace (nth n ex).
  Proof.
    intros tgl Hsp H. cbv [has_inf_trace] in H. specialize (H (length (trace (nth n ex)))).
    destruct H as [m H]. rewrite <- H. pose proof (trace_longer_trans _ _ tgl Hsp) as H0.
    assert (n <= m \/ m <= n) by lia. destruct H1 as [H1|H1].
    - specialize (H0 _ _ H1). destruct H0 as [tr' Htr']. rewrite Htr'.
      rewrite lfirstn_app_r. reflexivity.
    - specialize (H0 _ _ H1). eassert (H': forall x y, x = y -> length x = length y).
      { intros. subst. reflexivity. }
      apply H' in H. rewrite length_lfirstn in H. rewrite length_firstn in H.
      destruct H0 as [tr' Htr']. rewrite Htr'. apply H' in Htr'.
      rewrite List.length_app in Htr'.
      assert (length tr' = 0) by lia. destruct tr'; [|discriminate H0].
      rewrite List.app_nil_r. rewrite lfirstn_all. reflexivity.
  Qed.

  Fixpoint lskipn {T : Type} n (l : list T) :=
    match n, l with
    | S n', cons _ l' => lskipn n' l'
    | _, _ => l
    end.

  Lemma firstn_app_skipn {T : Type} n (l : list T) :
    (lfirstn n l ++ lskipn n l = l)%list.
  Proof.
    revert n. induction l; intros n.
    - destruct n; reflexivity.
    - destruct n; [reflexivity|]. simpl. f_equal. auto.
  Qed.

  Lemma lfirstn_firstn {T : Type} m n (s : stream T) :
    lfirstn m (firstn n s) = firstn (Nat.min m n) s.
  Proof.
    revert m s. induction n; intros m s.
    - simpl. destruct s. rewrite PeanoNat.Nat.min_0_r. destruct m; reflexivity.
    - simpl. destruct s. destruct m; [reflexivity|]. simpl. f_equal. apply IHn.
  Qed.
      
  Lemma aep_enough' sp lf ex tr :
    excluded_middle ->
    trace_gets_longer sp ->
    has_inf_trace ex tr ->
    sp ex ->
    (forall ex, sp ex -> OK ex) ->
    linterp_lol lf ex <-> interp_aep (aep_of tr lf) sp.
  Proof.
    intros em tgl H1 H2 H3. revert sp tgl ex H1 H2 H3.
    induction lf; cbn -[nth].
    - intros. split.
      + intros H' s Hs. exists O. intros x. eapply interp_aep_weaken.
        2: { specialize H with (2 := H1) (3 := H2). apply H; auto. }
        intros. destruct H0 as [_ H0]. simpl in H0. destruct s. simpl in H0. assumption.
      + intros H' n. specialize H' with (1 := H2). destruct H' as [n0 H'].
        specialize (H' n). specialize H with (ex := skipn n0 ex). rewrite <- H in H'.
        -- eapply linterp_lol_skipn; eassumption.
        -- eapply trace_gets_longer_preserved with (sp1 := sp).
           2: { intros ? [_ ?]. eassumption. }
           assumption.
        -- apply has_inf_trace_skipn. assumption.
        -- split.
           ++ rewrite nth_skipn. f_equal. lia.
           ++ rewrite andthen_firstn_skipn. assumption.
        -- intros. destruct H0 as (?&H0). apply H3 in H0. cbv [OK] in H0. cbv [OK].
           destruct H0 as [tr0 H0]. exists tr0. apply has_inf_trace_andthen in H0. apply H0.
    - intros. split.
      + intros H' s Hs. exists O. destruct H' as [x Hx]. exists x. eapply interp_aep_weaken.
        2: { specialize H with (2 := H1) (3 := H2). apply H; auto. }
        intros. destruct H0 as [_ H0]. simpl in H0. destruct s. simpl in H0. assumption.
      + intros H'. specialize H' with (1 := H2). destruct H' as [n (x&H')].
        exists x. specialize H with (ex := skipn n ex). rewrite <- H in H'.
        -- eapply linterp_lol_skipn; eassumption.
        -- eapply trace_gets_longer_preserved with (sp1 := sp).
           2: { intros ? [_ ?]. eassumption. }
           assumption.
        -- apply has_inf_trace_skipn. assumption.
        -- split.
           ++ rewrite nth_skipn. f_equal. lia.
           ++ rewrite andthen_firstn_skipn. assumption.
        -- intros. destruct H0 as (?&H0). apply H3 in H0. cbv [OK] in H0. cbv [OK].
           destruct H0 as [tr0 H0]. exists tr0. apply has_inf_trace_andthen in H0. apply H0.
    - intros. split.
      + intros [n Hn] s Hs. apply H3 in Hs. destruct Hs as [tr' Htr'].
        assert (Hem := em (forall n0, firstn n0 tr = firstn n0 tr')).
        destruct Hem as [same|not_same].
        -- cbv [has_inf_trace] in Htr'. specialize (Htr' (length (trace (nth n ex)))).
           destruct Htr' as [m Htr']. rewrite <- same in Htr'. clear same tr'. exists m.
           left. pose proof firstn_inf_trace as fit.
           specialize fit with (1 := tgl) (2 := H2).
             rewrite fit in Htr' by assumption. clear fit.
           epose proof (firstn_app_skipn _ (trace (nth m s))) as H. rewrite Htr' in H.
           rewrite <- H. intros l. rewrite <- List.app_assoc. apply Hn.
        -- apply naen in not_same; [|assumption]. destruct not_same as [y not_same].
           cbv [has_inf_trace] in Htr'. specialize (Htr' y). destruct Htr' as [m Htr'].
           exists m. right. intros H'. rewrite H' in Htr'. apply not_same. rewrite <- Htr'.
           rewrite lfirstn_firstn in *. f_equal.
           eassert (H0: forall x y, x = y -> length x = length y).
           { intros. subst. reflexivity. }
           apply H0 in Htr'. do 2 rewrite length_firstn in Htr'. auto.
      + intros H'. specialize (H' _ H2). destruct H' as [n H']. exists n.
        destruct H' as [H'|H'].
        -- assumption.
        -- exfalso. apply H'. symmetry.
           pose proof firstn_inf_trace as fit.
           specialize fit with (1 := tgl) (2 := H2).
           apply fit; assumption.
  Qed.
  
  Lemma traces_diff ex tr tr' :
    excluded_middle ->
    has_inf_trace ex tr ->
    ~has_inf_trace ex tr' ->
    exists n, firstn n tr <> firstn n tr'.
  Proof.
    intros em H1 H2. cbv [has_inf_trace] in H2. apply naen in H2; [|assumption].
    destruct H2 as [n H2]. exists n. intros H'. apply H2. clear H2. rewrite <- H'. clear H'.
    cbv [has_inf_trace] in H1. apply H1.
  Qed.
      
  Lemma vacuity sp tr lf :
    excluded_middle ->
    (forall ex, sp ex -> OK ex) ->
    (forall ex, sp ex -> has_inf_trace ex tr -> False) ->
    interp_aep (aep_of tr lf) sp.
  Proof.
    intros em allOK H'. induction lf; cbn -[nth].
    - intros s Hs. exists O. intros x. eapply interp_aep_weaken. 2: eapply H.
      intros ? [_ H0]. simpl in H0. destruct s. simpl in H0. assumption.
    - intros s Hs. exists O. exists u. eapply interp_aep_weaken. 2: apply H.
      intros ? [_ H0]. destruct s. simpl in H0. assumption.
    - intros s Hs. specialize H' with (1 := Hs). specialize allOK with (1 := Hs).
      destruct allOK as [tr' Htr']. pose proof traces_diff as H.
      specialize H with (1 := em) (2 := Htr') (3 := H'). destruct H as [n H].
      specialize (Htr' n). destruct Htr' as [m Htr']. exists m. right.
      rewrite <- Htr' in H.
      eassert (H'': forall x y, x = y -> length x = length y).
      { intros. subst. reflexivity. }
      apply H'' in Htr'. clear H''.
      intros H''. rewrite H'' in H.
      apply H. rewrite lfirstn_firstn. f_equal.
      rewrite length_firstn, length_lfirstn in Htr'. apply Htr'.
  Qed.

  Lemma aep_enough sp lf :
    excluded_middle ->
    trace_gets_longer sp ->
    (forall ex, sp ex -> OK ex) ->
    (forall ex, sp ex ->
           linterp_lol lf ex) <->
      interp_aep (AEP_A _ _ (fun tgt => (aep_of tgt lf))) sp.
  Proof.
    intros em tgl allOK. pose proof aep_enough' as H'.
    specialize H' with (1 := em). split; intros H.
    - specialize H' with (1 := tgl).
      cbn -[nth]. intros. exists O. intros tr.
      eapply interp_aep_weaken with (sp1 := sp).
      { intros ? (?&?). simpl in H2. destruct s. simpl in H2. apply H2. }
      clear s H0.
      assert (Hem := em (exists ex, sp ex /\ has_inf_trace ex tr)).
      destruct Hem as [Hex|Hne].
      + destruct Hex as (ex&Hsp&Hinf). rewrite <- H'; eauto.
      + apply vacuity; try assumption. intros. apply Hne. eexists; eauto.
    - intros ex Hex. cbn -[nth] in H. specialize (H ex Hex). destruct H as [n H].
      (* specialize H' with (2 := Hex). specialize H' with (2 := allOK). *)
      assert (Htr := allOK). specialize Htr with (1 := Hex).
      destruct Htr as [tr Htr]. (* specialize H' with (1 := Htr). *)
      specialize (H tr). eapply linterp_lol_skipn; try eassumption. erewrite H'.
      1: eassumption.
      3: { cbn -[nth]. rewrite nth_skipn. instantiate (1 := n). split.
           { f_equal. lia. }
           rewrite andthen_firstn_skipn. assumption. }
      + eapply trace_gets_longer_preserved; eauto. intros ? [? ?]. eassumption.
      + apply has_inf_trace_skipn. assumption.
      + cbn -[nth]. intros ? [? ?]. simpl. apply allOK in H1. destruct H1 as [tr' Htr'].
        exists tr'. Search has_inf_trace. eapply has_inf_trace_andthen. eassumption.
  Qed.
  
  Lemma linterp_iff_linterp_lol sp lf tr ex :
    trace_gets_longer sp ->
    sp ex ->
    has_inf_trace ex tr ->
    linterp Event lf tr <-> linterp_lol lf ex.
  Proof.
    intros tgl. pose proof trace_longer_trans as Htl.
    specialize Htl with (1 := tgl). 
    intros Hsp. specialize (Htl _ Hsp). 
    intros H. induction lf; intros; simpl.
    - split; intros; apply H0; auto.
    - split; intros (?&?); eexists; apply H0; eauto.
    - split; intros (n&H').
      + cbv [has_inf_trace] in H. specialize (H n). destruct H as [m H].
        exists m. intros l. rewrite <- (firstn_app_skipn n (trace _)).
        rewrite <- List.app_assoc. rewrite H. apply H'.
      + exists (length (trace (nth n ex))). Search has_inf_trace.
        erewrite firstn_inf_trace by eassumption. assumption.
  Qed.

  Lemma sinterp_to_aep' sp sf :
    excluded_middle ->
    (forall U : Type, FunctionalChoice_on U (lformula Event)) ->
    trace_gets_longer sp ->
    (forall ex, sp ex -> OK ex) ->
    exists lf,
    interp_aep (AEP_A _ _ (fun tgt => (aep_of tgt lf))) sp <->
      (forall ex, sp ex ->
             exists tr, has_inf_trace ex tr /\ sinterp _ sf tr).
  Proof.
    intros em choice tgl allOK. pose proof (finite_prefixes_enough Event ev) as fpe.
    specialize (fpe sf em choice). destruct fpe as [lf fpe]. exists lf.
    rewrite <- aep_enough by assumption. split.
    - intros H ex Hsp. specialize allOK with (1 := Hsp). destruct allOK as [tr Htr].
      exists tr. split; [assumption|]. rewrite fpe.
      rewrite linterp_iff_linterp_lol by eassumption. apply H. assumption.
    - intros H ex Hsp. specialize H with (1 := Hsp). destruct H as [tr (H1&H2)].
      rewrite <- linterp_iff_linterp_lol by eassumption.
      rewrite <- fpe. assumption.
  Qed.

  (* Lemma suffixes_better {U : Type} (aep : AEP (U -> Prop)) sp sp' : *)
  (*   interp_aep aep sp -> *)
  (*   (forall s, sp' s -> exists l, sp (and_then l s)) -> *)
  (*   interp_aep aep sp'. *)
  (* Proof. *)
  (*   revert sp sp'. induction aep; intros sp sp' H1 H2. *)
  (*   - cbn -[nth]. intros s Hs. specialize H2 with (1 := Hs). destruct H2 as [l Hl]. *)
  (*     cbn -[nth] in H1. specialize H1 with (1 := Hl). destruct H1 as [n H1]. *)
  (*     exists (n + length l). intros x. eapply H. 1: eauto. cbn -[nth]. intros s0 (H2&H3). *)
      
  (*     simpl. .eapply interp_aep_weaken. 2: eauto. cbn -[nth]. *)
  (*     intros. *)
  (*   revert sp sp'. induction aep; intros sp sp' H1 H2; cbn -[nth]. *)
  (*   - intros s Hsp. cbn -[nth] in H1. specialize H2 with (1 := Hsp). *)
  (*     destruct H2 as [l H2]. specialize H1 with (1 := H2). destruct H1 as [n H1]. *)
  (*     exists n. intros x. eapply H; [apply H1|]. cbn -[nth]. intros.  *)
  
  Lemma AEP_A_forall U sp aep :
    interp_aep (AEP_A _ U aep) sp <-> forall u, interp_aep (U := U) (aep u) sp.
  Proof.
    split.
    2: { intros H. cbn -[nth]. intros s Hs. exists O. intros x. Search interp_aep.
    - cbn -[nth]. (*TODO use suffixes_better here*) Abort.
  

  Definition AEP_and {T : Type} (l r : AEP T) :=
    AEP_A _ bool (fun b => if b then l else r).

  Lemma AEP_and_works {T : Type} (l r : AEP (T -> Prop)) sp :
    interp_aep (AEP_and l r) sp <-> (interp_aep l sp /\ interp_aep r sp).
  Proof. (*TODO is corollary of AEP_A_forall*) Abort.

  Definition AEP_is_inf : AEP (State -> Prop) :=
    AEP_A _ nat (fun n => AEP_P _ (fun x => length (trace x) = n)).
  
  Lemma sinterp_to_aep sp sf :
    excluded_middle ->
    (forall U : Type, FunctionalChoice_on U (lformula Event)) ->
    trace_gets_longer sp ->
    exists lf,
      interp_aep (AEP_and AEP_is_inf (AEP_A _ _ (fun tgt => (aep_of tgt lf)))) sp <->
        (forall ex, sp ex ->
               exists tr, has_inf_trace ex tr /\ sinterp _ sf tr).
  Proof. (*TODO follows from AEP_and_works*) Abort.
End OK_execution.
