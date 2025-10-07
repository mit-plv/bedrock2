Require Import riscv.Utility.runsToNonDet.
Require Import BinIntDef.
Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.ClassicalFacts.
Require Import Lia.
Require Import Coq.Lists.Streams.

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

Import List.
Section streams.
  Context (State : Type) (might_step : State -> State -> Prop).
  
  Fixpoint Str_firstn {T : Type} (n : nat) (s : Stream T) : list T :=
    match s, n with
    | Cons a rest, S n' => a :: Str_firstn n' rest
    | Cons a rest, O => nil
    end.

  CoInductive possible : Stream State -> Prop :=
  | poss a b rest : might_step a b ->
                    possible (Cons b rest) ->
                    possible (Cons a (Cons b rest)).

  Inductive lpossible : list State -> Prop :=
  | lposs_nil : lpossible nil
  | lposs_one a : lpossible (cons a nil)
  | lposs_cons a b rest : might_step a b ->
                          lpossible (cons b rest) ->
                          lpossible (cons a (cons b rest)).
  
  CoFixpoint stream_of {T : Type} (start : T) (step : T -> T) :=
    Cons start (stream_of (step start) step).

  Lemma stream_of_eq T (start : T) step_ :
    stream_of start step_ = Cons start (stream_of (step_ start) step_).
  Proof. replace (stream_of start step_) with (match stream_of start step_ with
                                               | Cons hd tl => Cons hd tl
                                               end).
         { reflexivity. }
         destruct (stream_of _ _). reflexivity.
  Qed.

  (*taken from https://github.com/OwenConoly/semantics_relations/blob/master/equiv/EquivProof.v*)
  Lemma chains_finite_implies_Acc x :
    excluded_middle ->
    FunctionalChoice_on State State ->
    (forall str, Str_nth O str = x -> possible str -> False) ->
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

  Lemma lnth_firstn {T : Type} n n1 (t : Stream T) :
    n < n1 /\ nth_error (Str_firstn n1 t) n = Some (Str_nth n t) \/ n >= n1 /\ nth_error (Str_firstn n1 t) n = None.
  Proof.
    clear. revert n t. induction n1; intros.
    - right. split; [lia|]. simpl. destruct t. destruct n; reflexivity.
    - simpl. destruct t. destruct n; simpl.
      + left. split; [lia|]. reflexivity.
      + specialize (IHn1 n t0). destruct IHn1 as [(H1&H2)|(H1&H2)]; [left|right]; split; try lia;  assumption.
  Qed.
  
  Lemma lnth_firstn_Some {T : Type} n n1 (t : Stream T) :
    n < n1 ->
    nth_error (Str_firstn n1 t) n = Some (Str_nth n t).
  Proof. pose proof (lnth_firstn n n1 t). destruct H as [(H1&H2)|(H1&H2)]; [auto|lia]. Qed.

  Definition last_elt {T : Type} (l : list T) := nth_error l (length l - 1).
  
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
    R (Str_nth n str) (Str_nth (S n) str).
  Proof.
    revert str. induction n.
    - intros str H. inversion H. subst. simpl. assumption.
    - intros str H. inversion H. subst. simpl. apply IHn. assumption.
  Qed.

  Lemma possible_skipn {U : Type} str (R : U -> U -> Prop) n :
    possible U R str ->
    possible U R (Str_nth_tl n str).
  Proof.
    revert str. induction n.
    - intros str H. inversion H. subst. simpl. assumption.
    - intros str H. inversion H. subst. simpl. apply IHn. assumption.
  Qed.

  Lemma lpossible_firstn {U : Type} str (R : U -> U -> Prop) n :
    possible U R str ->
    lpossible U R (Str_firstn n str).
  Proof.
    revert str. induction n.
    - intros. destruct str. simpl. constructor.
    - intros. destruct str. simpl. inversion H. subst. destruct n.
      1: constructor. constructor; auto. apply IHn in H3. simpl in H3.
      apply H3.
  Qed.

  Fixpoint and_then {U : Type} (l : list U) (s : Stream U) : Stream U :=
    match l with
    | nil => s
    | cons a l' => Cons a (and_then l' s)
    end.

  Lemma length_Str_firstn {A : Type} n (s : Stream A) : length (Str_firstn n s) = n.
  Proof.
    revert s. induction n; destruct s; [reflexivity|]. simpl. rewrite IHn. reflexivity.
  Qed.

  Lemma nth_andthen {U : Type} (l : list U) (s : Stream U) n :
    n < length l /\ Some (Str_nth n (and_then l s)) = nth_error l n \/
      length l <= n /\ Str_nth n (and_then l s) = Str_nth (n - length l) s.
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
    | Some x => R x (Str_nth O str)
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
    Str_nth_tl (length l) (and_then l s) = s.
  Proof. revert s. induction l; auto. Qed.         
  
  Lemma runsTo_iff_trace_pred s P :
    excluded_middle ->
    FunctionalChoice_on State State ->
    runsTo step s P <-> (forall str, possible _ might_step str ->
                               Str_nth O str = s ->
                               exists n, P (Str_nth n str)).
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
      assert (Hyp: forall str, Str_nth O str = s -> possible _ (fun x y => R y x) str -> False).
      { intros str HO Hsteps. subst. eassert _ as Hn.
        { apply H. 2: reflexivity. eapply possible_weaken. 1: eassumption.
          subst R. simpl. intros ? ? [? ?]. assumption. }
        destruct Hn as [n Hn]. apply (possible_nth _ _ n) in Hsteps. subst R.
        simpl in Hsteps. destruct Hsteps as [_ ?]. auto. }
      apply chains_finite_implies_Acc in Hyp; [|assumption|assumption].
      induction Hyp. assert (H' := em (P x)). destruct H' as [H'|H'].
      { apply runsToDone. assumption. }
      subst R. simpl in *. apply runsToStep_cps. intros y Hy. eapply H1; eauto.
      intros str. specialize (H (Cons x str)). intros Hstr ?. destruct str. subst.
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
    (sp : Stream U -> Prop) : Prop :=
    match aep with
    | AEP_A _ _ aep' =>
        forall s,
          sp s ->
          exists n,
          forall x, interp_aep (aep' x)
                 (fun sfx => Str_nth O sfx = Str_nth n s /\
                            sp (and_then (Str_firstn n s) sfx))
    | AEP_E _ _ aep' =>
        forall s,
          sp s ->
          exists n,
          exists x, interp_aep (aep' x)
                 (fun sfx => Str_nth O sfx = Str_nth n s /\
                            sp (and_then (Str_firstn n s) sfx))

    | AEP_P _ P =>
        forall s,
          sp s ->
          exists n,
            P (Str_nth n s)
    end.

  Lemma interp_aep_weaken {U : Type} (aep : AEP (U -> Prop)) (sp1 sp2 : Stream U -> Prop) :
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
      interp_aep aep (fun str => possible _ might_step str /\ Str_nth O str = s).
  Proof.
    intros em choice. revert s. induction aep; intros s.
    - rewrite runsTo_iff_trace_pred by assumption. split.
      + intros H'. cbn [interp_aep]. intros s0 (H1&H2). specialize (H' s0 H1 H2).
        destruct H' as [n Hn]. exists n. intros x. simpl in Hn. specialize (Hn x).
        apply H in Hn. eapply interp_aep_weaken. 2: eassumption. cbv beta.
        intros ? (H3&H4&H5). split; [|assumption].
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
              --- cbv [last_elt]. rewrite length_Str_firstn.
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
        intros ? (H3&H4&H5). split; [|assumption].
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
              --- cbv [last_elt]. rewrite length_Str_firstn.
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
      interp_aep aep (fun str => possible _ might_step str /\ Str_nth O str = s).
  Proof. rewrite step'_iff_step. apply runsTo_iff_trace_pred'. Qed.
End more_omni_trad.

Section post_of_surj.
  Context (Event : Type) (State : Type) (st : State).
  Context (might_step : State -> State -> Prop).
  Notation step := (step _ might_step).

  (*fancy formulas stating predicates about event streams*)
  Inductive fformula :=
  | fforall (U : Type) : (U -> fformula) -> fformula
  | fexists (U : Type) : (U -> fformula) -> fformula
  | fasstn (n : nat) : (State -> fformula) -> fformula
  | fpropn : Prop -> fformula
  | fand : fformula -> fformula -> fformula
  | fnot : fformula -> fformula.

  Fixpoint finterp (f : fformula) (t : Stream State) : Prop :=
    match f with
    | fforall _ f' => forall n, finterp (f' n) t
    | fexists _ f' => exists n, finterp (f' n) t
    | fasstn n f' => finterp (f' (Str_nth n t)) t
    | fpropn P => P
    | fand f1 f2 => finterp f1 t /\ finterp f2 t
    | fnot f' => ~finterp f' t
    end.
  
  (*For concreteness, say this is the set of stream predicates that can be written in Coq.*)
  Axiom definable : (Stream State -> Prop) -> Prop.

  (*Hopefully this is believable.*)
  Axiom definable_characterization :
    forall P, definable P ->
         exists (f : fformula), forall t, P t <-> finterp f t.

  (*a formula stating a predicate about event streams*)
  Inductive sformula :=
  | sforall (U : Type) (u : U) : (U -> sformula) -> sformula
  | sexists (U : Type) (u : U) : (U -> sformula) -> sformula
  (*assertion about the nth element of the stream*)
  | sasstn (n : nat) : (State -> sformula) -> sformula
  (*base case: a prop*)
  | spropn : Prop -> sformula.

  Fixpoint sinterp (f : sformula) (t : Stream State) : Prop :=
    match f with
    | sforall U u f' => forall n, sinterp (f' n) t
    | sexists U u f' => exists n, sinterp (f' n) t
    | sasstn n f' => sinterp (f' (Str_nth n t)) t
    | spropn P => P
    end.

  Fixpoint neg (f : sformula) :=
    match f with
    | sforall _ u0 f' => sexists _ u0 (fun u => neg (f' u))
    | sexists _ u0 f' => sforall _ u0 (fun u => neg (f' u))
    | sasstn n f' => sasstn n (fun s => neg (f' s))
    | spropn P => spropn (~P)
    end.

  Fixpoint sformula_of (f : fformula) :=
    match f with
    | fforall _ f' => sforall _ (inl tt) (fun u =>
                                           match u with
                                           | inl _ => spropn True
                                           | inr u' => sformula_of (f' u')
                                           end)
    | fexists _ f' => sexists _ (inl tt) (fun u =>
                                           match u with
                                           | inl _ => spropn False
                                           | inr u' => sformula_of (f' u')
                                           end)
    | fasstn n f' => sasstn n (fun s => sformula_of (f' s))
    | fpropn P => spropn P
    | fnot f' => neg (sformula_of f')
    | fand f1 f2 => sforall _ true (fun b => if b then sformula_of f1 else sformula_of f2)
    end.

  Require Import coqutil.Tactics.fwd.
  Lemma neg_works sf t :
    excluded_middle ->
    sinterp (neg sf) t <-> ~sinterp sf t.
  Proof.
    intros em. induction sf; simpl; split; cbv [not] in *; intros; fwd;
      try solve [edestruct H; eauto].
    apply naen in H0; try assumption. destruct H0 as [y H0]. edestruct H; eauto.
  Qed.
      
  Lemma sformula_of_works ff t :
    excluded_middle ->
    finterp ff t <-> sinterp (sformula_of ff) t.
  Proof.
    clear. intros em. induction ff; intros; simpl; split; intros; fwd;
      try assumption;
      try solve [auto; edestruct H; eauto].
    - destruct n. { simpl. constructor. } edestruct H; eauto.
    - specialize (H0 (inr n)). simpl in H0. edestruct H; eauto.
    - eexists (inr _). edestruct H; eauto.
    - destruct n; simpl in H0; [solve[destruct H0]|]. edestruct H; eauto.
    - destruct n; edestruct IHff1, IHff2; eauto.
    - pose proof (H false). pose proof (H true). simpl in *. destruct IHff1, IHff2; eauto.
    - apply neg_works; try assumption. destruct IHff; eauto.
    - apply neg_works in H; try assumption. destruct IHff; auto.
  Qed.
  
  (*about lists*)
  Inductive lformula :=
  | lforall (U : Type) (u : U) : (U -> lformula) -> lformula
  | lexists (U : Type) (u : U) : (U -> lformula) -> lformula
  | lpropn : (list State -> Prop) -> lformula.

  Fixpoint linterp (f : lformula) (t : Stream State) : Prop :=
    match f with
    | lforall U _ f' => forall n, linterp (f' n) t
    | lexists U _ f' => exists n, linterp (f' n) t
    | lpropn P => exists n, forall l, P (Str_firstn n t ++ l)%list
    end.

  Lemma firstn_split {T : Type} n m (t : Stream T) :
    n <= m ->
    Str_firstn m t = (Str_firstn n t ++ (Str_firstn (m - n) (Str_nth_tl n t)))%list.
  Proof.
    revert n t. induction m; intros n t Hn.
    - destruct n; [|lia]. destruct t. reflexivity.
    - destruct n.
      + destruct t. simpl. reflexivity.
      + destruct t. simpl. f_equal. apply IHm. lia.
  Qed.

  Lemma lnth_app_r {T : Type} n l l0 (x : T) :
    nth_error l n = Some x ->
    nth_error (l ++ l0) n = Some x.
  Proof.
    revert l. induction n; intros l H; (destruct l; simpl in *; [congruence|]); auto.
  Qed.

  (*lf is true, and nth is equal to s*)
  Fixpoint assert_nth s n lf : lformula :=
    match lf with
    | lforall _ u0 lf' => lforall _ u0 (fun u => assert_nth s n (lf' u))
    | lexists _ u0 lf' => lexists _ u0 (fun u => assert_nth s n (lf' u))
    | lpropn P => lpropn (fun l => P l /\ nth_error l n = Some s)
    end.
  
  Lemma assert_nth_works s n lf :
    forall t, linterp (assert_nth s n lf) t <-> (linterp lf t /\ Str_nth n t = s).
  Proof.
    clear. induction lf.
    - intros. simpl. split.
      + intros. (*hmm here we use that quantfiers are not vacuous.  relevant?*)
        assert (HO := H0 u). rewrite H in HO. destruct HO as [_ HO].
        split; [|assumption]. intros n0. specialize (H0 n0). rewrite H in H0.
        destruct H0. assumption.
      + intros H0 n0. rewrite H. destruct H0. auto.
    - intros. simpl. split.
      + intros [n0 Hn0]. rewrite H in Hn0. intuition eauto.
      + intros ([n0 H0] & H1). eexists. rewrite H. eauto.
    - intros t. simpl. split.
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

  Fixpoint lf_of sf :=
    match sf with
    | sforall _ u0 sf' => lforall _ u0 (fun u => lf_of (sf' u))
    | sexists _ u0 sf' => lexists _ u0 (fun u => lf_of (sf' u))
    | sasstn n sf' => lexists _ st (fun st' => assert_nth st' n (lf_of (sf' st')))
    | spropn P => lpropn (fun _ => P)
    end.
  
  Lemma finite_prefixes_enough sf :
    forall t, sinterp sf t <-> linterp (lf_of sf) t.
  Proof.
    clear -st. induction sf.
    - intros. simpl. split; intros; edestruct H; eauto.
    - intros. simpl. split; intros (?&?); edestruct H; eauto.
    - simpl. intros. split.
      + intros H'. exists (Str_nth n t). apply assert_nth_works. rewrite <- H. auto.
      + intros [n0 H']. apply assert_nth_works in H'. rewrite <- H in H'.
        destruct H'. subst. assumption.
    - simpl. split; eauto using O, nil. intros (?&?). auto using nil.
  Qed.
End post_of_surj.

Section OK_execution.
  Context (State : Type).
  Context (Event : Type) (ev : Event) (trace : State -> list Event).
  Context (post : State -> Prop).

  Definition trace_gets_longer (sp : _ -> Prop) :=
    forall s, sp s ->
         forall n, exists tr', trace (Str_nth (S n) s) = trace (Str_nth n s) ++ tr'.

  Lemma trace_longer_trans sp s :
    trace_gets_longer sp ->
    sp s ->
    forall n1 n2,
      n1 <= n2 ->
      exists tr', trace (Str_nth n2 s) = trace (Str_nth n1 s) ++ tr'.
  Proof.
    intros tgl H. specialize (tgl _ H). clear H. intros n1 n2 H.
    replace n2 with ((n2 - n1) + n1) by lia. clear H. remember (n2 - n1) as n.
    clear Heqn n2. induction n.
    - exists nil. rewrite List.app_nil_r. reflexivity.
    - destruct IHn as [tr' IHn]. specialize (tgl (n + n1)).
      destruct tgl as [tr'' tgl]. cbn -[nth]. rewrite tgl, IHn.
      rewrite <- List.app_assoc. eexists. reflexivity.
  Qed.

  Definition has_inf_trace (ex : Stream State) (tr : Stream Event) :=
    forall n, exists m, List.firstn n (trace (Str_nth m ex)) = Str_firstn n tr.

  Definition OK (ex : Stream State) :=
    (exists n, post (Str_nth n ex)) \/ exists tr, has_inf_trace ex tr.

  Fixpoint linterp_lol (f : lformula Event) (t : Stream State) : Prop :=
    match f with
    | lforall _ U _ f' => forall n, linterp_lol (f' n) t
    | lexists _ U _ f' => exists n, linterp_lol (f' n) t
    | lpropn _ P => exists n, forall l, P (List.app (trace (Str_nth n t)) l)
    end.

  Fixpoint aep_of (tgt : Stream Event) (lf : lformula Event) : AEP (State -> Prop) :=
    match lf with
    | lforall _ U u af' => AEP_A _ _ (fun x => aep_of tgt (af' x))
    | lexists _ U u af' => AEP_E _ _ (fun x => aep_of tgt (af' x))
    | lpropn _ P => AEP_P _ (fun s => (forall l, P (trace s ++ l)%list) \/ (trace s) <> Str_firstn (length (trace s)) tgt \/ post s)
    end.

  Lemma linterp_lol_skipn lf n sp s :
    trace_gets_longer sp ->
    sp s ->
    linterp_lol lf (Str_nth_tl n s) <-> linterp_lol lf s.
  Proof.
    intros tgl Hsp. induction lf; simpl; split; intros H'.
    - intros. apply H. apply H'.
    - intros. apply H. apply H'.
    - destruct H' as [n0 Hn0]. exists n0. apply H. apply Hn0.
    - destruct H' as [n0 Hn0]. exists n0. apply H. apply Hn0.
    - destruct H' as [n0 H']. exists (n0 + n). intros.
      pose proof trace_longer_trans as H. specialize H with (1 := tgl).
      specialize (H s Hsp). rewrite Str_nth_plus in H'. apply H'.
    - destruct H' as [n0 H']. exists n0. intros.
      pose proof trace_longer_trans as H. specialize H with (1 := tgl).
      specialize (H s Hsp). specialize (H n0 (n0 + n) ltac:(lia)).
      destruct H as [tr' Htr']. rewrite Str_nth_plus. rewrite Htr'.
      rewrite <- List.app_assoc. apply H'.
  Qed.

  Lemma firstns_something {T : Type} n m (l : list T) s : 
    m <= n ->
    firstn n l = Str_firstn n s ->
    firstn m l = Str_firstn m s.
  Proof.
    revert n m s. induction l; intros n m s Hmn H.
    - destruct s. destruct n; [|discriminate H]. replace m with 0 by lia. reflexivity.
    - destruct s. destruct m; [reflexivity|]. destruct n; [lia|]. simpl in H.
      inversion H. subst. clear H. simpl. f_equal. eapply IHl. 2: eassumption. lia.
  Qed.

  Lemma tail_has_inf_trace a s tr :
    has_inf_trace (Cons a s) tr <->
    has_inf_trace s tr.
  Proof.
    split; cbv [has_inf_trace]; intros H' n.
    - specialize (H' (n + S (length (trace a)))). destruct H' as [m H'].
      destruct m.
      + simpl in H'. eassert (forall x y, length x <> length y -> x <> y).
        2: { exfalso. eapply H. 2: exact H'. rewrite length_firstn.
             rewrite length_Str_firstn. cbv [Str_nth]. simpl. lia. }
        intros. intros H''. apply H. subst. reflexivity.
      + exists m. simpl in H'. eapply firstns_something. 2: eassumption. lia.
    - specialize (H' n). destruct H' as [m H']. exists (S m). simpl. assumption.
  Qed.
      
  Lemma has_inf_trace_skipn n s tr :
    has_inf_trace s tr <-> has_inf_trace (Str_nth_tl n s) tr.
  Proof.
    revert s. induction n; simpl; split; intros H'; try assumption.
    - destruct s. rewrite <- IHn. eapply tail_has_inf_trace. eassumption.
    - destruct s. rewrite <- IHn in H'. apply tail_has_inf_trace. apply H'.
  Qed.

  Lemma has_inf_trace_andthen l s tr :
    has_inf_trace s tr <-> has_inf_trace (and_then l s) tr.
  Proof.
    replace (has_inf_trace s tr) with 
      (has_inf_trace (Str_nth_tl (length l) (and_then l s)) tr).
    { split; apply has_inf_trace_skipn. }
    f_equal. rewrite skipn_andthen. reflexivity.
  Qed.

  Lemma andthen_firstn_skipn {T : Type} (s : Stream T) n :
    and_then (Str_firstn n s) (Str_nth_tl n s) = s.
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

  Lemma firstn_inf_trace sp n ex tr :
    trace_gets_longer sp ->
    sp ex ->
    has_inf_trace ex tr ->
    Str_firstn (length (trace (Str_nth n ex))) tr = trace (Str_nth n ex).
  Proof.
    intros tgl Hsp H. cbv [has_inf_trace] in H. specialize (H (length (trace (Str_nth n ex)))).
    destruct H as [m H]. rewrite <- H. pose proof (trace_longer_trans _ _ tgl Hsp) as H0.
    assert (n <= m \/ m <= n) by lia. destruct H1 as [H1|H1].
    - specialize (H0 _ _ H1). destruct H0 as [tr' Htr']. rewrite Htr'.
      rewrite List.firstn_app_l by reflexivity. reflexivity.
    - specialize (H0 _ _ H1). eassert (H': forall x y, x = y -> length x = length y).
      { intros. subst. reflexivity. }
      apply H' in H. rewrite length_Str_firstn in H. rewrite length_firstn in H.
      destruct H0 as [tr' Htr']. rewrite Htr'. apply H' in Htr'.
      rewrite List.length_app in Htr'.
      assert (length tr' = 0) by lia. destruct tr'; [|discriminate H0].
      rewrite List.app_nil_r. rewrite firstn_all. reflexivity.
  Qed.

  Lemma firstn_Str_firstn {T : Type} m n (s : Stream T) :
    firstn m (Str_firstn n s) = Str_firstn (Nat.min m n) s.
  Proof.
    revert m s. induction n; intros m s.
    - simpl. destruct s. rewrite PeanoNat.Nat.min_0_r. destruct m; reflexivity.
    - simpl. destruct s. destruct m; [reflexivity|]. simpl. f_equal. apply IHn.
  Qed.

  Lemma lnth_oob {U : Type} (l : list U) n :
    length l <= n ->
    nth_error l n = None.
  Proof.
    revert n. induction l.
    - intros. destruct n; reflexivity.
    - simpl. intros. destruct n; [lia|]. simpl. apply IHl. lia.
  Qed.
      
  Lemma nth_andthen' {U : Type} (l : list U) s n :
    Str_nth n (and_then l s) = match nth_error l n with
                               | Some x => x
                               | None => Str_nth (n - length l) s
                               end.
  Proof.
    pose proof (nth_andthen l s n) as H. destruct H as [(H1&H2)|(H1&H2)].
    - rewrite <- H2. reflexivity.
    - rewrite H2. rewrite lnth_oob by lia. reflexivity.
  Qed.

  Lemma nth_andthen_r {U : Type} (l : list U) s n :
    length l <= n ->
    Str_nth n (and_then l s) = Str_nth (n - length l) s.
  Proof.
    pose proof (nth_andthen l s n) as H. destruct H as [(H1&H2)|(H1&H2)].
    - lia.
    - intros. assumption.
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
        exists m. intros l. rewrite <- (firstn_skipn n (trace _)).
        rewrite <- List.app_assoc. rewrite H. apply H'.
      + exists (length (trace (Str_nth n ex))).
        erewrite firstn_inf_trace by eassumption. assumption.
  Qed.
  
  Lemma aep_enough' sp lf ex tr :
    excluded_middle ->
    trace_gets_longer sp ->
    has_inf_trace ex tr ->
    (forall n, ~post (Str_nth n ex)) ->
    sp ex ->
    (forall ex, sp ex -> OK ex) ->
    linterp_lol lf ex <-> interp_aep (aep_of tr lf) sp.
  Proof.
    intros em tgl H1 H0 H2 H3. revert sp tgl ex H1 H0 H2 H3.
    induction lf; cbn -[nth].
    - intros. split.
      + intros H' s Hs. exists O. intros x. eapply interp_aep_weaken.
        2: { specialize H with (2 := H1) (4 := H2) (3 := H0). apply H; auto. }
        intros str (_&H4). destruct s. simpl in H4. assumption.
      + intros H' n. specialize H' with (1 := H2). destruct H' as [n0 H'].
        specialize (H' n). specialize H with (ex := Str_nth_tl n0 ex). rewrite <- H in H'.
        -- eapply linterp_lol_skipn; eassumption.
        -- eapply trace_gets_longer_preserved with (sp1 := sp).
           2: { intros ? [_ ?]. eassumption. }
           assumption.
        -- apply has_inf_trace_skipn. assumption.
        -- intros. rewrite Str_nth_plus. auto.
        -- split.
           ++ rewrite Str_nth_plus. reflexivity.
           ++ rewrite andthen_firstn_skipn. assumption.
        -- intros ex' Hex'. destruct Hex' as (?&Hex'). apply H3 in Hex'.
           cbv [OK] in Hex'. cbv [OK]. destruct Hex' as [Hex'|Hex']; [left|right].
           ++ destruct Hex' as [n' Hn']. epose proof nth_andthen as Hna.
              edestruct Hna as [(H17&Hna')|(_&Hna')]; clear Hna; [|rewrite Hna' in Hn'].
              --- exfalso. eapply H0. rewrite length_Str_firstn in H17.
                  rewrite lnth_firstn_Some in Hna' by lia. inversion Hna'. rewrite <- H6.
                  assumption.
              --- eexists. eassumption.
           ++ destruct Hex' as [tr' Htr']. exists tr'.
              apply has_inf_trace_andthen in Htr'. apply Htr'.
    - intros. split.
      + intros H' s Hs. exists O. destruct H' as [x Hx]. exists x. eapply interp_aep_weaken.
        2: { specialize H with (2 := H1) (4 := H2) (3 := H0). apply H; auto. }
        intros ? (_&H4). destruct s. simpl in H4. assumption.
      + intros H'. specialize H' with (1 := H2). destruct H' as [n (x&H')].
        exists x. specialize H with (ex := Str_nth_tl n ex). rewrite <- H in H'.
        -- eapply linterp_lol_skipn; eassumption.
        -- eapply trace_gets_longer_preserved with (sp1 := sp).
           2: { intros ? [_ ?]. eassumption. }
           assumption.
        -- apply has_inf_trace_skipn. assumption.
        -- intros. rewrite Str_nth_plus. auto.
        -- split.
           ++ rewrite Str_nth_plus. reflexivity.
           ++ rewrite andthen_firstn_skipn. assumption.
        -- intros ex' Hex'. destruct Hex' as (?&Hex'). apply H3 in Hex'.
           cbv [OK] in Hex'. cbv [OK]. destruct Hex' as [Hex'|Hex']; [left|right].
           ++ destruct Hex' as [n' Hn']. epose proof nth_andthen as Hna.
              edestruct Hna as [(H17&Hna')|(_&Hna')]; clear Hna; [|rewrite Hna' in Hn'].
              --- exfalso. eapply H0. rewrite length_Str_firstn in H17.
                  rewrite lnth_firstn_Some in Hna' by lia. inversion Hna'. rewrite <- H6.
                  assumption.
              --- eexists. eassumption.
           ++ destruct Hex' as [tr' Htr']. exists tr'.
              apply has_inf_trace_andthen in Htr'. apply Htr'.
    - intros. split.
      + intros [n Hn] s Hs. apply H3 in Hs. destruct Hs as [Hs|Hs].
        { destruct Hs as [n' Hn']. exists n'. right. right. assumption. }
        destruct Hs as [tr' Htr'].
        assert (Hem := em (forall n0, Str_firstn n0 tr = Str_firstn n0 tr')).
        destruct Hem as [same|not_same].
        -- cbv [has_inf_trace] in Htr'. specialize (Htr' (length (trace (Str_nth n ex)))).
           destruct Htr' as [m Htr']. rewrite <- same in Htr'. clear same tr'. exists m.
           left. pose proof firstn_inf_trace as fit.
           specialize fit with (1 := tgl) (2 := H2).
           rewrite fit in Htr' by assumption. clear fit.
           epose proof (firstn_skipn _ (trace (Str_nth m s))) as H. rewrite Htr' in H.
           rewrite <- H. intros l. rewrite <- List.app_assoc. apply Hn.
        -- apply naen in not_same; [|assumption]. destruct not_same as [y not_same].
           cbv [has_inf_trace] in Htr'. specialize (Htr' y). destruct Htr' as [m Htr'].
           exists m. right. left. intros H'. rewrite H' in Htr'. apply not_same. rewrite <- Htr'.
           rewrite firstn_Str_firstn in *. f_equal.
           eassert (H5: forall x y, x = y -> length x = length y).
           { intros. subst. reflexivity. }
           apply H5 in Htr'. do 2 rewrite length_Str_firstn in Htr'. auto.
      + intros H'. specialize (H' _ H2). destruct H' as [n H']. exists n.
        destruct H' as [H'|[H'|H']].
        -- assumption.
        -- exfalso. apply H'. symmetry.
           pose proof firstn_inf_trace as fit.
           specialize fit with (1 := tgl) (2 := H2).
           apply fit; assumption.
        -- exfalso. eapply H0. eassumption.
  Qed.
  
  Lemma traces_diff ex tr tr' :
    excluded_middle ->
    has_inf_trace ex tr ->
    ~has_inf_trace ex tr' ->
    exists n, Str_firstn n tr <> Str_firstn n tr'.
  Proof.
    intros em H1 H2. cbv [has_inf_trace] in H2. apply naen in H2; [|assumption].
    destruct H2 as [n H2]. exists n. intros H'. apply H2. clear H2. rewrite <- H'. clear H'.
    cbv [has_inf_trace] in H1. apply H1.
  Qed.
      
  Lemma vacuity sp tr lf :
    excluded_middle ->
    (forall ex, sp ex -> OK ex) ->
    (forall ex, sp ex -> has_inf_trace ex tr -> ~(exists n, post (Str_nth n ex)) -> False) ->
    interp_aep (aep_of tr lf) sp.
  Proof.
    intros em allOK H'. induction lf; cbn -[nth].
    - intros s Hs. exists O. intros x. eapply interp_aep_weaken. 2: eapply H.
      intros ? [_ H0]. simpl in H0. destruct s. simpl in H0. assumption.
    - intros s Hs. exists O. exists u. eapply interp_aep_weaken. 2: apply H.
      intros ? [_ H0]. destruct s. simpl in H0. assumption.
    - intros s Hs. specialize H' with (1 := Hs). specialize allOK with (1 := Hs).
      destruct allOK as [sOK|sOK].
      { destruct sOK as [n Hn]. exists n. right. right. assumption. }
      destruct sOK as [tr' Htr']. pose proof traces_diff as H.
      eassert (Hem := em (exists n, post (Str_nth n s))). destruct Hem as [(n&Hn)|Hem].
      { eauto. }
      specialize H' with (2 := Hem).
      specialize H with (1 := em) (2 := Htr') (3 := H'). destruct H as [n H].
      specialize (Htr' n). destruct Htr' as [m Htr']. exists m. right. left.
      rewrite <- Htr' in H.
      eassert (H'': forall x y, x = y -> length x = length y).
      { intros. subst. reflexivity. }
      apply H'' in Htr'. clear H''.
      intros H''. rewrite H'' in H.
      apply H. rewrite firstn_Str_firstn. f_equal.
      rewrite length_firstn, length_Str_firstn in Htr'. apply Htr'.
  Qed.

  Lemma aep_enough sp lf :
    excluded_middle ->
    trace_gets_longer sp ->
    (forall ex, sp ex -> OK ex) ->
    (forall ex, sp ex ->
           (exists n, post (Str_nth n ex)) \/
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
      assert (Hem := em (exists ex, sp ex /\ has_inf_trace ex tr /\ ~(exists n, post (Str_nth n ex)))).
      destruct Hem as [Hex|Hne].
      + destruct Hex as (ex&Hsp&Hinf&Hnterm). rewrite <- H'; eauto.
        specialize H with (1 := Hsp). destruct H as [H|H]; eauto. exfalso. auto.
      + apply vacuity; try assumption. intros. apply Hne. eexists; eauto.
    - intros ex Hex. cbn -[nth] in H. specialize (H ex Hex). destruct H as [n H].
      assert (Htr := allOK). specialize Htr with (1 := Hex).
      destruct Htr as [Htr|Htr].
      { left. assumption. }
      destruct Htr as [tr Htr]. (* specialize H' with (1 := Htr). *)
      specialize (H tr). pose proof (em (exists n, post (Str_nth n ex))) as Hem.
      destruct Hem as [Hem|Hem]; [left; assumption|]. right.
      eapply linterp_lol_skipn; try eassumption. erewrite H'.
      1: eassumption.
      4: { cbn -[nth]. rewrite Str_nth_plus. instantiate (1 := n). split; [reflexivity|].
           rewrite andthen_firstn_skipn. assumption. }
      + eapply trace_gets_longer_preserved; eauto. intros ? [? ?]. eassumption.
      + apply has_inf_trace_skipn. assumption.
      + intros n0 Hn0. apply Hem. eexists. rewrite Str_nth_plus in Hn0. eassumption.
      (*TODO factor out below bullet into a lemma*)
      + intros ex' Hex'. destruct Hex' as (?&Hex'). apply allOK in Hex'.
        cbv [OK] in Hex'. cbv [OK]. destruct Hex' as [Hex'|Hex']; [left|right].
        -- destruct Hex' as [n' Hn']. epose proof nth_andthen as Hna.
           edestruct Hna as [(H17&Hna')|(_&Hna')]; clear Hna; [|rewrite Hna' in Hn'].
           ++ exfalso. eapply Hem. rewrite length_Str_firstn in H17.
              rewrite lnth_firstn_Some in Hna' by lia. inversion Hna'. eexists. rewrite <- H2.
              assumption.
           ++ eexists. eassumption.
        -- destruct Hex' as [tr' Htr']. exists tr'.
           apply has_inf_trace_andthen in Htr'. apply Htr'.
  Qed.
  
  Lemma sinterp_to_aep' sp sf :
    excluded_middle ->
    trace_gets_longer sp ->
    (forall ex, sp ex -> OK ex) ->
    interp_aep (AEP_A _ _ (fun tgt => (aep_of tgt (lf_of _ ev sf)))) sp <->
      (forall ex, sp ex ->
             (exists n, post (Str_nth n ex)) \/
               exists tr, has_inf_trace ex tr /\ sinterp _ sf tr).
  Proof.
    intros em tgl allOK. pose proof (finite_prefixes_enough Event ev) as fpe.
    specialize (fpe sf). rewrite <- aep_enough by assumption. split.
    - intros H ex Hsp. specialize allOK with (1 := Hsp).
      destruct allOK as [term|nonterm].
      { left. assumption. }
      destruct nonterm as (tr&Htr). pose proof (em (exists n, post (Str_nth n ex))) as Hem.
      destruct Hem as [Hem|Hem]; [left; assumption|]. right.
      exists tr. split; [assumption|]. rewrite fpe.
      rewrite linterp_iff_linterp_lol by eassumption. apply H in Hsp.
      destruct Hsp as [Hsp|Hsp]; [exfalso; auto|]. assumption.
    - intros H ex Hsp. specialize H with (1 := Hsp). destruct H as [H|(tr&H1&H2)].
      { left. assumption. }
      rewrite <- linterp_iff_linterp_lol by eassumption.
      rewrite <- fpe. right. assumption.
  Qed.

  Lemma andthen_assoc {U : Type} (l1 l2 : list U) s :
    and_then l1 (and_then l2 s) = and_then (List.app l1 l2) s.
  Proof.
    induction l1.
    - reflexivity.
    - simpl. f_equal. assumption.
  Qed.
    
  Lemma firstn_plus_m {U : Type} n m (s : Stream U) :
    Str_firstn n s ++ Str_firstn m (Str_nth_tl n s) = Str_firstn (n + m) s.
  Proof.
    revert s. induction n; intros s.
    - destruct s. simpl. reflexivity.
    - destruct s. simpl. f_equal. auto.
  Qed.
  
  Lemma AEP_A_forall {T U : Type} (sp : Stream T -> Prop) aep :
    excluded_middle ->
    interp_aep (AEP_A _ _ aep) sp <-> forall (u : U), interp_aep (aep u) sp.
  Proof.
    intros em. split.
    2: { intros H. cbn -[nth]. intros s Hs. exists O. intros x. eapply interp_aep_weaken.
         2: solve[auto]. intros str [H1 H2]. destruct s. simpl in H2. apply H2. }
    subst. cbn -[nth]. intros H u. destruct (aep u) eqn:E.
    + cbn -[nth]. intros s Hs. cbn -[nth] in H. specialize (H s Hs).
      destruct H as [n Hn]. specialize (Hn u). rewrite E in Hn. cbn -[nth] in Hn.
      specialize (Hn (Str_nth_tl n s)). edestruct Hn as (n0&H0); clear Hn.
      { rewrite Str_nth_plus. split; [f_equal; lia|]. rewrite andthen_firstn_skipn.
        assumption. }
      exists (n0 + n). intros x. specialize (H0 x). eapply interp_aep_weaken. 2: eassumption.
      cbn -[nth]. intros ? [H2 H3]. rewrite Str_nth_plus. rewrite H2.
      split; [f_equal; lia|]. split.
      -- destruct n0.
         ++ cbn -[nth]. destruct (Str_nth_tl n s). cbn -[nth]. assumption.
         ++ rewrite nth_andthen'. epose proof lnth_firstn as H.
            edestruct H as [(?&H')|(?&?)]; [rewrite H'|lia]. rewrite Str_nth_plus.
            reflexivity.
      -- rewrite andthen_assoc. rewrite firstn_plus_m.
         replace (n + n0) with (n0 + n) by lia. assumption.
    + cbn -[nth]. intros s Hs.
      cbn -[nth] in H. specialize (H s Hs). destruct H as [n Hn].
      specialize (Hn u). rewrite E in Hn. cbn -[nth] in Hn.
      specialize (Hn (Str_nth_tl n s)). edestruct Hn as (n0&x0&H0).
      { rewrite Str_nth_plus. split; [f_equal; lia|]. rewrite andthen_firstn_skipn.
        assumption. }
      exists (n + n0), x0. eapply interp_aep_weaken. 2: eapply H0.
      clear Hn H0. cbn -[nth]. intros ? (H2&H3). rewrite Str_nth_plus. rewrite H2.
      split; [f_equal; lia|]. split.
      -- destruct n0.
         ++ cbn -[nth]. destruct (Str_nth_tl n s). cbn -[nth]. rewrite H2. f_equal. lia.
         ++ rewrite nth_andthen'. epose proof lnth_firstn as H.
            edestruct H as [(?&H')|(?&?)]; [rewrite H'|lia]. rewrite Str_nth_plus.
            reflexivity.
      -- rewrite andthen_assoc. rewrite firstn_plus_m. assumption.
    + simpl. intros s Hs. specialize (H _ Hs). destruct H as [n Hn].
      specialize (Hn u). rewrite E in Hn. cbn -[nth] in Hn.
      specialize (Hn (Str_nth_tl n s)). edestruct Hn as [n0 Hn0].
      { rewrite Str_nth_plus. split; [f_equal; lia|]. rewrite andthen_firstn_skipn.
        assumption. }
      rewrite Str_nth_plus in Hn0. eexists. eassumption.
  Qed.

  Definition AEP_and {T : Type} (l r : AEP T) :=
    AEP_A _ bool (fun b => if b then l else r).

  Lemma AEP_and_works {T : Type} (l r : AEP (T -> Prop)) sp :
    excluded_middle ->
    interp_aep (AEP_and l r) sp <-> (interp_aep l sp /\ interp_aep r sp).
  Proof.
    intros em. cbv [AEP_and]. rewrite AEP_A_forall by assumption.
    split.
    - intros H. pose proof (H false). pose proof (H true). auto.
    - intros (H1&H2). intros u. destruct u; auto.
  Qed.

  Definition AEP_is_OK : AEP (State -> Prop) :=
    AEP_A _ nat (fun n => AEP_P _ (fun x => post x \/ length (trace x) > n)).

  Lemma lists_same {U : Type} (l1 l2 : list U) :
    (forall n, n < Nat.max (length l1) (length l2) ->
          nth_error l1 n = nth_error l2 n) ->
    l1 = l2.
  Proof.
    intros H. revert l2 H. induction l1; intros l2 H.
    - destruct l2; [reflexivity|]. simpl in H. specialize (H O ltac:(lia)).
      discriminate H.
    - cbn [length] in H. assert (HO := H O ltac:(lia)). destruct l2; [discriminate HO|].
      simpl in HO. inversion HO. subst. f_equal. apply IHl1. intros n Hn.
      specialize (H (S n)). simpl in H. apply H. lia.
  Qed.

  Lemma AEP_is_OK_works sp :
    excluded_middle ->
    FunctionalChoice_on nat nat ->
    trace_gets_longer sp ->
    interp_aep AEP_is_OK sp <-> (forall s, sp s -> OK s).
  Proof.
    intros em choice tgl. cbv [AEP_is_OK]. rewrite AEP_A_forall by assumption.
    split.
    - intros H s Hs. cbv [OK]. simpl in H. specialize H with (1 := Hs).
      eassert (Hf: exists f, _).
      { apply choice. intros x. specialize (H x). destruct H as [n Hn].
        exists n. exact Hn. }
      clear H. destruct Hf as [f Hf].
      set (trn := cofix trn (n : nat) : Stream Event :=
             Cons (match nth_error (trace (Str_nth (f n) s)) n with
                   | Some x => x
                   | None => ev
                   end) (trn (S n))).
      eassert (Hem := em _). destruct Hem as [Hem|Hem]; [left; exact Hem|].
      eassert (Hf': forall x, (_ : Prop)).
      { intros x. specialize (Hf x). destruct Hf as [Hf|Hf]; [|exact Hf].
        exfalso. apply Hem. eauto. }
      clear Hf. rename Hf' into Hf.
      right.
      exists (trn O). cbv [has_inf_trace]. intros n. assert (Hn := Hf n).
      exists (f n). apply lists_same. rewrite length_firstn. rewrite length_Str_firstn.
      intros n0 H. assert (Hn0 := Hf n0). epose proof lnth_firstn as H'.
      edestruct H' as [(_&H'')|(?&?)]; [rewrite H''|lia]. clear H'.
      rewrite List.nth_error_firstn by lia.
      assert (Htrn: forall m q, Str_nth_tl m (trn q) = trn (m + q)).
      { intros m. induction m.
        - reflexivity.
        - intros. simpl. rewrite IHm. f_equal. lia. }
      replace (Str_nth n0 (trn O)) with (Str_nth O (Str_nth_tl n0 (trn O))).
      2: { rewrite Str_nth_plus. reflexivity. }
      rewrite Htrn. simpl.
      specialize (Htrn n0 O).
      pose proof trace_longer_trans as tgl'. specialize tgl' with (1 := tgl) (2 := Hs).
      replace (n0 + 0) with n0 in * by lia.
      assert (Hle: f n <= f n0 \/ f n0 <= f n) by lia.
      remember (Str_nth (f n) _). cbv [Str_nth]. simpl. subst.
      destruct Hle as [Hle|Hle]; specialize tgl' with (1 := Hle); destruct tgl' as [tr' tgl']; rewrite tgl'.
      + destruct (nth_error (trace (Str_nth (f n) s)) n0) eqn:E.
        -- eapply lnth_app_r in E. rewrite E. reflexivity.
        -- exfalso. apply nth_error_None in E. lia.
      + destruct (nth_error (trace (Str_nth (f n0) s)) n0) eqn:E.
        -- eapply lnth_app_r in E. rewrite E. reflexivity.
        -- exfalso. apply nth_error_None in E. lia. 
    - intros H u. simpl. intros s Hs. specialize (H _ Hs). cbv [OK] in H.
      destruct H as [(?&?)|H]; [eexists; left; eassumption|].
      destruct H as (tr&Htr). cbv [has_inf_trace] in Htr. specialize (Htr (S u)).
      destruct Htr as [m Htr]. exists m.
      eassert (forall x y, x = y -> length x = length y) as H' by (intros; subst; reflexivity).
      apply H' in Htr. rewrite length_Str_firstn, length_firstn in Htr. lia.
  Qed.

  Lemma sinterp_to_aep sp sf :
    excluded_middle ->
    FunctionalChoice_on nat nat ->
    trace_gets_longer sp ->
    interp_aep (AEP_and AEP_is_OK (AEP_A _ _ (fun tgt => (aep_of tgt (lf_of _ ev sf))))) sp <->
      (forall ex, sp ex ->
             (exists n, post (Str_nth n ex)) \/
               exists tr, has_inf_trace ex tr /\ sinterp _ sf tr).
  Proof.
    intros em choice tgl. pose proof sinterp_to_aep' as H.
    specialize H with (1 := em) (2 := tgl).
    rewrite AEP_and_works by assumption. rewrite AEP_is_OK_works by assumption.
    split.
    - intros (?&?). intros. apply H; auto.
    - intros. assert (forall s, sp s -> OK s).
      { intros s Hs. specialize H0 with (1 := Hs). cbv [OK].
        destruct H0 as [H0|H0]; [left; assumption|right].
        destruct H0 as (?&?&?). eauto. }
    rewrite H; auto.
  Qed.

  Context (might_step : State -> State -> Prop).
  Notation step := (step State might_step).
  Notation step' := (step' _ State step).

  Lemma sinterp_to_omni_aep s P sf :
    excluded_middle ->
    FunctionalChoice_on nat nat ->
    FunctionalChoice_on State State ->

    (forall t, P t <-> sinterp _ sf t) ->
    (forall s1 s2, might_step s1 s2 -> exists tr', trace s2 = (trace s1 ++ tr')%list) ->
    runsTo step' (s, (AEP_and AEP_is_OK (AEP_A _ _ (fun tgt => (aep_of tgt (lf_of _ ev sf))))))
      (fun '(s', aep') =>
         match aep' with
         | (AEP_A _ _ _) | (AEP_E _ _ _) => False
         | (AEP_P _ P) => P s'
         end) <->
      (forall ex, possible _ might_step ex /\ Str_nth O ex = s ->
             (exists n, post (Str_nth n ex)) \/
               exists tr, has_inf_trace ex tr /\ P tr).
  Proof.
    intros em choice1 choice3 Hd tgl.
    pose proof sinterp_to_aep as H.
    specialize H with (1 := em) (2 := choice1).
    specialize (H (fun str : Stream State => possible State might_step str /\ Str_nth 0 str = s) sf).
    eassert _ as blah. 2: specialize (H blah); clear blah.
    { cbv [trace_gets_longer]. intros ? (?&?) n.
      specialize (tgl (Str_nth n s0) (Str_nth (S n) s0)).
      eapply possible_nth in H0. specialize tgl with (1 := H0). destruct tgl as [tr' tgl].
      exists tr'. assumption. }
    rewrite step'_iff_step.
    rewrite runsTo_iff_trace_pred' by assumption.
    rewrite H. split; intuition auto.
    - specialize (H2 ex ltac:(auto)). destruct H2 as [?|(?&?&?)]; auto. right.
      eexists. rewrite Hd. eauto.
    - specialize (H0 ex ltac:(auto)). destruct H0 as [?|(?&?&?)]; auto. right.
      eexists. rewrite <- Hd. eauto.
  Qed.
End OK_execution.

Axiom em: excluded_middle.
Axiom fun_choice: forall T1 T2, FunctionalChoice_on T1 T2.

Lemma sinterp_to_omni_aep_pretty (State Event : Type) (trace : State -> list Event) (P : Stream Event -> Prop) (post : State -> Prop) (ev : Event) :
  definable _ P ->
  exists aep,
  forall (might_step : State -> State -> Prop) (s : State),

    (forall s1 s2,
        might_step s1 s2 -> exists tr', trace s2 = (trace s1 ++ tr')%list) ->

    runsTo (step' _ _ (step _ might_step)) (s, aep)
      (fun '(s', aep') =>
         match aep' with
         | AEP_A _ _ _ | AEP_E _ _ _ => False
         | AEP_P _ P0 => P0 s'
         end) <->
      (forall ex : Stream State,
          possible _ might_step ex /\ Str_nth 0 ex = s ->
          (exists n, post (Str_nth n ex)) \/
            (exists tr : Stream Event, has_inf_trace _ _ trace ex tr /\ P tr)).
Proof.
  intros Hd. apply definable_characterization in Hd. destruct Hd as (?&Hd).
  eassert (forall t, _).
  { intros t. specialize (Hd t). rewrite sformula_of_works in Hd by (exact em). exact Hd. }
  clear Hd.
  eexists. intros. apply sinterp_to_omni_aep; auto using em, fun_choice.
  Unshelve. exact ev.
Qed.
Print Assumptions sinterp_to_omni_aep_pretty.
