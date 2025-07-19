Require Import riscv.Utility.runsToNonDet.
Require Import coqutil.sanity coqutil.Byte.
Require Import bedrock2.MetricLeakageSemantics.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import Coq.Logic.ChoiceFacts.
Require Import Coq.Logic.ClassicalFacts.

Section step.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context (State : Type) (step : State -> (State -> Prop) -> Prop).

  Definition State' : Type := State * AEP.
  Inductive step' : State' -> (State' -> Prop) -> Prop :=
  | step_usual s aep mid P : step s mid ->
                          (forall s', mid s' -> P (s', aep)) -> 
                          step' (s, aep) P
  | step_A s aep P : (forall x, P (s, aep x)) ->
                     step' (s, AEP_A aep) P
  | step_E s aep P : (exists x, P (s, aep x)) ->
                     step' (s, AEP_E aep) P.

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
    | AEP_A aep' => fun post => fun s => forall n, runsTo step s (post_of (aep' n) post)
    | AEP_E aep' => fun post => fun s => exists n, runsTo step s (post_of (aep' n) post)
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

  Lemma inp_works inp aep s post :
    compat aep inp ->
    (forall aep',
        goes_to aep inp aep' ->
        runsTo step' (s, aep') post) ->
    runsTo step' (s, aep) post.
  Proof.
    intros Hcom Haep. revert aep Hcom Haep. induction inp; intros aep Hcom Haep;
      inversion Hcom; subst.
    - apply Haep. constructor.
    - apply runsToStep_cps. apply step_E. exists n. eapply IHinp; try eassumption. intros. apply Haep. constructor.
      assumption.
    - apply runsToStep_cps. apply step_A. intros x. eapply H; eauto. intros. apply Haep. econstructor.
      eassumption.
  Qed.
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

  Lemma possible_weaken {T : Type} str (R1 : T -> T -> Prop) :
    possible T R1 str ->
    forall R2,
    (forall x y, R1 x y -> R2 x y) ->
    possible T R2 str.
  Proof.
    intros H' R2 H. revert str H'. cofix Hstr. intros str H'. inversion H'. subst.
    clear H'. constructor. 1: auto. apply Hstr. assumption.
  Qed.

  Lemma possible_nth {T : Type} str (R : T -> T -> Prop) n :
    possible T R str ->
    R (nth n str) (nth (S n) str).
  Proof.
    revert str. induction n.
    - intros str H. inversion H. subst. simpl. assumption.
    - intros str H. inversion H. subst. simpl. apply IHn. assumption.
  Qed.

  Lemma possible_skipn {T : Type} str (R : T -> T -> Prop) n :
    possible T R str ->
    possible T R (skipn n str).
  Proof.
    revert str. induction n.
    - intros str H. inversion H. subst. simpl. assumption.
    - intros str H. inversion H. subst. simpl. apply IHn. assumption.
  Qed.

  
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

Section post_of_surj.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context (Event : Type) (State := nat : Type) (trace : State -> list Event).
  Context (might_step : State -> State -> Prop).
  Context (trace_gets_longer : forall x y, might_step x y -> exists t, trace y = List.app (trace x) t).
  Notation step := (step _ might_step).

  (*a formula stating a predicate about event streams*)
  Inductive sformula :=
  (*because I don't want to deal with dependent types, quantifiers can only bind nats*)
  | sforall : (nat -> sformula) -> sformula
  | sexists : (nat -> sformula) -> sformula
  (*assertion about the nth element of the stream*)
  | sasstn (n : nat) : (State -> sformula) -> sformula
  (*base case: a prop*)
  | spropn : Prop -> sformula.

  Fixpoint sinterp (f : sformula) (t : stream State) : Prop :=
    match f with
    | sforall f' => forall n, sinterp (f' n) t
    | sexists f' => exists n, sinterp (f' n) t
    | sasstn n f' => sinterp (f' (nth n t)) t
    | spropn P => P
    end.
  Axiom definable : (stream State -> Prop) -> Prop.
  Axiom definable_characterization :
    forall P, definable P ->
         exists f, forall t, P t <-> sinterp f t.

  (*about lists*)
  Inductive lformula :=
  | lforall : (nat -> lformula) -> lformula
  | lexists : (nat -> lformula) -> lformula
  | lpropn : (list State -> Prop) -> lformula.

  Fixpoint linterp (f : lformula) (t : stream State) : Prop :=
    match f with
    | lforall f' => forall n, linterp (f' n) t
    | lexists f' => exists n, linterp (f' n) t
    | lpropn P => exists n, forall n0, n <= n0 -> P (firstn n0 t)
    end.

  Fixpoint lnth {T : Type} (n : nat) (l : list T) : option T :=
    match n, l with
    | S n', cons a l' => lnth n' l'
    | O, cons a l' => Some a
    | _, _ => None
    end.

  Require Import Lia.
  Lemma lnth_firstn {T : Type} n n1 (t : stream T) :
    n < n1 /\ lnth n (firstn n1 t) = Some (nth n t) \/ n >= n1 /\ lnth n (firstn n1 t) = None.
  Proof.
    clear. revert n t. induction n1; intros.
    - right. split; [lia|]. simpl. destruct t. destruct n; reflexivity.
    - simpl. destruct t. destruct n; simpl.
      + left. split; [lia|]. reflexivity.
      + specialize (IHn1 n t). destruct IHn1 as [(H1&H2)|(H1&H2)]; [left|right]; split; try lia;  assumption.
  Qed.

  Lemma assert_nth s n lf :
    excluded_middle ->
    FunctionalChoice_on nat lformula ->
    exists lf', forall t, linterp lf' t <-> (linterp lf t /\ nth n t = s).
  Proof.
    clear. intros em choice. induction lf.
    - eassert (H': exists l', _).
      { apply choice. intros x. specialize (H x). destruct H as [lf' H]. exists lf'. exact H. }
      clear H. destruct H' as [l' H']. exists (lforall l'). intros. simpl. split.
      + intros. (*hmm here we use that quantfiers over nats are not vacuous.  relevant?*)
        assert (HO := H O). rewrite H' in HO. destruct HO as [_ HO].
        split; [|assumption]. intros n0. specialize (H n0). rewrite H' in H.
        destruct H. assumption.
      + intros H0 n0. rewrite H'. destruct H0. auto.
    - eassert (H': exists l', _).
      { apply choice. intros x. specialize (H x). destruct H as [lf' H]. exists lf'. exact H. }
      clear H. destruct H' as [l' H']. exists (lexists l'). intros. simpl. split.
      + intros [n0 Hn0]. rewrite H' in Hn0. intuition eauto.
      + intros ([n0 H0] & H1). eexists. rewrite H'. eauto.
    - exists (lpropn (fun l => P l /\ lnth n l = Some s)). intros t. simpl. split.
      + intros [n0 H]. assert (HO := H n0 ltac:(lia)). destruct HO as [_ HO].
        epose proof lnth_firstn as H'. edestruct H' as [(_&H'')|(_&H'')]; [rewrite H'' in HO|]; clear H'.
        -- inversion HO. subst. split; [|reflexivity]. exists n0. intros n1 Hn1.
           specialize (H _ Hn1). destruct H. assumption.
        -- congruence.
      + intros [(n0&Hn0) ?]. subst. exists (Nat.max (S n) n0). intros n1 Hn2.
        specialize (Hn0 n1 ltac:(lia)). split; [assumption|].
        epose proof lnth_firstn as H'. edestruct H' as [(_&H'')|H'']; [exact H''|].
        clear H'. destruct H''. lia.
  Qed.
  
  Lemma finite_prefixes_enough f :
    excluded_middle ->
    FunctionalChoice_on nat lformula ->
    exists lf, forall t, sinterp f t <-> linterp lf t.
  Proof.
    clear. intros em choice. induction f.
    - eassert (H': exists P, _).
      { apply choice. intros x. specialize (H x). destruct H as [P H]. exists P. exact H. }
      clear H. destruct H' as [P H']. exists (lforall P). intros t.
      split.
      + simpl. intros. apply H'. auto.
      + simpl. intros. apply H'. auto.
    - eassert (H': exists P, _).
      { apply choice. intros x. specialize (H x). destruct H as [P H]. exists P. exact H. }
      clear H. destruct H' as [P H']. exists (lexists P). intros t.
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
      clear H. destruct H0 as [f H]. exists (lexists f). intros. simpl. split.
      + intros H'. eexists. rewrite H. split; [eassumption|]. reflexivity.
      + intros [n0 H']. rewrite H in H'. destruct H' as [H' ?]. subst. assumption.
    - simpl. Print lformula. eexists (lpropn (fun _ => P)). simpl. intuition eauto.
      destruct H as [n H]. specialize (H n ltac:(lia)). assumption.
      Unshelve. exact O.
  Qed.

  Fixpoint aep_post_of (f : formula) : AEP :=
    match f with
    | forall_ f' => AEP_A (fun x => aep_post_of (f' x))
    | exists_ f' => AEP_E (fun x => aep_post_of (f' x))
    | asstn n f' => 

  Lemma post_of_surj :
  (* Lemma post_of_surjective P : *)
  (*   definable P -> *)
  (*   exists aep post, *)
  (*     (forall t, P t <-> exists n, post_of _ step aep post (prefix n t)). *)

End post_of_surj.

Section aep_omni_trad.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context (Event : Type) (State : Type) (trace : State -> list Event).
  Context (might_step : State -> State -> Prop).

  Notation step := (step _ might_step).
  Notation step' := (step' _ step).
  
  Fixpoint simple_post_of aep (post : _ -> State -> Prop) (str : stream State) :=
    match aep with
    | AEP_A aep' =>
        forall str,
          starts_with str s ->
          
        exists n, forall x,
        forall str',
          prefix n str = prefix n str' ->
          simple_post_of (aep' x) post str'
    | AEP_E aep' =>
        exists n, exists x,
        forall str',
          prefix n str = prefix n str' ->
          simple_post_of (aep' x) post str
    | AEP_P X => exists n, post X (nth n str)
    end.

  (* Lemma simple_post_of_skipn aep post str n : *)
  (*   simple_post_of aep post (skipn n str) -> *)
  (*   simple_post_of aep post str. *)
  (* Proof. *)
  (*   intros H. induction aep; simpl in *; auto. *)
  (*   - destruct H as [n0 H]. eauto. *)
  (*   - destruct H as [n0 H]. rewrite nth_skipn in H. eauto. *)
  (* Qed. *)

  Lemma post_of_iff_trace_pred aep post s :
    excluded_middle ->
    FunctionalChoice_on State State ->
    (forall str, possible _ might_step str ->
            nth O str = s ->
            (exists n, post_of _ step aep post (nth n str))) <->
      (forall str, possible _ might_step str ->
              nth O str = s ->
              simple_post_of aep post str).
  Proof.
    intros em choice. split.
    - revert s post. induction aep; intros s post H'; cbn [post_of simple_post_of] in *.
      + intros str Hstr HO. subst. specialize H' with (1 := Hstr) (2 := eq_refl).
        destruct H' as [n H']. exists n. intros x str' Hstr'. subst. eapply H. intros. subst. specialize H' with (1 := H0) (2 := eq_refl).
        destruct H' as (n0 & H'). specialize (H' n).
        rewrite runsTo_iff_trace_pred in H' by assumption.
        specialize (H' (skipn n0 str) ltac:(auto using possible_skipn)).
        rewrite nth_skipn, PeanoNat.Nat.add_0_r in H'. specialize (H' eq_refl).
        destruct H' as (n1 & H'). rewrite nth_skipn in H'. eauto.
      + Check runsTo_iff_trace_pred. Print simple_post_of.
        apply H'. ; auto.
        specialize H' with (1 := Hstr) (2 := eq_refl). destruct H' as [n0 Hn0].
        cbn [post_of] in Hn0. specialize (Hn0 n).
        rewrite runsTo_iff_trace_pred in Hn0 by assumption.
        specialize H with (1 := Hn0). clear Hn0.
        eapply simple_post_of_skipn. eapply H.
        2: rewrite nth_skipn, PeanoNat.Nat.add_0_r; reflexivity.
        auto using possible_skipn.
      + specialize H' with (1 := Hstr) (2 := eq_refl). destruct H' as (n & n0 & H').
        rewrite runsTo_iff_trace_pred in H' by assumption.
        specialize H with (1 := H'). clear H'. exists n0.
        eapply simple_post_of_skipn. eapply H.
        2: rewrite nth_skipn, PeanoNat.Nat.add_0_r; reflexivity.
        auto using possible_skipn.
      + auto.
    - revert s post. induction aep; intros s post H' str Hstr HO; cbn [post_of simple_post_of] in *; subst.
      + exists O. intros n. rewrite runsTo_iff_trace_pred by assumption. intros.
        eapply H. 3: eassumption. 2: assumption. intros. apply H'; assumption.
      + exists O. assert (H'' := H'). specialize (H' _ ltac:(eassumption) ltac:(reflexivity)).
        destruct H' as [n H']. exists n. rewrite runsTo_iff_trace_pred by assumption.
        apply H.
        
      
  Lemma blah s aep post :
    excluded_middle ->
    FunctionalChoice_on State State ->
    runsTo step' (s, aep)
      (fun '(s', aep') =>
         match aep' with
         | AEP_P P => post P s'
         | _ => False
         end) <->
      True.
  Proof.
    intros em choice.
    rewrite step'_iff_step. rewrite runsTo_iff_trace_pred; [|assumption|assumption].
    w
    reflexivity.
  Qed.

  Print post_of. 
    
  Lemma step'_iff_trace_pred s aep post :
    runsTo step' (s, aep)
      (fun '(s', aep') =>
         match aep' with
         | AEP_P P => post P s'
         | _ => False
         end) <->
      (forall str, possible str -> simple_post_of aep post str).
  Proof.
    split; intros H.
    - intros str Hstr.

  
