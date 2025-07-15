Require Import riscv.Utility.runsToNonDet.
Require Import coqutil.sanity coqutil.Byte.
Require Import bedrock2.MetricLeakageSemantics.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.

Section step.
  Context (State : Type) (step : State -> (State -> Prop) -> Prop).
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.

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
  
  CoInductive stream (T : Type) :=
  | scons (a : T) (rest : stream T).

  Fixpoint nth {T : Type} (n : nat) (s : stream T) : T :=
    match s, n with
    | scons _ a rest, S n' => nth n' rest
    | scons _ a rest, O => a
    end.
  
  CoInductive possible {T : Type} (step_ : T -> T -> Prop) : stream T -> Prop :=
  | poss a b rest : step_ b a ->
                    possible step_ (scons _ b rest) ->
                    possible step_ (scons _ a (scons _ b rest)).

  Fixpoint trace_pred_of {T : Type} aep : _ -> stream T -> Prop :=
    match aep with
    | AEP_A aep' => fun post => fun str => forall x, trace_pred_of (aep' x) post str
    | AEP_E aep' => fun post => fun str => exists x, trace_pred_of (aep' x) post str
    | AEP_P P => fun post => fun str => exists n, post P (nth n str)
    end.

  Require Import Coq.Logic.ChoiceFacts.
  Require Import Coq.Logic.ClassicalFacts.
  Lemma naen (A : Type) (P : A -> Prop) :
    excluded_middle ->
    ~(forall y, P y) ->
    exists y, ~P y.
  Proof.
    intros em. clear -em. cbv [excluded_middle]. intros H. assert (H1 := em (exists y, ~P y)).
    destruct H1 as [H1|H1].
    - assumption.
    - exfalso. apply H. clear H. intros y. assert (H2 := em (P y)).
      destruct H2 as [H2|H2].
      + assumption.
      + exfalso. apply H1. exists y. assumption.
  Qed.

  Lemma chains_finite_implies_Acc' (A : Type) (R : A -> A -> Prop) x str :
    nth O str = x ->
    possible R str ->
    ~ Acc R x.
  Proof.
    intros H1 H2 H3. revert str H1 H2. induction H3. intros str H1 H2. inversion H2.
    subst. simpl in *. specialize H0 with (3 := H4). specialize H0 with (2 := eq_refl).
    apply H0. apply H3.
  Qed.

  Lemma notnot :
    excluded_middle ->
    forall P,
    ~~P ->
    P.
  Proof. intros em P nnP. specialize (em P). tauto. Qed.

  Lemma chains_finite_implies_Acc (A : Type) (R : A -> A -> Prop) x :
    excluded_middle ->
    ~ (forall str, possible R str -> nth O str = x -> False) ->
    Acc R x.
  Proof.
    intros em H. apply (notnot em). intros H'. apply H. intros. clear H. Search excluded_middle. Abort. 
  (* Lemma runsTo_iff_trace_pred {T : Type} (step_ : T -> _ -> Prop) s P : *)
  (*   runsTo step_ s P <-> (forall str, possible step_ str -> *)
  (*                              nth O str = s -> *)
  (*                              exists n, P (nth n str)). *)
  (* Proof. *)
  (*   split; intros H. *)
  (*   - induction H. *)
  (*     + intros. destruct str; inversion H1. subst. exists O. simpl. assumption. *)
  (*     + intros. inversion H2. subst.  *)
  (*       specialize H4 with (1 := H). specialize H0 with (1 := H4). *)
  (*       specialize H1 with (1 := H4). specialize H1 with (1 := H5). *)
  (*       specialize (H1 eq_refl). destruct H1 as [n H1]. exists (S n). simpl. assumption. *)
  (*   -  *)
        
  (* Lemma step'_iff_trace_pred s aep post : *)
  (*   runsTo step' (s, aep) *)
  (*     (fun '(s', aep') => *)
  (*        match aep' with *)
  (*        | AEP_P P => post P s' *)
  (*        | _ => False *)
  (*        end) <-> *)
  (*     (forall str, possible str -> trace_pred_of aep post str). *)
  (* Proof. *)
  (*   split; intros H. *)
  (*   - intros str Hstr. *)
End step.
