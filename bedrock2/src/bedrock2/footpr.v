Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.destr coqutil.Decidable.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation.
Require Import bedrock2.Map.SeparationLogic.

Section Footprint.
  Context {key value} {map : map.map key value} {ok : map.ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

  (* if P allows different footprints, we return the intersection of all possible footprints *)
  Definition footprint_underapprox(P: map -> Prop): key -> Prop :=
    fun a => forall m, P m -> exists v, map.get m a = Some v.

  (* if P allows different footprints, we return the union of all possible footprints *)
  Definition footprint_overapprox(P: map -> Prop): key -> Prop :=
    fun a => exists m v, P m /\ map.get m a = Some v.

  Definition unique_footprint(P: map -> Prop): Prop :=
    forall m1 m2, P m1 -> P m2 -> map.same_domain m1 m2.

  Definition non_contrad(P: map -> Prop): Prop := exists m, P m.

  Lemma footprint_underapprox_subset_overapprox: forall (P: map -> Prop),
      non_contrad P ->
      subset (footprint_underapprox P) (footprint_overapprox P).
  Proof.
    unfold non_contrad, subset, footprint_underapprox, footprint_overapprox,
           elem_of.
    intros.
    destruct H as [m Pm].
    firstorder idtac.
  Qed.

  Lemma footprint_overapprox_subset_underapprox: forall (P: map -> Prop),
      unique_footprint P ->
      subset (footprint_overapprox P) (footprint_underapprox P).
  Proof.
    unfold unique_footprint, subset, footprint_underapprox, footprint_overapprox,
           elem_of, map.same_domain, map.sub_domain.
    intros.
    destruct H0 as [m' [v [Pm G]]].
    specialize (H _ _ H1 Pm).
    destruct H as [S1 S2].
    eapply S2. eassumption.
  Qed.

  Lemma footprint_over_equals_underapprox: forall (P: map -> Prop),
      unique_footprint P ->
      non_contrad P ->
      footprint_underapprox P = footprint_overapprox P.
  Proof.
    intros.
    apply iff1ToEq.
    split.
    - eapply footprint_underapprox_subset_overapprox. assumption.
    - eapply footprint_overapprox_subset_underapprox. assumption.
  Qed.

  (* Given that under normal circumstances, footprint_underapprox is the same as
     footprint_overapprox (see lemma above), we choose to use footprint_underapprox,
     because it requires no preconditions for footpr_sep_subset_l/r. *)

  Definition footpr := footprint_underapprox.

  Lemma in_footpr_sep_l: forall (x: key) (P Q: map -> Prop),
      elem_of x (footpr P) ->
      elem_of x (footpr (sep P Q)).
  Proof.
    unfold footpr, footprint_underapprox, sep, elem_of.
    intros.
    destruct H0 as [mp [mq [Sp [Pmp Qmq]]]].
    specialize (H mp Pmp).
    destruct H as [v G].
    unfold map.split, map.disjoint in Sp. destruct Sp as [? D]. subst.
    exists v.
    rewrite map.get_putmany_dec.
    destr (map.get mq x).
    - exfalso. eauto.
    - assumption.
  Qed.

  Lemma footpr_sep_subset_l: forall (P Q: map -> Prop) (A: key -> Prop),
      subset (footpr (sep P Q)) A -> subset (footpr P) A.
  Proof.
    unfold subset. eauto using in_footpr_sep_l.
  Qed.

  Lemma in_footpr_sep_r: forall (x: key) (P Q: map -> Prop),
      elem_of x (footpr Q) ->
      elem_of x (footpr (sep P Q)).
  Proof.
    unfold footpr, footprint_underapprox, sep, elem_of.
    intros.
    destruct H0 as [mp [mq [Sp [Pmp Qmq]]]].
    specialize (H mq Qmq).
    destruct H as [v G].
    unfold map.split, map.disjoint in Sp. destruct Sp as [? D]. subst.
    exists v.
    rewrite map.get_putmany_dec.
    destr (map.get mq x).
    - assumption.
    - discriminate.
  Qed.

  Lemma footpr_sep_subset_r: forall (P Q: map -> Prop) (A: key -> Prop),
      subset (footpr (sep P Q)) A -> subset (footpr Q) A.
  Proof.
    unfold subset. eauto using in_footpr_sep_r.
  Qed.

  Lemma rearrange_footpr_subset(P Q: map -> Prop) (A: key -> Prop)
      (H1: subset (footpr P) A)
      (H2: iff1 P Q):
    subset (footpr Q) A.
  Proof.
    intros. apply iff1ToEq in H2. subst P. assumption.
  Qed.

  Lemma shrink_footpr_subset(P Q R: map -> Prop) (A: key -> Prop)
      (H1: subset (footpr Q) A)
      (H2: iff1 Q (sep P R)):
      subset (footpr P) A.
  Proof.
    intros.
    apply iff1ToEq in H2. subst Q.
    eapply footpr_sep_subset_l. eassumption.
  Qed.

  Lemma same_domain_split: forall (m1 m2 m1l m1r m2l m2r : map),
      map.same_domain m1l m2l ->
      map.same_domain m1r m2r ->
      map.split m1 m1l m1r ->
      map.split m2 m2l m2r ->
      map.same_domain m1 m2.
  Proof.
    unfold map.same_domain, map.sub_domain, map.split.
    intros. destruct H, H0, H1, H2. subst.
    split.
    - intros.
      rewrite map.get_putmany_dec in H1.
      destr (map.get m1r k).
      + inversion H1. subst v1.
        specialize (H0 _ _ E). destruct H0 as [v2 G].
        exists v2. apply map.get_putmany_right. assumption.
      + specialize (H _ _ H1). destruct H as [v2 G].
        exists v2. rewrite map.get_putmany_left. 1: assumption.
        destr (map.get m2r k); [exfalso | reflexivity].
        specialize (H4 _ _ E0). destruct H4 as [v2' G'].
        congruence.
    - intros.
      rewrite map.get_putmany_dec in H1.
      destr (map.get m2r k).
      + inversion H1. subst v1.
        specialize (H4 _ _ E). destruct H4 as [v2 G].
        exists v2. apply map.get_putmany_right. assumption.
      + specialize (H3 _ _ H1). destruct H3 as [v2 G].
        exists v2. rewrite map.get_putmany_left. 1: assumption.
        destr (map.get m1r k); [exfalso | reflexivity].
        specialize (H0 _ _ E0). destruct H0 as [v2' G'].
        congruence.
  Qed.

  Lemma unique_footprint_sep(P Q: map -> Prop):
    unique_footprint P ->
    unique_footprint Q ->
    unique_footprint (sep P Q).
  Proof.
    unfold unique_footprint. intros.
    unfold sep in *.
    destruct H1 as [m1P [m1Q [? [? ?] ] ] ].
    destruct H2 as [m2P [m2Q [? [? ?] ] ] ].
    eapply same_domain_split; cycle 2; eauto.
  Qed.

End Footprint.
