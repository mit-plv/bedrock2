Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Require Export coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.Solver.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require Export coqutil.Decidable.
Require Export compiler.util.Tactics.
Require Export lib.fiat_crypto_tactics.UniquePose.


Lemma nth_error_nth: forall {T: Type} (l: list T) (e d: T) (i: nat),
  nth_error l i = Some e ->
  nth i l d = e.
Proof.
  intros T l. induction l; intros.
  - destruct i; simpl in H; discriminate.
  - destruct i; simpl in H; inversion H; subst.
    + reflexivity.
    + simpl. auto.
Qed.

Require Import coqutil.Datatypes.PropSet.
(* TODO move to PropSet *)
Definition set(A: Type) := A -> Prop.
Definition of_list{A: Type}(l: list A): set A := fun a => List.In a l.


Section WithMap.
  Context {K V} {M: map.map K V} {Ok: map.ok M} {Keq: DecidableEq K}.

  Lemma putmany_of_list_sameLength : forall bs vs st st',
      map.putmany_of_list bs vs st = Some st' ->
      length bs = length vs.
  Proof.
    induction bs, vs; cbn; try discriminate; trivial; [].
    intros; destruct (map.putmany_of_list bs vs st) eqn:?; eauto using f_equal.
  Qed.

  Lemma sameLength_putmany_of_list : forall bs vs st,
      length bs = length vs ->
      exists st', map.putmany_of_list bs vs st = Some st'.
  Proof.
    induction bs, vs; cbn; try discriminate; intros; eauto.
  Qed.

  Lemma only_differ_putmany : forall (bs : list K) (vs : list V) st st',
      map.putmany_of_list bs vs st = Some st' ->
      map.only_differ st (of_list bs) st'.
  Proof.
    induction bs, vs; cbn; try discriminate.
    - inversion 1; subst. cbv; eauto.
    - intros ? ? H x.
      simpl.
      destruct (map.putmany_of_list bs vs st) eqn:Heqo.
      + specialize IHbs with (1 := H). specialize (IHbs x).
        destruct IHbs as [IHbs | IHbs]; auto.
        rewrite (map.get_put_dec (key_eq_dec := Keq)) in IHbs.
        destruct (dec (a = x)); auto.
      + apply putmany_of_list_sameLength in H.
        apply (sameLength_putmany_of_list _ _ st) in H.
        destruct H. rewrite H in Heqo. discriminate.
  Qed.

(*
  Context {Kset: SetFunctions K}.
  Context {K_eq_dec: DecidableEq K}.

  Lemma putmany_extends_exists: forall (ks: list K) (vs: list V) m1 m1' m2,
      putmany ks vs m1 = Some m1' ->
      extends m2 m1 ->
      exists m2', putmany ks vs m2 = Some m2' /\ extends m2' m1'.
  Proof.
    induction ks; intros.
    - destruct vs; simpl in H; [|discriminate].
      inversion H. subst m1'. exists m2. simpl. auto.
    - simpl in *. repeat (destruct_one_match_hyp; try discriminate).
      inversion H. subst m1'. clear H.
      specialize IHks with (1 := E) (2 := H0).
      destruct IHks as (m2' & IH1 & IH2).
      rewrite IH1.
      eexists; split; [reflexivity|].
      map_solver K V.
  Qed.

  Lemma putmany_extends: forall (ks: list K) (vs: list V) m1 m1' m2 m2',
      putmany ks vs m1 = Some m1' ->
      putmany ks vs m2 = Some m2' ->
      extends m2 m1 ->
      extends m2' m1'.
  Proof.
    induction ks; intros.
    - destruct vs; simpl in *; [|discriminate].
      inversion H. inversion H0. subst. assumption.
    - simpl in *. repeat (destruct_one_match_hyp; try discriminate).
      inversion H. subst m1'. clear H.
      inversion H0. subst m2'. clear H0.
      specialize IHks with (1 := E0) (2 := E) (3 := H1).
      map_solver K V.
  Qed.
*)
End WithMap.
