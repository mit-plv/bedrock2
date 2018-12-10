Require Export Coq.omega.Omega.
Require Export Coq.Lists.List.
Require Export riscv.util.Word.
Require Export compiler.Decidable.
Require Export compiler.util.Tactics.
Require Export compiler.util.Set.
Require Export compiler.util.Map.
Require Export lib.fiat_crypto_tactics.UniquePose.

Global Instance dec_eq_word : forall sz, DecidableEq (word sz) := @weq_dec.

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

Fixpoint option_all {A} (l : list (option A)) {struct l} : option (list A) :=
  match l with
  | nil => Some nil
  | (Some x)::l =>
    match option_all l with
    | Some l' => Some (x::l')
    | _ => None end
  | _ => None
  end.

Section WithMap.
  Context {K V} {TMap: MapFunctions K V}.

  Fixpoint putmany (keys : list K) (values : list V) (init : map K V) {struct keys} : option (map K V) :=
    match keys, values with
    | nil, nil => Some init
    | b::binders, v::values => match putmany binders values init with
                               | Some t => Some (put t b v)
                               | None => None
                               end
    | _, _ => None
    end.

  Lemma putmany_sameLength : forall bs vs st st' (H:putmany bs vs st = Some st'),
      length bs = length vs.
  Proof.
    induction bs, vs; cbn; try discriminate; trivial; [].
    intros; destruct (putmany bs vs st) eqn:?; [eauto using f_equal|discriminate].
  Qed.

  Context {Kset: SetFunctions K}.
  Context {K_eq_dec: DecidableEq K}.

  Lemma only_differ_putmany : forall (bs : list K) (vs : list V) st st'
                                     (H : putmany bs vs st = Some st'),
      only_differ st (fold_right union empty_set (List.map singleton_set bs)) st'.
  Proof.
    induction bs, vs; cbn; try discriminate.
    { inversion 1; subst. cbv; eauto. }
    { intros ? ? H; destruct (putmany bs vs st) eqn:Heqo; [|discriminate].
      inversion H; subst.
      specialize (IHbs _ _ _ Heqo).
      intros x; destruct (IHbs x);
        autorewrite with rew_set_op_specs in *; rewrite ?get_put;
          destruct (dec (a=x)); eauto. }
  Qed.

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

End WithMap.
