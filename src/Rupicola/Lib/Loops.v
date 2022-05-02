Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.
Require Import Rupicola.Lib.Invariants.
Require Import Rupicola.Lib.Gensym.

Open Scope list.

Section Subseq.
  Context {T: Type}.
  Implicit Type l: list T.

  Definition subseq l l' :=
    forall x, In x l -> In x l'.

  Lemma subseq_refl {l} :
    subseq l l.
  Proof. firstorder. Qed.

  Lemma subseq_nil {l} :
    subseq [] l.
  Proof. firstorder. Qed.

  Lemma subseq_singleton x l :
    In x l -> subseq [x] l.
  Proof. firstorder (subst; eauto). Qed.

  Lemma subseq_cons_l x l l':
    subseq (x :: l) l' -> subseq l l'.
  Proof. firstorder. Qed.

  Lemma subseq_cons_r x l l':
    subseq l l' -> subseq l (x :: l').
  Proof. firstorder. Qed.

  Lemma subseq_app_r1 {l l'}:
    subseq l (l ++ l').
  Proof. firstorder eauto using in_or_app. Qed.

  Lemma subseq_app_r2 {l l'}:
    subseq l' (l ++ l').
  Proof. firstorder eauto using in_or_app. Qed.

  Lemma subseq_app_l1 {l l' l''}:
    subseq (l ++ l') l'' -> subseq l l''.
  Proof. firstorder eauto using in_or_app. Qed.

  Lemma subseq_app_l2 {l l' l''}:
    subseq (l ++ l') l'' -> subseq l' l''.
  Proof. firstorder eauto using in_or_app. Qed.
End Subseq.

Create HintDb loops discriminated.
#[local] Hint Resolve subseq_singleton: loops.
#[local] Hint Resolve subseq_cons_l subseq_cons_r: loops.
#[local] Hint Resolve subseq_app_l1 subseq_app_l2: loops.
#[local] Hint Resolve subseq_app_r1 subseq_app_r2: loops.
#[local] Hint Resolve in_app_or in_or_app in_eq: loops.

Notation body_ext_irrel b b' :=
  (forall acc idx pr pr', b acc idx pr = b' acc idx pr').

Notation body_ext b b' :=
  (forall acc idx pr, b acc idx pr = b' acc idx pr).

Section Folds.
  Context {A T: Type}.
  Context (xs: list T).

  Section Dep.
    Context (f: forall (acc: A) (x: T), List.In x xs -> A).
    Context (stop: A -> bool).

    Lemma foldl_dep'0 {x0 suffix}:
      (forall x, In x (x0 :: suffix) -> In x xs) -> In x0 xs.
    Proof. simpl; eauto. Defined.

    Lemma foldl_dep'1 {idx tl P}:
      (forall x : T, In x (idx :: tl) -> P x) ->
      (forall x : T, In x tl -> P x).
    Proof. simpl; eauto. Defined.

    Fixpoint foldl_dep' xxs : subseq xxs xs -> A -> A :=
      match xxs with
      | [] => fun _ a => a
      | x :: xxs => fun pr a =>
                    if stop a then a
                    else let a := f a x (foldl_dep'0 pr) in
                         foldl_dep' xxs (foldl_dep'1 pr) a
      end.
  End Dep.

  Context (f: forall (acc: A) (x: T), A).
  Context (stop: A -> bool).

  Fixpoint foldl xs (a: A) : A :=
    match xs with
    | [] => a
    | x :: xs =>
        if stop a then a
        else foldl xs (f a x)
    end.

  Lemma foldl_as_foldl_dep' :
    forall (xxs: list T) H (a0: A),
      foldl xxs a0 = foldl_dep' (fun a idx _ => f a idx) stop xxs H a0.
  Proof.
    induction xxs; simpl; intros; erewrite ?IHxxs; reflexivity.
  Qed.
End Folds.

Notation foldl_dep xs f stop a0 :=
  (foldl_dep' xs f stop xs subseq_refl a0).

Lemma foldl_as_foldl_dep {A T} f stop :
  forall (xs: list T) (a0: A),
    foldl f stop xs a0 = foldl_dep xs (fun a idx _ => f a idx) stop a0.
Proof. intros; apply foldl_as_foldl_dep'. Qed.

Section Props.
  Context {A T: Type}.

  Section Simple.
    Context (xs: list T).
    Context (f: forall (acc: A) (x: T), List.In x xs -> A).
    Context (stop: A -> bool).

    Lemma foldl_dep_stop xxs Hs a0:
      stop a0 = true -> foldl_dep' xs f stop xxs Hs a0 = a0.
    Proof. destruct xxs; simpl; intros h; try rewrite h; reflexivity. Qed.

    Lemma foldl_dep_exit xxs Hs a0:
      xxs = [] -> foldl_dep' xs f stop xxs Hs a0 = a0.
    Proof. intros; subst; reflexivity. Qed.
  End Simple.

  Implicit Type a: A.
  Implicit Type xs: list T.

  (* Membership proofs are not unique (there could be duplicates in the list),
     and it's a bit off that the spec of foldl allows it to pass the "wrong"
     proof along with a list element.  Switching to a unique equivalent would
     make it clear that the proof's structure is irrelevant (it doesn't
     necessarily encode the element's index), but it requires additional axioms.
     Alternatively, we could track indices and pass them around, and then the
     proof would just be `nth_error` since we'd again be giving the "wrong"
     proof *)

  Lemma foldl_dep_Proper:
    forall xs xs'
      f f' stop stop'
      xxs xxs' Hs Hs' a0 a0',
      xxs = xxs' -> a0 = a0' ->
      (forall a x h h', f a x h = f' a x h') ->
      (forall a, stop a = stop' a) ->
      foldl_dep' xs f stop xxs Hs a0 =
      foldl_dep' xs' f' stop' xxs' Hs' a0'.
  Proof.
    induction xxs; intros * ? ? Hb Hs; subst; simpl in *.
    - reflexivity.
    - rewrite Hs; destruct stop'; try reflexivity.
      apply IHxxs; f_equal; eauto.
  Qed.

  Hint Resolve foldl_dep_Proper : loops.

  Lemma foldl_dep_app:
    forall xs f stop xxs xxs' a0 Hsapp Hs Hs',
      (forall a x h h', f a x h = f a x h') ->
      foldl_dep' xs f stop (xxs ++ xxs') Hsapp a0 =
      foldl_dep' xs f stop xxs' Hs' (foldl_dep' xs f stop xxs Hs a0).
  Proof.
    induction xxs; cbn; intros.
    - eauto with loops.
    - destruct stop eqn:?.
      + rewrite foldl_dep_stop; eauto.
      + unshelve erewrite IHxxs; eauto with loops.
  Qed.

  Lemma foldl_dep_snoc:
    forall xs f stop x xxs a0 Hsapp Hs H,
      (forall a x h h', f a x h = f a x h') ->
      foldl_dep' xs f stop (xxs ++ [x]) Hsapp a0 =
      (let butlast := foldl_dep' xs f stop xxs Hs a0 in
       if stop butlast then butlast
       else f butlast x H).
  Proof.
    intros; unshelve erewrite foldl_dep_app; simpl; eauto with loops.
    destruct stop; eauto.
  Qed.

  Lemma foldl_dep_snoc_nstop:
    forall xs f stop x xxs a0 Hsapp Hs H,
      (forall a x h h', f a x h = f a x h') ->
      let butlast := foldl_dep' xs f stop xxs Hs a0 in
      stop butlast = false ->
      foldl_dep' xs f stop (xxs ++ [x]) Hsapp a0 =
      f butlast x H.
  Proof.
    intros; unshelve erewrite foldl_dep_snoc; eauto.
    subst butlast; simpl; destruct (stop _); congruence.
  Qed.

  Lemma foldl_dep_monotonic :
    forall xs f stop xxs' xxs a0 H Happ,
      (forall a x h h', f a x h = f a x h') ->
      stop (foldl_dep' xs f stop xxs H a0) = true ->
      foldl_dep' xs f stop (xxs ++ xxs') Happ a0 =
      foldl_dep' xs f stop xxs H a0.
  Proof.
    intros; unshelve erewrite foldl_dep_app; eauto with loops.
    eauto using foldl_dep_stop.
  Qed.

  Lemma foldl_dep_Proper_strong':
    forall xs xs'
      f f' stop stop'
      xxs xxs1 (Hs: subseq (xxs1 ++ xxs) xs) Hs0 Hs0' Hs1 a0,
      body_ext_irrel f f ->
      (forall xxs1 Hs1 x h h',
          let a := foldl_dep' xs f stop xxs1 Hs1 a0 in
          f a x h = f' a x h') ->
      (forall xxs1 Hs1,
          let a := foldl_dep' xs f stop xxs1 Hs1 a0 in
          stop a = stop' a) ->
      foldl_dep' xs f stop xxs Hs0
                 (foldl_dep' xs f stop xxs1 Hs1 a0) =
      foldl_dep' xs' f' stop' xxs Hs0'
                 (foldl_dep' xs f stop xxs1 Hs1 a0).
  Proof.
    induction xxs; intros * ????? Hf Hb Hs; subst; simpl in *.
    - reflexivity.
    - rewrite <- Hs; destruct stop eqn:?; try reflexivity.
      pose proof Hs0 as H.
      replace (xxs1 ++ a :: xxs) with ((xxs1 ++ [a]) ++ xxs) in H
        by (rewrite <- app_assoc; reflexivity).
      replace (f (foldl_dep' xs f stop xxs1 Hs2 a0) a (foldl_dep'0 xs Hs1))
        with (foldl_dep' xs f stop (xxs1 ++ [a]) (subseq_app_l1 H) a0).
      replace (f' (foldl_dep' xs f stop xxs1 Hs2 a0) a (foldl_dep'0 xs' Hs0'))
        with (foldl_dep' xs f stop (xxs1 ++ [a]) (subseq_app_l1 H) a0).
      apply IHxxs; f_equal; eauto.
      + unshelve erewrite foldl_dep_snoc_nstop; eauto with loops.
      + unshelve erewrite foldl_dep_snoc_nstop; eauto with loops.
  Qed.

  Lemma foldl_dep_Proper_strong:
    forall xs xs'
      f f' stop stop'
      xxs xxs' Hs Hs' a0 a0',
      xxs = xxs' -> a0 = a0' ->
      body_ext_irrel f f ->
      (forall xxs1 Hs1 x h h',
          let a := foldl_dep' xs f stop xxs1 Hs1 a0 in
          f a x h = f' a x h') ->
      (forall xxs1 Hs1,
          let a := foldl_dep' xs f stop xxs1 Hs1 a0 in
          stop a = stop' a) ->
      foldl_dep' xs f stop xxs Hs a0 =
      foldl_dep' xs' f' stop' xxs' Hs' a0'.
  Proof.
    intros; subst.
    eapply (foldl_dep_Proper_strong') with (xxs1 := []) (Hs1 := subseq_nil);
      eauto.
  Qed.
End Props.

#[local] Hint Resolve foldl_dep_Proper : loops.

Section Induction.
  Context {A T: Type}.
  Context (xs: list T).
  Context (f: forall (acc: A) (x: T), List.In x xs -> A).
  Context (stop: A -> bool).
  Context (P: A -> Prop) (a0: A).

  Context (H0: P a0).
  Context (Hbody: forall x a1 Hin, P a1 -> P (f a1 x Hin)).

  Lemma foldl_dep_ind xxs Hs:
    P (foldl_dep' xs f stop xxs Hs a0).
  Proof.
    revert xxs Hs a0 H0; induction xxs; simpl; intros.
    - eauto.
    - destruct stop; eauto.
  Qed.
End Induction.

Arguments foldl_dep' {A T} xs f stop !xxs _ _ / : assert.
(* Arguments foldl_dep {A T} !xs f stop a0 / : assert. *)

Section SimpleFolds.
  Context {A B T: Type}.

  Lemma fold_left_as_foldl (f: A -> T -> A) xs:
    forall a0, fold_left f xs a0 = foldl f  (fun _ => false) xs a0.
  Proof. induction xs; simpl; eauto. Qed.

  Lemma fold_left_as_foldl_dep (f: A -> T -> A) xs a0:
    fold_left f xs a0 =
    foldl_dep xs (fun a x _ => f a x) (fun _ => false) a0.
  Proof. rewrite fold_left_as_foldl; eauto using foldl_as_foldl_dep. Qed.

  Lemma map_as_fold_left' (f: A -> B) :
    forall xs xs', xs' ++ List.map f xs =
              List.fold_left (fun a x => a ++ [f x]) xs xs'.
  Proof.
    induction xs; simpl; intros;
      rewrite ?app_nil_r, <- ?IHxs, <- ?app_assoc; eauto.
  Qed.

  Lemma map_as_fold_left (f: A -> B) xs:
    List.map f xs =
    List.fold_left (fun a x => a ++ [f x]) xs [].
  Proof.
    rewrite <- map_as_fold_left'; reflexivity.
  Qed.

  Lemma map_as_fold_right (f: A -> B) :
    forall xs, List.map f xs =
          List.fold_right (fun x a => f x :: a) [] xs.
  Proof.
    induction xs; simpl; intros; try rewrite <- IHxs; eauto.
  Qed.
End SimpleFolds.

Section ZRange.
  Fixpoint z_range' z0 len :=
    match len with
    | O => []
    | S len => z0 :: z_range' (z0 + 1) len
    end.

  Lemma z_range'_snoc' z0 len :
    forall xxs, z_range' z0 (S len) ++ xxs =
           z_range' z0 len ++ [z0 + Z.of_nat len] ++ xxs.
  Proof.
    induction len in z0 |- *.
    - rewrite Z.add_0_r; reflexivity.
    - remember (S len) as n; intros.
      simpl; rewrite IHlen; rewrite Heqn; cbn -[Z.of_nat].
      replace (z0 + Z.of_nat (S len)) with (z0 + 1 + Z.of_nat len) by lia.
      reflexivity.
  Qed.

  Lemma z_range'_snoc z0 len :
    z_range' z0 (S len) =
    z_range' z0 len ++ [z0 + Z.of_nat len].
  Proof.
    intros; pose proof z_range'_snoc' z0 len [] as H.
    rewrite !app_nil_r in H.
    assumption.
  Qed.

  Lemma z_range'_sound len :
    forall z0 z,
      List.In z (z_range' z0 len) ->
      z0 <= z < z0 + Z.of_nat len.
  Proof.
    induction len; cbn -[Z.of_nat].
    - inversion 1; subst; lia.
    - destruct 1 as [-> | H].
      + lia.
      + specialize (IHlen _ _ H). lia.
  Qed.

  Lemma z_range'_complete len :
    forall z0 z,
      z0 <= z < z0 + Z.of_nat len ->
      List.In z (z_range' z0 len).
  Proof.
    induction len; cbn -[Z.of_nat].
    - lia.
    - intros.
      destruct (Z.eq_dec z0 z);
        [left; eauto | right].
      apply IHlen.
      lia.
  Qed.

  Lemma z_range'_length : forall len from,
      List.length (z_range' from len) = len.
  Proof.
    induction len; intros; simpl; rewrite ?IHlen; reflexivity.
  Qed.

  Lemma z_range'_app:
    forall len from len',
      z_range' from (len + len') =
      z_range' from len ++ z_range' (from + Z.of_nat len) len'.
  Proof.
    induction len; cbn -[Z.of_nat]; intros.
    - rewrite Z.add_0_r; reflexivity.
    - rewrite IHlen. repeat (lia || f_equal).
  Qed.

  Definition z_range from to :=
    z_range' from (Z.to_nat (to - from)).

  Lemma z_range_sound from to z:
    List.In z (z_range from to) ->
    from - 1 < z < to.
  Proof.
    unfold z_range; intros H%z_range'_sound; lia.
  Qed.

  Lemma z_range_complete from to z:
    from - 1 < z < to ->
    List.In z (z_range from to).
  Proof.
    unfold z_range; intros; apply z_range'_complete; lia.
  Qed.

  Lemma z_range_add from len:
    z_range from (from + len) = z_range' from (Z.to_nat len).
  Proof. unfold z_range; do 2 f_equal; lia. Qed.

  Lemma z_range_length from to :
    List.length (z_range from to) = Z.to_nat (to - from).
  Proof. unfold z_range; rewrite z_range'_length; reflexivity. Qed.

  Lemma range_unique from to z :
    forall (h h': from - 1 < z < to), h = h'.
  Proof.
    destruct h, h'; f_equal;
      unfold Z.lt in *; eapply @Eqdep_dec.UIP_dec; decide equality.
  Qed.

  Lemma z_range_nil from to:
    from >= to ->
    z_range from to = [].
  Proof.
    intros; unfold z_range.
    replace (Z.to_nat (to - from)) with 0%nat by lia; reflexivity.
  Qed.

  Lemma z_range_cons from to:
    from < to ->
    z_range from to = from :: z_range (from + 1) to.
  Proof.
    unfold z_range; intros.
    replace (Z.to_nat (to - from)) with (S (Z.to_nat (to - (from + 1)))) by lia.
    reflexivity.
  Qed.

  Lemma z_range_app from mid to:
    from <= mid <= to ->
    z_range from to = z_range from mid ++ z_range mid to.
  Proof.
    unfold z_range; intros.
    replace (Z.to_nat (to - from)) with (Z.to_nat (mid - from) + Z.to_nat (to - mid))%nat by lia.
    rewrite z_range'_app. repeat (lia || f_equal).
  Qed.

  Lemma z_range_snoc1 from to:
    from <= to ->
    z_range from (to + 1) = z_range from to ++ [to].
  Proof.
    unfold z_range; intros.
    replace (Z.to_nat (to + 1 - from)) with (S (Z.to_nat (to - from))) by lia.
    rewrite z_range'_snoc, Z2Nat.id by lia; repeat f_equal; lia.
  Qed.

  Lemma z_range_snoc from to:
    from < to ->
    z_range from to = z_range from (to - 1) ++ [to - 1].
  Proof.
    intros; replace to with (to - 1 + 1) at 1 by lia.
    apply z_range_snoc1; lia.
  Qed.
End ZRange.

#[local] Hint Extern 1 => f_equal: loops.
#[local] Hint Resolve range_unique: loops.

Section Loops.
  Context {A: Type}.
  Context (from to: Z).

  Section WithBreak.
    Context (body: forall (acc: A) (idx: Z), from - 1 < idx < to -> A).
    Context (stop: A -> bool).

    Definition ranged_for_break a0 :=
      foldl_dep (z_range from to)
                (fun acc idx in_range =>
                   body acc idx (z_range_sound from to idx in_range))
                stop a0.

    Lemma ranged_for_break_stop a0:
      stop a0 = true -> ranged_for_break a0 = a0.
    Proof. apply foldl_dep_stop. Qed.

    Lemma ranged_for_break_exit a0:
      from >= to -> ranged_for_break a0 = a0.
    Proof. unfold ranged_for_break; auto using foldl_dep_exit, z_range_nil. Qed.
  End WithBreak.

  Section WithBreakSimple.
    Context (body: forall (acc: A) (idx: Z), A).
    Context (stop: A -> bool).

    Definition nd_ranged_for_break a0 :=
      foldl body stop (z_range from to) a0.

    Lemma nd_as_ranged_for_break a0:
      nd_ranged_for_break a0 =
      ranged_for_break (fun a idx _ => body a idx) stop a0.
    Proof. apply foldl_as_foldl_dep. Qed.
  End WithBreakSimple.

  Section NoBreak.
    Context (body: forall (acc: A) (idx: Z), from - 1 < idx < to -> A).

    Definition ranged_for_all :=
      ranged_for_break body (fun _ => false).

    Lemma ranged_for_all_exit a0:
      from >= to -> ranged_for_all a0 = a0.
    Proof. intros; apply ranged_for_break_exit; assumption. Qed.
  End NoBreak.

  Section NoBreakSimple.
    Context (body: forall (acc: A) (idx: Z), A).

    Definition nd_ranged_for_all :=
      nd_ranged_for_break body (fun _ => false).

    Lemma nd_as_ranged_for_all a0:
      nd_ranged_for_all a0 =
      ranged_for_all (fun a idx _ => body a idx) a0.
    Proof. apply foldl_as_foldl_dep. Qed.

    Lemma fold_left_as_nd_ranged_for_all a0:
      fold_left body (z_range from to) a0 =
      nd_ranged_for_all a0.
    Proof.
      rewrite fold_left_as_foldl, !nd_as_ranged_for_all; reflexivity.
    Qed.
  End NoBreakSimple.
End Loops.

Section Properties.
  Context {A: Type}.
  Implicit Type stop : A -> bool.

  Lemma ranged_for_break_Proper :
    forall from from' to to' body body' stop stop' a0 a0',
      a0 = a0' ->
      from = from' -> to = to' ->
      (forall z a h h', body z a h = body' z a h') ->
      (forall a, stop a = stop' a) ->
      ranged_for_break from to body stop a0 =
      ranged_for_break from' to' body' stop' a0'.
  Proof. intros; subst; apply foldl_dep_Proper; eauto. Qed.

  Lemma ranged_for_break_Proper_irrelevant :
    forall from to body body' stop stop' a0 a0',
      a0 = a0' ->
      (forall z a h, body z a h = body' z a h) ->
      (forall a, stop a = stop' a) ->
      ranged_for_break from to body stop a0 =
      ranged_for_break from to body' stop' a0'.
  Proof.
    intros; apply ranged_for_break_Proper; eauto.
    intros; f_equal; apply range_unique.
  Qed.

  Lemma ranged_for_all_Proper :
    forall from from' to to' body body' (a0 a0': A),
      a0 = a0' ->
      from = from' -> to = to' ->
      (forall z a h h', body z a h = body' z a h') ->
      ranged_for_all from to body a0 =
      ranged_for_all from' to' body' a0'.
  Proof. intros; apply ranged_for_break_Proper; eauto. Qed.

  Section Induction.
    Context (P: A -> Prop) (a0: A).

    Context (from to: Z).
    Context (body: forall (acc: A) (idx: Z), from - 1 < idx < to -> A).

    Context (H0: P a0).
    Context (Hbody: forall a1 idx Hle, P a1 -> P (body a1 idx Hle)).

    Section WithBreak.
      Context (stop: A -> bool).

      Lemma ranged_for_break_ind :
        P (ranged_for_break from to body stop a0).
      Proof. unfold ranged_for_break; eapply foldl_dep_ind; eauto. Qed.
    End WithBreak.

    Section NoBreak.
      Lemma ranged_for_all_ind :
        P (ranged_for_all from to body a0).
      Proof. eapply ranged_for_break_ind; eauto. Qed.
    End NoBreak.
  End Induction.

  Ltac forget_range_proofs :=
    repeat match goal with
           | [  |- context[z_range_sound ?from ?to] ] =>
             generalize (z_range_sound from to)
           end.

  Lemma ranged_for_break_app1 {from mid to idx}:
    mid - 1 < to ->
    from - 1 < idx < mid ->
    from - 1 < idx < to.
  Proof. lia. Qed.

  Lemma ranged_for_break_app2 {from mid to idx}:
    from - 1 < mid ->
    mid - 1 < idx < to ->
    from - 1 < idx < to.
  Proof. lia. Qed.

  Lemma ranged_for_break_app from mid to body stop a0 :
    forall (Hf: from - 1 < mid) (Ht: mid - 1 < to),
      ranged_for_break from to body stop a0 =
      let b1 acc idx pr := body acc idx (@ranged_for_break_app1 from mid to idx Ht pr) in
      let b2 acc idx pr := body acc idx (@ranged_for_break_app2 from mid to idx Hf pr) in
      ranged_for_break mid to b2 stop (ranged_for_break from mid b1 stop a0).
  Proof.
    intros; unfold ranged_for_break; forget_range_proofs.
    rewrite (z_range_app from mid to) by lia; intros.
    unshelve erewrite foldl_dep_app; eauto with loops.
  Qed.

  Lemma ranged_for_break_unfold_l1 {from to}:
    from < to -> from - 1 < from < to.
  Proof. lia. Qed.

  Lemma ranged_for_break_unfold_l2 {from to z}:
    from + 1 - 1 < z < to -> from - 1 < z < to.
  Proof. lia. Qed.

  Lemma ranged_for_break_unfold_l from to body stop (a0: A):
    ranged_for_break from to body stop a0 =
    match Z_lt_dec from to with
    | left Hlt =>
      if stop a0 then a0
      else let a0 := body a0 from (ranged_for_break_unfold_l1 Hlt) in
           ranged_for_break
             (from + 1) to
             (fun acc idx pr => body acc idx (ranged_for_break_unfold_l2 pr))
             stop a0
    | right _ => a0
    end.
  Proof.
    destruct Z_lt_dec.
    - unfold ranged_for_break; forget_range_proofs.
      rewrite (z_range_cons from to) by assumption.
      intros; simpl; destruct stop; eauto with loops.
    - apply ranged_for_break_exit; lia.
  Qed.

  Lemma ranged_for_break_extend1 {from to}:
    forall idx, (from - 1 < idx < to)%Z -> (from - 1 < idx < to + 1)%Z.
  Proof. lia. Qed.

  Lemma ranged_for_break_unfold_r1 {from}:
    forall idx, (from - 1 < idx)%Z -> (from - 1 < idx < idx + 1)%Z.
  Proof. lia. Qed.

  Lemma ranged_for_break_unfold_r from to body stop (a0: A) H:
    ranged_for_break from (to + 1) body stop a0 =
    let body' (acc : A) (idx : Z) (pr : from - 1 < idx < to) :=
        body acc idx (ranged_for_break_extend1 idx pr) in
    let butlast := ranged_for_break from to body' stop a0 in
    if stop butlast then butlast
    else body butlast to H.
  Proof.
    intros; unfold ranged_for_break; forget_range_proofs.
    rewrite z_range_snoc1 by lia; intros.
    unshelve erewrite foldl_dep_snoc; eauto with loops; simpl.
    match goal with
    | [  |- (if _ ?x then _ else _) = (if _ ?x' then _ else _) ] =>
      replace x with x' by eauto with loops
    end.
    destruct stop; eauto with loops.
  Qed.

  Lemma ranged_for_break_unfold_r_nstop from to body body1 stop (a0: A) H:
    body_ext_irrel body body1 ->
    stop (ranged_for_break from to body stop a0) = false ->
    ranged_for_break from (to + 1) body1 stop a0 =
    body1 (ranged_for_break from to body stop a0) to H.
  Proof.
    intros Hb Hs.
    unshelve erewrite ranged_for_break_unfold_r; eauto; simpl.
    erewrite (ranged_for_break_Proper _ from _ to _ body _ stop _ a0); intros; eauto.
    rewrite Hs; reflexivity.
  Qed.

  Lemma ranged_for_break_monotonic from to body to1 body1 stop (a0: A):
    to1 >= to ->
    body_ext_irrel body body1 ->
    stop (ranged_for_break from to body stop a0) = true ->
    ranged_for_break from to1 body1 stop a0 =
    ranged_for_break from to body stop a0.
  Proof.
    intros.

    destruct (Z_le_gt_dec to1 from), (Z_le_gt_dec from to).
    1-2: intros; rewrite !ranged_for_break_exit by lia; reflexivity.
    - unshelve erewrite (ranged_for_break_app from to to1); try lia.
      rewrite @ranged_for_break_stop with (a0 := ranged_for_break _ _ _ _ _).
      + eauto with loops.
      + etransitivity; [ | eauto ]; f_equal; eauto with loops.
    - rewrite ranged_for_break_stop.
      rewrite ranged_for_break_exit by lia; reflexivity.
      rewrite ranged_for_break_exit in H1 by lia; auto.
  Qed.

  Definition ranged_for_widen_bounds {from idx from' to} :
    from - 1 < idx < from' ->
    from' <= to ->
    from - 1 < idx < to.
  Proof. lia. Qed.
End Properties.

Arguments Z.of_nat : simpl never.

Lemma replace_nth_app1 {A}:
  forall (xs xs': list A) idx x,
    (idx < List.length xs)%nat ->
    replace_nth idx (xs ++ xs') x =
    replace_nth idx xs x ++ xs'.
Proof.
  induction xs; simpl; intros.
  - lia.
  - destruct idx; simpl; rewrite ?IHxs by lia; reflexivity.
Qed.

Lemma replace_nth_app2 {A}:
  forall (xs xs': list A) idx x,
    (idx >= List.length xs)%nat ->
    replace_nth idx (xs ++ xs') x =
    xs ++ replace_nth (idx - List.length xs) xs' x.
Proof.
  induction xs; simpl; intros.
  - repeat f_equal; lia.
  - destruct idx; simpl; rewrite ?IHxs; lia || reflexivity.
Qed.

Lemma replace_nth_app_skip {A}:
  forall (xs xs': list A) x x',
    replace_nth (List.length xs) (xs ++ x :: xs') x' =
    xs ++ x' :: xs'.
Proof.
  intros; rewrite replace_nth_app2 by lia.
  rewrite Nat.sub_diag; reflexivity.
Qed.

Lemma nth_error_lt_some {A} (xs: list A):
  forall idx,
    (idx < List.length xs)%nat ->
    exists x, List.nth_error xs idx = Some x.
Proof.
  induction xs; simpl; intros; try lia.
  destruct idx; simpl; eauto; [].
  apply IHxs; lia.
Qed.

Section FoldsAsLoops.
  Context {A B T: Type}.

  Notation zlen l := (Z.of_nat (List.length l)).

  (* There are two kinds of folds: those that can keep consulting the original
     list because it is not mutated (`copying_fold_left` above), and those that
     have to consult the list that's being mutated instead.  TODO: Support the
     second kind, as a generalization of the `map` code below.  *)

  (** The way the following lemmas are phrased allows them to be used for all
      sorts of list representations and get/put interfaces (using default
      values, dependent types, etc.). **)

  Section CopyingFolds.
    Lemma copying_fold_left_as_ranged_fold_left' (f: A -> B -> A):
      forall l1 l0 a0,
        List.fold_left f (l0 ++ l1) a0 =
        List.fold_left
          (fun (a: A) idx =>
             match List.nth_error (l0 ++ l1) (Z.to_nat idx) with
             | Some x => f a x
             | None => a
             end)
          (z_range' (zlen l0) (List.length l1))
          (List.fold_left f l0 a0).
    Proof.
      induction l1; intros; simpl.
      - rewrite app_nil_r. reflexivity.
      - rewrite Nat2Z.id, nth_error_app2, Nat.sub_diag by lia.
        rewrite List.assoc_app_cons, IHl1, app_length; simpl.
        rewrite <- List.assoc_app_cons.
        rewrite fold_left_app.
        simpl; repeat f_equal. lia.
    Qed.

    Lemma copying_fold_left_as_ranged_fold_left (f: A -> B -> A):
      forall l a0,
        List.fold_left f l a0 =
        List.fold_left
          (fun (a: A) idx =>
             match List.nth_error l (Z.to_nat idx) with
             | Some x => f a x
             | None => a
             end)
          (z_range 0 (zlen l))
          a0.
    Proof.
      intros; unfold z_range; rewrite Z.sub_0_r, Nat2Z.id.
      apply copying_fold_left_as_ranged_fold_left' with (l0 := []).
    Qed.

    Context (f: A -> B -> A).
    Context (f': A -> Z -> A).

    Definition acts_as_foldl_step (bs: list B) :=
      (forall idx a b,
          nth_error bs (Z.to_nat idx) = Some b ->
          f' a idx  = f a b).

    Lemma acts_as_foldl_step_firstn bs n:
      (n <= length bs)%nat ->
      acts_as_foldl_step bs ->
      acts_as_foldl_step (firstn n bs).
    Proof.
      unfold acts_as_foldl_step; intros.
      eauto using nth_error_firstn_weaken.
    Qed.

    Lemma copying_fold_left_as_nd_ranged_for_all (bs: list B) :
      acts_as_foldl_step bs ->
      forall a0,
        List.fold_left f bs a0 =
        nd_ranged_for_all 0 (zlen bs) f' a0.
    Proof.
      unfold acts_as_foldl_step; intros Hf' *.
      rewrite copying_fold_left_as_ranged_fold_left.
      rewrite <- fold_left_as_nd_ranged_for_all.
      apply fold_left_Proper; try reflexivity.
      intros a idx Hin%z_range_sound.
      destruct (nth_error_lt_some bs (Z.to_nat idx) ltac:(lia)) as (b & Hb).
      specialize (Hf' _ a _ Hb); rewrite Hb; eauto.
    Qed.

    Lemma copying_fold_left_firstn_as_nd_ranged_for_all n bs:
      0 <= n <= zlen bs ->
      acts_as_foldl_step bs ->
      forall a0,
        List.fold_left f (List.firstn (Z.to_nat n) bs) a0 =
        nd_ranged_for_all 0 n f' a0.
    Proof.
      intros.
      replace n with (zlen (firstn (Z.to_nat n) bs)) at 2
        by (rewrite firstn_length_le; lia).
      apply copying_fold_left_as_nd_ranged_for_all, acts_as_foldl_step_firstn;
        eauto || lia.
    Qed.
  End CopyingFolds.

  Section Maps.
    Context (f: A -> A) (f': list A -> Z -> list A).

    Definition acts_as_replace_nth :=
      forall xs a xs', f' (xs ++ a :: xs') (zlen xs) = xs ++ f a :: xs'.

    Context (Hrp: acts_as_replace_nth).

    Lemma map_as_nd_ranged_for_all':
      forall xs xs0 xs1,
        xs0 ++ List.map f xs ++ xs1 =
        nd_ranged_for_all (zlen xs0) (zlen xs0 + zlen xs) f' (xs0 ++ xs ++ xs1).
    Proof.
      setoid_rewrite <- fold_left_as_nd_ranged_for_all.
      unfold z_range; setoid_rewrite Z.add_simpl_l.
      setoid_rewrite Nat2Z.id.
      induction xs; simpl; intros.
      - reflexivity.
      - rewrite Hrp.
        rewrite (List.assoc_app_cons xs0 _ (f a)).
        rewrite (List.assoc_app_cons xs0 (xs ++ xs1) (f a)).
        replace (zlen xs0 + 1) with (zlen (xs0 ++ [f a]))
          by (rewrite app_length, Nat2Z.inj_add; reflexivity).
        rewrite <- IHxs; reflexivity.
    Qed.

    Lemma map_as_nd_ranged_for_all xs:
      List.map f xs = nd_ranged_for_all 0 (zlen xs) f' xs.
    Proof.
      pose proof map_as_nd_ranged_for_all' xs [] [] as H.
      rewrite !app_nil_l, !app_nil_r in H.
      eassumption.
    Qed.

    Lemma map_firstn_as_nd_ranged_for_all n xs:
      (n <= length xs)%nat ->
      List.map f (List.firstn n xs) ++ List.skipn n xs =
      nd_ranged_for_all 0 (Z.of_nat n) f' xs.
    Proof.
      pose proof map_as_nd_ranged_for_all' (List.firstn n xs) [] (List.skipn n xs) as H.
      intros; rewrite !app_nil_l, List.firstn_skipn, List.firstn_length_le in H; simpl in H.
      all: eassumption.
    Qed.

    Lemma nth_error_bound {xs: list A} {n x}:
      nth_error xs n = Some x ->
      -1 < Z.of_nat n < Z.of_nat (length xs).
    Proof.
      pose proof nth_error_Some xs n as (Hn, Hn').
      intros * H; rewrite H in Hn; specialize (Hn ltac:(inversion 1)).
      lia.
    Qed.
  End Maps.

  Section Iter.
   Lemma Nat_iter_S n f: forall (a : A),
       Nat.iter (S n) f a = Nat.iter n f (f a).
   Proof. induction n; intros; simpl; rewrite <- ?IHn; reflexivity. Qed.

   Lemma Nat_iter_as_nd_ranged_for_all n f : forall (a: A) i,
     Nat.iter n f a = nd_ranged_for_all i (i + Z.of_nat n) (fun a _ => f a) a.
   Proof.
     unfold nd_ranged_for_all, nd_ranged_for_break, z_range.
     setoid_rewrite Z.add_simpl_l. rewrite Nat2Z.id.
     induction n; intros.
     - reflexivity.
     - rewrite Nat_iter_S; apply IHn.
   Qed.
  End Iter.
End FoldsAsLoops.

Module Type ExitToken_sig.
  Axiom t : Set.
  Axiom new : t.
  Axiom get : t -> bool.
  Axiom break : t -> t.
  Axiom continue : t -> t.
End ExitToken_sig.

Module ExitToken <: ExitToken_sig.
  (* TODO figure out a representation that lets us store ExitToken.t in the same
     variable as the loop counter *)
  Definition t := bool.
  Definition new : t := false.
  Definition get (tok: t) : bool := tok.
  Definition break (tok: t) : t := true.
  Definition continue (tok: t) : t := false.
  Definition branch {T} (tok: t) (break continue: T) :=
    if tok then break else continue.

  Lemma map_branch {T1 T2} (f: T1 -> T2) tok break continue:
    f (branch tok break continue) =
    branch tok (f break) (f continue).
  Proof. destruct tok; reflexivity. Qed.
End ExitToken.

Section WithTok.
  Context {A: Type}.

  Section Loops.
    Context from to
            (body: forall (acc: A) (tok: ExitToken.t) (idx: Z),
                from - 1 < idx < to -> (ExitToken.t * A))
            (a0: A).

    Definition ranged_for' :=
      ranged_for_break
        from to
        (fun acc idx pr =>
           body (snd acc) ExitToken.new idx pr)
        (fun tok_acc => ExitToken.get (fst tok_acc))
        (ExitToken.new, a0).

    Definition ranged_for :=
      snd ranged_for'.

    Lemma ranged_for_exit :
      from >= to ->
      ranged_for = a0.
    Proof.
      unfold ranged_for, ranged_for'; intros.
      rewrite ranged_for_break_exit; eauto.
    Qed.
  End Loops.

  Section SimpleLoops.
    Context (from to: Z)
            (body: forall (acc: A) (tok: ExitToken.t) (idx: Z), ExitToken.t * A)
            (a0: A).

    Definition nd_ranged_for' :=
      nd_ranged_for_break
        from to
        (fun acc idx => body (snd acc) ExitToken.new idx)
        (fun tok_acc => ExitToken.get (fst tok_acc))
        (ExitToken.new, a0).

    Lemma nd_as_ranged_for' :
      nd_ranged_for' =
      ranged_for' from to (fun acc tok idx _ => body acc tok idx) a0.
    Proof. apply nd_as_ranged_for_break. Qed.

    Definition nd_ranged_for :=
      snd nd_ranged_for'.

    Lemma nd_as_ranged_for :
      nd_ranged_for =
      ranged_for from to (fun acc tok idx _ => body acc tok idx) a0.
    Proof. unfold nd_ranged_for, ranged_for; f_equal; apply nd_as_ranged_for'. Qed.
  End SimpleLoops.

  Lemma ranged_for'_Proper :
    forall from from' to to' body body' a0 a0',
      a0 = a0' ->
      from = from' -> to = to' ->
      (forall tok z a h h', body tok z a h = body' tok z a h') ->
      ranged_for' from to body a0 =
      ranged_for' from' to' body' a0'.
  Proof.
    unfold ranged_for'; intros.
    apply ranged_for_break_Proper; eauto || congruence.
  Qed.

  Lemma ranged_for'_unfold_r from to body a0 H:
    let wbody acc tok idx pr :=
        body acc tok idx (ranged_for_break_extend1 idx pr) in
    ranged_for' from (to + 1) body a0 =
    let butlast := ranged_for' from to wbody a0 in
    if fst butlast then butlast
    else body (snd butlast) ExitToken.new to H.
  Proof.
    unfold ranged_for'.
    erewrite ranged_for_break_unfold_r.
    reflexivity.
  Qed.

  Lemma ranged_for'_unfold_r_nstop from to body body' a0
        (H: from  - 1 < to < to + 1):
    (forall t, body_ext_irrel (body t) (body' t)) ->
    fst (ranged_for' from to body a0) = false ->
    ranged_for' from (to + 1) body' a0 =
    body' (snd (ranged_for' from to body a0)) ExitToken.new to H.
  Proof.
    unfold ranged_for'; intros Hb Hc.
    erewrite ranged_for_break_unfold_r_nstop; eauto; cbv beta; eauto.
  Qed.

  Lemma ranged_for'_monotonic from to body a0 to' body':
    to' >= to ->
    (forall t, body_ext_irrel (body t) (body' t)) ->
    fst (ranged_for' from to body a0) = true ->
    ranged_for' from to' body' a0 =
    ranged_for' from to body a0.
  Proof.
    unfold ranged_for'; intros.
    erewrite ranged_for_break_monotonic; eauto; cbv beta; eauto.
  Qed.

  Lemma ranged_for_all_as_ranged_for from to body a0:
    ranged_for_all from to body a0 =
    ranged_for from to (fun a tok idx pr => (tok, body a idx pr)) a0.
  Proof.
    unfold ranged_for_all, ranged_for, ranged_for', ranged_for_break.
    generalize (z_range_sound from to);
      generalize (z_range from to).
    intros;
      generalize (@subseq_refl _ l);
      generalize l at 1 5 8 as ll.
    intros ll; revert from to body a0 a;
      induction ll; simpl; intros.
    - reflexivity.
    - rewrite IHll; reflexivity.
  Qed.
End WithTok.

Section with_parameters.
  Context {width: Z} {word: word.word width}.
  Context {word_ok : word.ok word}.
  Context {A: Type}
          (from to: word).

  Section Loops.
    Context {to_Z: word -> Z}
            (to_Z_of_Z: forall l h w,
                to_Z l <= w <= to_Z h ->
                to_Z (word.of_Z w) = w).

    Lemma ranged_for_w1 {idx}:
      to_Z from - 1 < idx < to_Z to ->
      to_Z from - 1 < to_Z (word.of_Z idx) < to_Z to.
    Proof. intros; erewrite (to_Z_of_Z from to); lia. Qed.

    Section WithTok.
      Context (body: forall (acc: A) (tok: ExitToken.t) (idx: word),
                  to_Z from - 1 < to_Z idx < to_Z to ->
                  (ExitToken.t * A)).

      Definition w_body_tok acc tok idx pr :=
        body acc tok (word.of_Z idx) (ranged_for_w1 pr).

      Definition ranged_for_w (a0: A) : A :=
        ranged_for (to_Z from) (to_Z to) w_body_tok a0.
      Definition ranged_for_w_continued (a0: A) : \<< word, A \>> :=
        \< to, ranged_for_w a0 \>.

      Lemma ranged_for_w_exit a0:
        to_Z from >= to_Z to -> ranged_for_w a0 = a0.
      Proof.
        intros; unfold ranged_for_w, ranged_for, ranged_for'.
        rewrite ranged_for_break_exit; eauto.
      Qed.

      Section Induction.
        Context (P: A -> Prop) (a0: A).
        Context (H0: P a0).
        Context (Hbody: forall tok idx a1 Hle, P a1 -> P (snd (body a1 tok idx Hle))).

        Lemma ranged_for_w_ind : P (ranged_for_w a0).
        Proof.
          unfold ranged_for_w, ranged_for, ranged_for'.
          apply ranged_for_break_ind; simpl; eauto.
        Qed.
      End Induction.
    End WithTok.

    Section SimpleWithTok.
      Context (body: forall (acc: A) (tok: ExitToken.t) (idx: word),
                  (ExitToken.t * A)).

      Definition nd_w_body_tok acc tok idx :=
        body acc tok (word.of_Z idx).

      Definition nd_ranged_for_w (a0: A) : A :=
        nd_ranged_for (to_Z from) (to_Z to) nd_w_body_tok a0.
      Definition nd_ranged_for_w_continued (a0: A) : \<< word, A \>> :=
        \< to, nd_ranged_for_w a0 \>.

      Lemma nd_as_ranged_for_w a0 :
        nd_ranged_for_w a0 =
        ranged_for_w (fun acc tok idx _ => body acc tok idx) a0.
      Proof.
        unfold nd_ranged_for_w, ranged_for_w.
        rewrite nd_as_ranged_for; reflexivity.
      Qed.

      Lemma nd_as_ranged_for_w_continued a0 :
        nd_ranged_for_w_continued a0 =
        ranged_for_w_continued (fun acc tok idx _ => body acc tok idx) a0.
      Proof.
        unfold nd_ranged_for_w_continued, ranged_for_w_continued.
        rewrite nd_as_ranged_for_w; reflexivity.
      Qed.
    End SimpleWithTok.

    Section NoBreak.
      Context (body: forall (acc: A) (idx: word),
                  to_Z from - 1 < to_Z idx < to_Z to ->
                  A).

      Definition w_body acc idx pr :=
        body acc (word.of_Z idx) (ranged_for_w1 pr).

      Definition ranged_for_all_w (a0: A) : A :=
        ranged_for_all (to_Z from) (to_Z to) w_body a0.
      Definition ranged_for_all_w_continued (a0: A) : \<< word, A \>> :=
        \< to, ranged_for_all_w a0 \>.

      Lemma ranged_for_all_w_exit a0:
        to_Z from >= to_Z to -> ranged_for_all_w a0 = a0.
      Proof.
        intros; apply ranged_for_all_exit; eauto.
      Qed.

      Section Induction.
        Context (P: A -> Prop) (a0: A).
        Context (H0: P a0).
        Context (Hbody: forall a1 idx Hle, P a1 -> P (body a1 idx Hle)).

        Lemma ranged_for_all_w_ind : P (ranged_for_all_w a0).
        Proof.
          unfold ranged_for_all_w.
          apply ranged_for_all_ind; simpl; eauto.
        Qed.
      End Induction.
    End NoBreak.

    Section SimpleNoBreak.
      Context (body: forall (acc: A) (idx: word), A).

      Definition nd_w_body acc idx :=
        body acc (word.of_Z idx).

      Definition nd_ranged_for_all_w (a0: A) : A :=
        nd_ranged_for_all (to_Z from) (to_Z to) nd_w_body a0.
      Definition nd_ranged_for_all_w_continued (a0: A) : \<< word, A \>> :=
        \< to, nd_ranged_for_all_w a0 \>.

      Lemma nd_as_ranged_for_all_w a0 :
        nd_ranged_for_all_w a0 =
        ranged_for_all_w (fun acc idx _ => body acc idx) a0.
      Proof.
        unfold nd_ranged_for_all_w, ranged_for_all_w.
        rewrite nd_as_ranged_for_all; reflexivity.
      Qed.

      Lemma nd_as_ranged_for_all_w_continued a0 :
        nd_ranged_for_all_w_continued a0 =
        ranged_for_all_w_continued (fun acc idx _ => body acc idx) a0.
      Proof.
        unfold nd_ranged_for_all_w_continued, ranged_for_all_w_continued.
        rewrite nd_as_ranged_for_all_w; reflexivity.
      Qed.
    End SimpleNoBreak.
  End Loops.

  Section Unsigned.
    Lemma word_unsigned_of_Z_bracketed (l h : word) w :
      word.unsigned l <= w <= word.unsigned h ->
      @word.unsigned _ word (word.of_Z w) = w.
    Proof.
      pose proof word.unsigned_range l.
      pose proof word.unsigned_range h.
      intros; rewrite word.unsigned_of_Z, word.wrap_small; lia.
    Qed.

    Definition ranged_for_u :=
      ranged_for_w word_unsigned_of_Z_bracketed.
    Definition ranged_for_u_continued :=
      ranged_for_w_continued word_unsigned_of_Z_bracketed.

    Definition ranged_for_u_ind :=
      ranged_for_w_ind word_unsigned_of_Z_bracketed.

    Definition ranged_for_all_u :=
      ranged_for_all_w word_unsigned_of_Z_bracketed.
    Definition ranged_for_all_u_continued :=
      ranged_for_all_w_continued word_unsigned_of_Z_bracketed.

    Definition ranged_for_all_u_ind :=
      ranged_for_all_w_ind word_unsigned_of_Z_bracketed.

    Definition nd_ranged_for_u :=
      nd_ranged_for_w (to_Z := word.unsigned).
    Definition nd_ranged_for_u_continued :=
      nd_ranged_for_w_continued (to_Z := word.unsigned).

    Definition nd_ranged_for_all_u :=
      nd_ranged_for_all_w (to_Z := word.unsigned).
    Definition nd_ranged_for_all_u_continued :=
      nd_ranged_for_all_w_continued (to_Z := word.unsigned).
  End Unsigned.

  Section Signed.
    Lemma word_signed_of_Z_bracketed (l h : word) w:
      word.signed l <= w <= word.signed h ->
      @word.signed _ word (word.of_Z w) = w.
    Proof.
      pose proof word.signed_range l.
      pose proof word.signed_range h.
      intros; rewrite word.signed_of_Z, word.swrap_inrange; lia.
    Qed.

    Definition ranged_for_s :=
      ranged_for_w word_signed_of_Z_bracketed.
    Definition ranged_for_s_continued :=
      ranged_for_w_continued word_signed_of_Z_bracketed.

    Definition ranged_for_s_ind :=
      ranged_for_w_ind word_signed_of_Z_bracketed.

    Definition ranged_for_all_s :=
      ranged_for_all_w word_signed_of_Z_bracketed.
    Definition ranged_for_all_s_continued :=
      ranged_for_all_w_continued word_signed_of_Z_bracketed.

    Definition ranged_for_all_s_ind :=
      ranged_for_all_w_ind word_signed_of_Z_bracketed.

    Definition nd_ranged_for_s :=
      nd_ranged_for_w (to_Z := word.signed).
    Definition nd_ranged_for_s_continued :=
      nd_ranged_for_w_continued (to_Z := word.signed).

    Definition nd_ranged_for_all_s :=
      nd_ranged_for_all_w (to_Z := word.signed).
    Definition nd_ranged_for_all_s_continued :=
      nd_ranged_for_all_w_continued (to_Z := word.signed).
  End Signed.

  Definition wZ_must_pos (a: Z) {_ : Bitwidth width} :
    match Z_gt_dec a 0, Z_le_dec a (2 ^ 32 - 1) with
    | left _, left _ => @word.unsigned _ word (word.of_Z a) > 0
    | _, _ => True
    end.
  Proof.
    destruct Z_le_dec, Z_gt_dec; [ | exact I .. ].
    assert (2 ^ 32 - 1 <= 2 ^ width - 1) by
        (destruct Bitwidth.width_cases as [-> | ->]; lia).
    rewrite word.unsigned_of_Z, word.wrap_small; lia.
  Qed.
End with_parameters.

Section with_parameters.
  Context {width: Z} {word: word.word width} {word_ok : word.ok word}.

  Context {locals: map.map String.string word}.
  Lemma getmany0 (l : locals) t vt vx vy x y:
    map.getmany_of_list l (vx :: vy :: vt) = Some (x :: y :: t) ->
    map.get l vx = Some x.
  Proof.
    intros; eapply (map.getmany_of_list_get _ 0); eauto || reflexivity.
  Qed.

  Lemma getmany1 (l : locals) t vt vx vy x y:
    map.getmany_of_list l (vx :: vy :: vt) = Some (x :: y :: t) ->
    map.get l vy = Some y.
  Proof.
    intros; eapply (map.getmany_of_list_get _ 1); eauto || reflexivity.
  Qed.

  Context {BW: Bitwidth width}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {mem: map.map word Byte.byte}.
  Context {mem_ok : map.ok mem}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Ltac _split_conj :=
    match goal with
    | [ H: forall from a0 tr mem0 locals0, _ -> _ /\ _ |- _ ] =>
      pose proof (fun from a0 tr mem locals pred => proj1 (H from a0 tr mem locals pred));
      pose proof (fun from a0 tr mem locals pred => proj2 (H from a0 tr mem locals pred))
    end.

  Notation wbody body pr Hr :=
    (fun acc tok idx pr =>
       body acc tok idx (ranged_for_widen_bounds pr Hr)).

  Notation wbody_all body pr Hr :=
    (fun acc idx pr =>
       body acc idx (ranged_for_widen_bounds pr Hr)).

  Notation in_signed_bounds x :=
    (- 2 ^ (width - 1) <= x < 2 ^ (width - 1)).

  Notation in_unsigned_bounds x :=
    (0 <= x < 2 ^ width).

  Section Generic.
    Context (signed: bool).

    Definition cmd_loop (signed: bool) from_var to_expr body_impl :=
      cmd.while
        (expr.op (if signed then bopname.lts else bopname.ltu)
                 (expr.var from_var) to_expr)
        body_impl.

    Lemma _compile_ranged_for : forall A {tr mem locals functions}
          (from to: Z) body (a0: A),
      let v := ranged_for from to body a0 in
      forall {P} {pred: P v -> predicate}
        (loop_pred: forall (idx: Z) (a: A), predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (from_var: string) (to_expr: expr) vars,

        let lp from tok_acc tr mem locals :=
            let from := ExitToken.branch (fst tok_acc) to (from + 1) in
            loop_pred from (snd tok_acc) tr mem locals in

        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.get locals from_var = Some (word.of_Z from) /\
            WeakestPrecondition.dexpr mem locals to_expr (word.of_Z to)) ->

        loop_pred from a0 tr mem locals ->

        (if signed then in_signed_bounds from /\ in_signed_bounds to
         else in_unsigned_bounds from /\ in_unsigned_bounds to) ->

        ((* loop body *)
          let lp := lp in
          forall tr mem locals from'
            (Hl: from - 1 < from')
            (Hr: from' < to)
            (Hr': from' <= to),
            let a := ranged_for' from from' (wbody body pr Hr') a0 in
            let prev_tok := fst a in
            let acc := snd a in  (* FIXME use primitive projections? *)
            ExitToken.get prev_tok = false ->
            loop_pred from' acc tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body acc ExitToken.new from' (conj Hl Hr)) }>)) ->
        (let v := v in
         forall tr mem locals,
           let from' := Z.max from to in
           loop_pred from' v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd_loop signed from_var to_expr body_impl)
          k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
      intros * Hlocals Hinit Hbounds Hbody Hk;
        unfold cmd_loop.
      repeat straightline.
      _split_conj.

      destruct (Z_gt_le_dec from to).
      { (* Loop won't run at all *)
        eexists nat, lt, (fun n tr mem locals => loop_pred from a0 tr mem locals);
          repeat apply conj; eauto using lt_wf, 0%nat.

        intros.
        exists (word.of_Z 0); repeat apply conj.
        - eexists; split; eauto.
          eapply WeakestPrecondition_dexpr_expr; eauto.
          pose proof Zlt_cases from to.
          destruct signed; simpl;
            rewrite <- ?word.morph_lts, <- ?word.morph_ltu by tauto;
            destruct (from <? to); reflexivity || lia.
        - rewrite word.unsigned_of_Z_0; intros; exfalso; lia.
        - intros. apply Hk.
          replace (Z.max from to) with from by lia.
          subst v. rewrite ranged_for_exit; eauto || lia. }

      pose (inv := (fun n tr mem locals =>
                     exists from' (Hr: from' <= to),
                       from <= from' /\
                       n = Z.to_nat (to - from') /\
                       let a := ranged_for' from from' (wbody body pr Hr) a0 in
                       (from' < to -> ExitToken.get (fst a) = false) /\
                       loop_pred from' (snd a) tr mem locals)).

      red. red.

      eexists nat, lt, inv; split.
      { apply lt_wf. }
      { split.
        { (* Initial invariant *)
          eexists; red.
          exists from.
          exists (ltac:(eauto): from <= to).
          split; try reflexivity.
          split; try reflexivity.
          unfold ranged_for, ranged_for';
            rewrite ranged_for_break_exit by lia.
          eauto. }
        intros niters * Hinv.
        destruct Hinv as (from' & Hl & Hr & -> & Hcontinue & Hpred).
        eexists ?[b]; split; [|split].
        { (* loop test can be eval'd *)
          eexists; split; eauto.
          eapply WeakestPrecondition_dexpr_expr; [|eauto].
          destruct signed; simpl;
            rewrite <- ?word.morph_lts, <- ?word.morph_ltu by lia;
            reflexivity. }
        all:
          pose proof Zlt_cases from' to;
          intros Hnz; destruct (from' <? to);
            try (rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1 in Hnz;
                 congruence); [].

        { eapply WeakestPrecondition_weaken; cycle 1.
          { (* User-supplied loop body *)
            unshelve apply Hbody; cycle -2.
            { unshelve apply Hcontinue; eassumption. }
            { apply Hpred. }
            all: eauto with arith || lia. }
          { (* Invariant proof *)
            subst lp; cbv beta.
            set (body _ _ _ _) as acc_tok in *.
            set (ExitToken.branch (fst acc_tok) to (from' + 1)) as from'' in *.

            intros * Hlp.
            exists (Z.to_nat (to - from'')); split.

            assert (exists h,
                       acc_tok =
                       (ranged_for' from (from' + 1) (wbody body pr h) a0))
              as [? Hrefold].
            { exists (ltac:(lia): from' + 1 <= to).
              subst acc_tok.
              erewrite @ranged_for'_unfold_r_nstop with (H := ?[H]).
              [H]: lia.
              f_equal; f_equal; apply range_unique.
              cbv beta; intros; f_equal; apply range_unique.
              erewrite ranged_for'_Proper; [apply Hcontinue|..];
                intros; cbv beta; f_equal; (congruence || lia || apply range_unique). }

            { (* Invariant proof *)
              exists from''.

              unshelve eexists;
                [subst from''; destruct (fst acc_tok); simpl; lia|].
              split;
                [subst from''; destruct (fst acc_tok); simpl; lia|].

              split; [reflexivity|].

              split.
              { (* If index is < to, loop didn't exit *)
                subst from'';
                  destruct (fst acc_tok) eqn:Htok; simpl in *;
                    [intros; exfalso; lia|].
                intros; rewrite <- Htok, Hrefold by assumption.
                unfold ExitToken.get; f_equal.
                apply ranged_for'_Proper;
                  intros; cbv beta; f_equal; (congruence || lia || apply range_unique). }

              { (* Final invariant holds *)
                subst from'';
                  destruct (fst acc_tok) eqn:Htok; simpl in *;
                    rewrite Hrefold in Hlp.
                { (* Loop exited early *)
                  erewrite ranged_for'_monotonic.
                  - eassumption.
                  - lia.
                  - cbv beta; intros; f_equal; apply range_unique.
                  - rewrite <- Hrefold; assumption. }
                { (* Loop did not exit early *)
                  erewrite ranged_for'_Proper;
                  [ eapply Hlp| .. ];
                  intros; cbv beta; f_equal; (congruence || lia || apply range_unique). } } }

            { (* Variant decreased *)
              subst from''. destruct (fst acc_tok); simpl; lia. } } }

        { (* Loop end analysis *)
          cbv zeta in Hpred.
          assert (from' = to) as Hend by lia; destruct Hend.
          eapply Hk.
          subst v.
          unfold ranged_for.
          replace (Z.max from from') with from' by lia.
          erewrite ranged_for'_Proper;
            [ eapply Hpred| .. ];
            intros; cbv beta; f_equal; (congruence || lia || apply range_unique). } }
    Qed.

    Definition cmd_loop_incr signed from_var to_expr body_impl :=
      cmd_loop signed from_var to_expr
               (cmd.seq body_impl
                        (cmd.set from_var
                                 (expr.op bopname.add
                                          (expr.var from_var)
                                          (expr.literal 1)))).

    Lemma compile_ranged_for_with_auto_increment : forall A {tr mem locals functions}
          (from to: Z) body (a0: A),
      let v := ranged_for from to body a0 in
      forall {P} {pred: P v -> predicate}
        (loop_pred: forall (idx: Z) (a: A), predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (from_var: string) (to_expr: expr) vars,

        let lp from tok_acc tr mem locals :=
            let from := ExitToken.branch (fst tok_acc) (to - 1) from in
            loop_pred from (snd tok_acc) tr mem locals in

        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.get locals from_var = Some (word.of_Z from) /\
            WeakestPrecondition.dexpr mem locals to_expr (word.of_Z to)) ->

        (forall from from' acc tr mem locals,
            loop_pred from acc tr mem locals ->
            loop_pred from' acc tr mem (map.put locals from_var (word.of_Z from'))) ->

        loop_pred from a0 tr mem locals ->

        (if signed then in_signed_bounds from /\ in_signed_bounds to
         else in_unsigned_bounds from /\ in_unsigned_bounds to) ->

        ((* loop body *)
          let lp := lp in
          forall tr mem locals from'
            (Hl: from - 1 < from')
            (Hr: from' < to)
            (Hr': from' <= to),
            let a := ranged_for' from from' (wbody body pr Hr') a0 in
            let prev_tok := fst a in
            let acc := snd a in  (* FIXME use primitive projections? *)
            ExitToken.get prev_tok = false ->
            loop_pred from' acc tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body acc ExitToken.new from' (conj Hl Hr)) }>)) ->
        (let v := v in
         forall tr mem locals,
           let from' := Z.max from to in
           loop_pred from' v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd_loop_incr signed from_var to_expr body_impl)
          k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
      intros; _split_conj; eapply _compile_ranged_for; try eassumption.
      (* Goal: (body; from := from + 1) does the right thing *)
      intros. simpl.
      eapply WeakestPrecondition_weaken; cycle 1.
      red; eauto.
      (* Goal: (from := from + 1) does the right thing *)

      subst lp acc a; cbv beta; intros * Hlp.

      eexists; split.
      eexists; split.
      eauto.

      simpl. red. red. rewrite <- word.ring_morph_add.
      rewrite (ExitToken.map_branch (fun z => word.of_Z (z + 1))).
      ring_simplify (to - 1 + 1).
      rewrite <- ExitToken.map_branch.
      reflexivity.

      red. red. eauto.
    Qed.

    Definition cmd_loop_fresh signed from_var from_expr to_var to_expr body_impl k_impl :=
      cmd.seq (cmd.set from_var from_expr)
              (cmd.seq (cmd.set to_var to_expr)
                       (cmd.seq (cmd_loop_incr signed from_var to_var body_impl)
                       k_impl)).

    Lemma compile_ranged_for_fresh : forall A {tr mem locals functions}
          (from to: Z) body (a0: A),
      let v := ranged_for from to body a0 in
      forall {P} {pred: P v -> predicate}
        (loop_pred: forall (idx: Z) (a: A), predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (from_var to_var: string) (from_expr to_expr: expr) vars,

        let locals1 := map.put locals from_var (word.of_Z from) in
        let locals2 := map.put locals1 to_var (word.of_Z to) in

        WeakestPrecondition.dexpr mem locals from_expr (word.of_Z from) ->
        WeakestPrecondition.dexpr mem locals1 to_expr (word.of_Z to) ->

        let lp from tok_acc tr mem locals :=
            let from := ExitToken.branch (fst tok_acc) (to - 1) from in
            loop_pred from (snd tok_acc) tr mem locals in

        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.get locals from_var = Some (word.of_Z from) /\
            map.get locals to_var = Some (word.of_Z to)) ->

        (forall from from' acc tr mem locals,
            loop_pred from acc tr mem locals ->
            loop_pred from' acc tr mem (map.put locals from_var (word.of_Z from'))) ->

        loop_pred from a0 tr mem locals2 ->

        (if signed then in_signed_bounds from /\ in_signed_bounds to
         else in_unsigned_bounds from /\ in_unsigned_bounds to) ->

        ((* loop body *)
          let lp := lp in
          forall tr mem locals from'
            (Hl: from - 1 < from')
            (Hr: from' < to)
            (Hr': from' <= to),
            let a := ranged_for' from from' (wbody body pr Hr') a0 in
            let prev_tok := fst a in
            let acc := snd a in  (* FIXME use primitive projections? *)
            ExitToken.get prev_tok = false ->
            loop_pred from' acc tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body acc ExitToken.new from' (conj Hl Hr)) }>)) ->
        (let v := v in
         forall tr mem locals,
           let from' := Z.max from to in
           loop_pred from' v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd_loop_fresh signed from_var from_expr to_var to_expr body_impl k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
      intros; unfold cmd_loop_fresh.
      repeat (repeat straightline; eexists; split; eauto).
      eapply compile_ranged_for_with_auto_increment; eauto.
      { _split_conj; split; eauto; []; repeat straightline; eauto. }
    Qed.

    Lemma compile_ranged_for_all_fresh : forall A {tr mem locals functions}
          (from to: Z) body (a0: A),
      let v := ranged_for_all from to body a0 in
      forall {P} {pred: P v -> predicate}
        (loop_pred: forall (idx: Z) (a: A), predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (from_var to_var: string) (from_expr to_expr: expr) vars,

        let locals1 := map.put locals from_var (word.of_Z from) in
        let locals2 := map.put locals1 to_var (word.of_Z to) in

        WeakestPrecondition.dexpr mem locals from_expr (word.of_Z from) ->
        WeakestPrecondition.dexpr mem locals1 to_expr (word.of_Z to) ->

        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.get locals from_var = Some (word.of_Z from) /\
            map.get locals to_var = Some (word.of_Z to)) ->

        (forall from from' acc tr mem locals,
            loop_pred from acc tr mem locals ->
            loop_pred from' acc tr mem (map.put locals from_var (word.of_Z from'))) ->

        loop_pred from a0 tr mem locals2 ->

        (if signed then in_signed_bounds from /\ in_signed_bounds to
         else in_unsigned_bounds from /\ in_unsigned_bounds to) ->

        ((* loop body *)
          let lp := loop_pred in
          forall tr mem locals from'
            (Hl: from - 1 < from')
            (Hr: from' < to)
            (Hr': from' <= to),
            let acc := ranged_for_all from from' (wbody_all body pr Hr') a0 in
            loop_pred from' acc tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body acc from' (conj Hl Hr)) }>)) ->
        (let v := v in
         forall tr mem locals,
           let from' := Z.max from to in
           loop_pred from' v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd_loop_fresh signed from_var from_expr to_var to_expr body_impl k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
      cbv zeta; intros until P.
      rewrite ranged_for_all_as_ranged_for; intros * ?????? Hb **.
      simple apply compile_ranged_for_fresh with (loop_pred := loop_pred);
        eauto; []; cbv zeta; intros.
      eapply WeakestPrecondition_weaken; [ | eapply Hb];
        simpl; rewrite ranged_for_all_as_ranged_for; intros; eassumption.
    Qed.

    Lemma compile_nd_ranged_for_all_fresh : forall A {tr mem locals functions}
          (from to: Z) body (a0: A),
      let v := nd_ranged_for_all from to body a0 in
      forall {P} {pred: P v -> predicate}
        (loop_pred: forall (idx: Z) (a: A), predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (from_var to_var: string) (from_expr to_expr: expr) vars,

        let locals1 := map.put locals from_var (word.of_Z from) in
        let locals2 := map.put locals1 to_var (word.of_Z to) in

        WeakestPrecondition.dexpr mem locals from_expr (word.of_Z from) ->
        WeakestPrecondition.dexpr mem locals1 to_expr (word.of_Z to) ->

        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.get locals from_var = Some (word.of_Z from) /\
            map.get locals to_var = Some (word.of_Z to)) ->

        (forall from from' acc tr mem locals,
            loop_pred from acc tr mem locals ->
            loop_pred from' acc tr mem (map.put locals from_var (word.of_Z from'))) ->

        loop_pred from a0 tr mem locals2 ->

        (if signed then in_signed_bounds from /\ in_signed_bounds to
         else in_unsigned_bounds from /\ in_unsigned_bounds to) ->

        ((* loop body *)
          let lp := loop_pred in
          forall tr mem locals from'
            (Hl: from - 1 < from')
            (Hr: from' < to)
            (Hr': from' <= to),
            let acc := nd_ranged_for_all from from' body a0 in
            loop_pred from' acc tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body acc from') }>)) ->
        (let v := v in
         forall tr mem locals,
           let from' := Z.max from to in
           loop_pred from' v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd_loop_fresh signed from_var from_expr to_var to_expr body_impl k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
      cbv zeta; intros until P.
      rewrite nd_as_ranged_for_all; intros * ?????? Hb **.
      simple apply compile_ranged_for_all_fresh with (loop_pred := loop_pred);
        eauto; []; cbv zeta; intros.
      eapply WeakestPrecondition_weaken; [ | eapply Hb];
        simpl; try rewrite nd_as_ranged_for_all; intros; eassumption.
    Qed.
  End Generic.

  Section GenericWordLoops.
    Context {signed: bool}.

    Context {to_Z: word -> Z}
            (of_Z_to_Z: forall w, word.of_Z (to_Z w) = w)
            (to_Z_of_Z: forall l h w,
                to_Z l <= w <= to_Z h ->
                to_Z (word.of_Z w) = w)
            {max: word -> word -> word}
            (max_of_Z: forall w1 w2, max w1 w2 = word.of_Z (Z.max (to_Z w1) (to_Z w2))).

    Lemma compile_ranged_for_w : forall A {tr mem locals functions}
          (from to: word)
          (H: if signed then in_signed_bounds (to_Z from) /\ in_signed_bounds (to_Z to)
              else in_unsigned_bounds (to_Z from) /\ in_unsigned_bounds (to_Z to))
          body (a0: A),
      let v := ranged_for_w from to to_Z_of_Z body a0 in
      forall {P} {pred: P v -> predicate}
        (loop_pred: word -> A -> predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (from_var to_var: string) vars,

        let lp from tok_acc tr mem locals :=
            let from := ExitToken.branch (fst tok_acc) (word.sub to (word.of_Z 1)) from in
            loop_pred from (snd tok_acc) tr mem locals in

        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.get locals from_var = Some from /\
            WeakestPrecondition.dexpr mem locals to_var to) ->

        (forall from from' acc tr mem locals,
            loop_pred from acc tr mem locals ->
            loop_pred from' acc tr mem (map.put locals from_var from')) ->

        loop_pred from a0 tr mem locals ->

        ((* loop body *)
          let lp := lp in
          forall tr mem locals from'
            (Hl: to_Z from - 1 < to_Z from')
            (Hr: to_Z from' < to_Z to)
            (Hr': to_Z from' <= to_Z to),
            let tok := ExitToken.new in
            let a := ranged_for' (to_Z from) (to_Z from')
                                (w_body_tok _ _ to_Z_of_Z
                                            (wbody body pr Hr')) a0 in
            ExitToken.get (fst a) = false ->

            loop_pred from' (snd a) tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body (snd a) tok from' (conj Hl Hr)) }>)) ->
        (let v := v in
         forall tr mem locals,
           let from' := max from to in
           loop_pred from' v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd_loop_incr signed from_var to_var body_impl)
          k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
      intros ? ? ? ? ? ? ? ?.
      intros * Hl Hfromindep Hinit Hbody Hk.
      apply compile_ranged_for_with_auto_increment
        with (loop_pred := fun z => loop_pred (word.of_Z z)).

      - rewrite of_Z_to_Z; eauto.
      - eauto.
      - rewrite of_Z_to_Z; eassumption.
      - eassumption.
      - intros.
        assert (exists h, a = ranged_for' (to_Z from) (to_Z (word.of_Z from')) (w_body_tok from (word.of_Z from') to_Z_of_Z (wbody body pr h)) a0) as [h eqn].
        { unshelve eexists; subst a.
          { rewrite (to_Z_of_Z from to); lia. }
          unshelve apply ranged_for'_Proper; reflexivity || eauto.
          { rewrite (to_Z_of_Z from to); try reflexivity; lia. }
          { unfold w_body_tok; intros; f_equal.
            apply range_unique. } }

        clearbody a; subst a; unfold w_body_tok at 1; cbv beta.
        eapply WeakestPrecondition_weaken; cycle 1.
        + unshelve (apply Hbody; eassumption);
            rewrite (to_Z_of_Z from to); lia.
        + unfold lp, lp0.
          set (ranged_for' _ _ _ _) as fr.

          set (body _ _ _ _) as b0; set (body _ _ _ _) as b1; assert (b0 = b1).
          { subst b0 b1. f_equal. apply range_unique. }
          clearbody b0; subst.

          intros * Hlp.
          * destruct (fst b1); simpl in *;
              repeat rewrite ?word.ring_morph_add, ?word.ring_morph_sub, ?of_Z_to_Z;
              eauto.
      - intros; eapply Hk.
        rewrite max_of_Z; eassumption.
    Qed.

    Lemma compile_ranged_for_w_continued : forall A {tr mem locals functions}
          (from to: word)
          (H: if signed then in_signed_bounds (to_Z from) /\ in_signed_bounds (to_Z to)
              else in_unsigned_bounds (to_Z from) /\ in_unsigned_bounds (to_Z to))
          body (a0: A),
      let v0 := ranged_for_w from to to_Z_of_Z body a0 in
      let v := ranged_for_w_continued from to to_Z_of_Z body a0 in
      forall {P} {pred: P v -> predicate}
        (loop_pred: word -> A -> predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (from_var to_var: string) vars,

        let lp from tok_acc tr mem locals :=
            let from := ExitToken.branch (fst tok_acc) (word.sub to (word.of_Z 1)) from in
            loop_pred from (snd tok_acc) tr mem locals in

        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.get locals from_var = Some from /\
            WeakestPrecondition.dexpr mem locals to_var to) ->

        (forall from from' acc tr mem locals,
            loop_pred from acc tr mem locals ->
            loop_pred from' acc tr mem (map.put locals from_var from')) ->

        loop_pred from a0 tr mem locals ->

        ((* loop body *)
          let lp := lp in
          forall tr mem locals from'
            (Hl: to_Z from - 1 < to_Z from')
            (Hr: to_Z from' < to_Z to)
            (Hr': to_Z from' <= to_Z to),
            let tok := ExitToken.new in
            let a := ranged_for' (to_Z from) (to_Z from')
                                (w_body_tok _ _ to_Z_of_Z
                                            (wbody body pr Hr')) a0 in
            ExitToken.get (fst a) = false ->

            loop_pred from' (snd a) tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body (snd a) tok from' (conj Hl Hr)) }>)) ->
        (let v0 := v0 in
         forall tr mem locals,
           let from' := max from to in
           loop_pred from' v0 tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k \< to, v0 \> eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd.seq
          (cmd_loop_incr signed from_var to_var body_impl)
          k_impl
        <{ pred (nlet_eq (from_var :: vars) v k) }>.
    Proof.
      intros;
        eapply compile_ranged_for_w
          with (vars := vars)
               (k := fun v' (Heq: v' = v0) => k \< to, v' \> ltac:(rewrite Heq; reflexivity));
        eauto.
    Qed.

    Lemma compile_ranged_for_w_fresh : forall A {tr mem locals functions}
          (from to: word)
          (H: if signed then in_signed_bounds (to_Z from) /\ in_signed_bounds (to_Z to)
              else in_unsigned_bounds (to_Z from) /\ in_unsigned_bounds (to_Z to))
          body (a0: A),
      let v := ranged_for_w from to to_Z_of_Z body a0 in
      forall {P} {pred: P v -> predicate}
        (loop_pred: word -> A -> predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (from_var to_var: string) (from_expr to_expr: expr) vars,

        let locals1 := map.put locals from_var from in
        let locals2 := map.put locals1 to_var to in

        WeakestPrecondition.dexpr mem locals from_expr from ->
        WeakestPrecondition.dexpr mem locals1 to_expr to ->

        let lp from tok_acc tr mem locals :=
            let from := ExitToken.branch (fst tok_acc) (word.sub to (word.of_Z 1)) from in
            loop_pred from (snd tok_acc) tr mem locals in

        (forall from a0 tr mem locals,
            loop_pred from a0 tr mem locals ->
            map.get locals from_var = Some from /\
            map.get locals to_var = Some to) ->

        (forall from from' acc tr mem locals,
            loop_pred from acc tr mem locals ->
            loop_pred from' acc tr mem (map.put locals from_var from')) ->

        loop_pred from a0 tr mem locals2 ->

        ((* loop body *)
          let lp := lp in
          forall tr mem locals from'
            (Hl: to_Z from - 1 < to_Z from')
            (Hr: to_Z from' < to_Z to)
            (Hr': to_Z from' <= to_Z to),
            let tok := ExitToken.new in
            let a := ranged_for' (to_Z from) (to_Z from')
                                (w_body_tok _ _ to_Z_of_Z
                                            (wbody body pr Hr')) a0 in
            ExitToken.get (fst a) = false ->

            loop_pred from' (snd a) tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp from' (body (snd a) tok from' (conj Hl Hr)) }>)) ->
        (let v := v in
         forall tr mem locals,
           let from' := max from to in
           loop_pred from' v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd_loop_fresh signed from_var from_expr to_var to_expr body_impl k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
      intros; unfold cmd_loop_fresh.
      repeat (repeat straightline; eexists; split; eauto).
      eapply compile_ranged_for_w; eauto.
      { _split_conj; split; eauto; []; repeat straightline; eauto. }
    Qed.
  End GenericWordLoops.

  Section ranged_for_words.
    Context {A: Type}
            {tr : Semantics.trace} {m : mem} {l : locals}
            {functions : list (string * (list string * list string * cmd))}
            (from to : word).

    Definition compile_ranged_for_u :=
      @compile_ranged_for_w_fresh
        false _ word.of_Z_unsigned word_unsigned_of_Z_bracketed
        word.maxu word.unsigned_maxu A tr m l functions from to
        (conj (word.unsigned_range _) (word.unsigned_range _)).

    Definition compile_ranged_for_s :=
      @compile_ranged_for_w_fresh
        true _ word.of_Z_signed word_signed_of_Z_bracketed
        word.maxs word.signed_maxs A tr m l functions from to
        (conj (word.signed_range _) (word.signed_range _)).

    Definition compile_ranged_for_u_continued :=
      @compile_ranged_for_w_continued
        false _ word.of_Z_unsigned word_unsigned_of_Z_bracketed
        word.maxu word.unsigned_maxu A tr m l functions from to
        (conj (word.unsigned_range _) (word.unsigned_range _)).

    Definition compile_ranged_for_s_continued :=
      @compile_ranged_for_w_continued
        true _ word.of_Z_signed word_signed_of_Z_bracketed
        word.maxs word.signed_maxs A tr m l functions from to
        (conj (word.signed_range _) (word.signed_range _)).
  End ranged_for_words.

  Section Maps.
    Context {A} f f' (a: list A) v (vars: list string)
            (Hrp: acts_as_replace_nth (A := A) f f')
            (Heq: v = List.map f a).

    Lemma compile_map: forall [tr mem locals functions],
      let v := v in
      forall {P} {pred: P v -> predicate}
        (loop_pred: forall (idx: Z) (a: list A), predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (idx_var to_var: string) (to_expr: expr),

        let to := Z.of_nat (length a) in
        let locals1 := map.put locals idx_var (word.of_Z 0) in
        let locals2 := map.put locals1 to_var (word.of_Z to) in

        0 <= to < 2^width ->
        WeakestPrecondition.dexpr mem locals1 to_expr (word.of_Z to) ->

        (forall idx a0 tr mem locals,
            loop_pred idx a0 tr mem locals ->
            map.get locals idx_var = Some (word.of_Z idx) /\
            map.get locals to_var = Some (word.of_Z to)) ->

        (forall idx idx' acc tr mem locals,
            loop_pred idx acc tr mem locals ->
            loop_pred idx' acc tr mem (map.put locals idx_var (word.of_Z idx'))) ->

        loop_pred 0 a tr mem locals2 ->

        ((* loop body *)
          let lp := loop_pred in
          forall tr mem locals idx,
            0 <= idx < to ->
            let n := Z.to_nat idx in
            let a := List.map f (List.firstn n a) ++ List.skipn n a in
            loop_pred idx a tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp idx (f' a idx) }>)) ->
        (let v := v in
         forall tr mem locals,
           loop_pred to v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd_loop_fresh false idx_var (expr.literal 0) to_var to_expr body_impl k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
      rewrite Heq; intros; subst v0. revert dependent k. revert dependent pred.
      erewrite (map_as_nd_ranged_for_all f f' Hrp a).
      intros; eapply compile_nd_ranged_for_all_fresh; reflexivity || lia || eauto.
      - intros; cbn; eapply WeakestPrecondition_weaken.
        2: eapply H4 with (idx := from'); try lia; [].
        all: erewrite map_firstn_as_nd_ranged_for_all, Z2Nat.id;
          eauto using Hrp; lia.
      - intros; subst from'; rewrite Z.max_r in * by lia; eauto.
    Qed.
  End Maps.

  Section CopyingFolds.
    Context {A B} (f: A -> B -> A) (f': A -> Z -> A)
            (bs: list B) (a: A) v (vars: list string)
            (Heq: v = List.fold_left f bs a)
            (Hrp: acts_as_foldl_step f f' bs).

    Lemma compile_scalar_fold_left: forall [tr mem locals functions],
      let v := v in
      forall {P} {pred: P v -> predicate}
        (loop_pred: forall (idx: Z) (a: A), predicate)
        {k: nlet_eq_k P v} {k_impl} {body_impl}
        (idx_var to_var: string) (to_expr: expr),

        let to := Z.of_nat (length bs) in
        let locals1 := map.put locals idx_var (word.of_Z 0) in
        let locals2 := map.put locals1 to_var (word.of_Z to) in

        0 <= to < 2^width ->
        WeakestPrecondition.dexpr mem locals1 to_expr (word.of_Z to) ->

        (forall idx a0 tr mem locals,
            loop_pred idx a0 tr mem locals ->
            map.get locals idx_var = Some (word.of_Z idx) /\
            map.get locals to_var = Some (word.of_Z to)) ->

        (forall idx idx' acc tr mem locals,
            loop_pred idx acc tr mem locals ->
            loop_pred idx' acc tr mem (map.put locals idx_var (word.of_Z idx'))) ->

        loop_pred 0 a tr mem locals2 ->

        ((* loop body *)
          let lp := loop_pred in
          forall tr mem locals idx,
            0 <= idx < to ->
            let n := Z.to_nat idx in
            let a' := List.fold_left f (List.firstn n bs) a in
            loop_pred idx a' tr mem locals ->
            (<{ Trace := tr;
                Memory := mem;
                Locals := locals;
                Functions := functions }>
             body_impl
             <{ lp idx (f' a' idx) }>)) ->
        (let v := v in
         forall tr mem locals,
           loop_pred to v tr mem locals ->
           (<{ Trace := tr;
               Memory := mem;
               Locals := locals;
               Functions := functions }>
            k_impl
            <{ pred (k v eq_refl) }>)) ->
        <{ Trace := tr;
           Memory := mem;
           Locals := locals;
           Functions := functions }>
        cmd_loop_fresh false idx_var (expr.literal 0) to_var to_expr body_impl k_impl
        <{ pred (nlet_eq vars v k) }>.
    Proof.
      rewrite Heq; intros; subst v0. revert dependent k. revert dependent pred.
      erewrite (copying_fold_left_as_nd_ranged_for_all f f' bs Hrp).
      intros; eapply compile_nd_ranged_for_all_fresh; reflexivity || lia || eauto.
      - intros; cbn; eapply WeakestPrecondition_weaken.
        2: eapply H4 with (idx := from'); try lia; [].
        all: erewrite copying_fold_left_firstn_as_nd_ranged_for_all;
          eauto using Hrp; lia.
      - intros; subst from'; rewrite Z.max_r in * by lia; eauto.
    Qed.
  End CopyingFolds.
End with_parameters.

Ltac make_ranged_for_predicate from_var from_arg to_var to_val vars args tr pred locals :=
  lazymatch substitute_target from_var from_arg pred locals with
  | (?pred, ?locals) =>
    lazymatch substitute_target to_var to_val pred locals with
    | (?pred, ?locals) => make_predicate vars args tr pred locals
    end
  end.

Ltac infer_ranged_for_predicate' from_var to_var to_val argstype vars tr pred locals :=
  (** Like `make_predicate`, but with a binding for `idx` at the front. *)
  let idxtype := type of to_val in
  let val_pred :=
      constr:(fun (idx: idxtype) (args: argstype) =>
                ltac:(let f := make_ranged_for_predicate
                                from_var idx to_var to_val
                                vars args tr pred locals in
                      exact f)) in
  eval cbv beta in val_pred.

Ltac infer_ranged_for_predicate from_var to_var to_val :=
  _infer_predicate_from_context
    ltac:(infer_ranged_for_predicate' from_var to_var to_val).

Ltac make_ranged_for_continued_predicate idxvar idxarg vars args tr pred locals :=
  lazymatch substitute_target idxvar idxarg pred locals with
  | (?pred, ?locals) => make_predicate vars args tr pred locals
  end.

Ltac infer_ranged_for_continued_predicate' argstype vars tr pred locals :=
  (** Like `make_predicate`, but with a binding for `idx` at the front. *)
  match argstype with
  | \<< ?idxtype, ?argstype \>> =>
    match vars with
    | ?idxvar :: ?vars =>
      let val_pred :=
          constr:(fun (idx: idxtype) (args: argstype) =>
                    ltac:(let f := make_ranged_for_continued_predicate
                                    idxvar idx vars args tr pred locals in
                          exact f)) in
      eval cbv beta in val_pred
    end
  end.

Ltac infer_ranged_for_continued_predicate :=
  _infer_predicate_from_context infer_ranged_for_continued_predicate'.

(* FIXME why doesn't simple eapply work for these lemmas? *)

Ltac compile_ranged_for_continued :=
  lazymatch goal with
  | [ |- WeakestPrecondition.cmd _ _ _ _ _ (_ (nlet_eq _ ?v _)) ] =>
    lazymatch v with
    | (ranged_for_u_continued _ _ _ _) =>
        let lp := infer_ranged_for_continued_predicate in
        eapply compile_ranged_for_u_continued with (loop_pred := lp)
    | (ranged_for_s_continued _ _ _ _) =>
        let lp := infer_ranged_for_continued_predicate in
        eapply compile_ranged_for_s_continued with (loop_pred := lp)
    end
  end.

Ltac _compile_ranged_for locals to thm :=
  let from_v := gensym locals "from" in
  let to_v := gensym locals "to" in
  let lp := infer_ranged_for_predicate from_v to_v to in
  eapply thm with (from_var := from_v) (to_var := to_v) (loop_pred := lp).

Ltac compile_ranged_for :=
  lazymatch goal with
  | [ |- WeakestPrecondition.cmd _ _ _ _ ?locals (_ (nlet_eq _ ?v _)) ] =>
      lazymatch v with
      | (ranged_for 0%Z ?to _ _) =>
          _compile_ranged_for locals to (compile_ranged_for_fresh false)
      | (ranged_for _ ?to _ _) =>
          _compile_ranged_for locals to (compile_ranged_for_fresh true)
      | (ranged_for_u _ ?to _ _) =>
          _compile_ranged_for locals to compile_ranged_for_u
      | (ranged_for_s _ ?to _ _) =>
          _compile_ranged_for locals to compile_ranged_for_s
      end
  end.

Module LoopCompiler.
  #[export] Hint Extern 1 => compile_ranged_for_continued; shelve : compiler.
  #[export] Hint Extern 1 => compile_ranged_for; shelve : compiler.

  #[export] Hint Extern 1 (WP_nlet (nd_ranged_for_all _ _ _ _)) =>
    rewrite nd_as_ranged_for_all; shelve : compiler_cleanup.
  #[export] Hint Extern 1 (WP_nlet (ranged_for_all _ _ _ _)) =>
    rewrite ranged_for_all_as_ranged_for; shelve : compiler_cleanup.
End LoopCompiler.

Section Examples.
  Context {width: Z} {BW: Bitwidth width}.
  Context {word: word.word width} {word_ok : word.ok word}.
  Context {locals: map.map string word} {locals_ok : map.ok locals}.
  Context {mem: map.map word byte} {mem_ok : map.ok mem}.

  Section LoopInference.
    Context (tr: Semantics.trace) {A} (ptr v v' from: word) (a a': A) (R: mem -> Prop)
            (rp: word -> A -> mem -> Prop).

    Check ltac:(let t := infer_ranged_for_continued_predicate'
                          (\<< word, A, word \>>)
                          ["from"; "ptr"; "v"]
                          tr
                          (rp ptr a ⋆ R)
                          (map.put (map := locals)
                                   (map.put (map.put map.empty "v" v)
                                            "from" from) "ptr" ptr)
                in exact t).
  End LoopInference.
End Examples.
