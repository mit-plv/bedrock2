Require Import coqutil.Map.Interface coqutil.Map.Properties bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Semantics bedrock2.Array coqutil.Word.LittleEndian.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Map.Interface. (* coercions word and rep *)
Require Import coqutil.Z.div_mod_to_equations.
Import HList List PrimitivePair.
Require Import Lia.

Section Scalars.
  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context {byte : Word.Interface.word 8} {byte_ok : word.ok byte}.

  Context {mem : map.map word byte} {mem_ok : map.ok mem}.

  Definition ptsto_bytes (n : nat) (addr : word) (value : tuple byte n) : mem -> Prop :=
    array ptsto (word.of_Z 1) addr (tuple.to_list value).

  Lemma load_bytes_of_sep a n bs R m
    (Hsep : sep (ptsto_bytes n a bs) R m)
    : Memory.load_bytes n m a = Some bs.
  Proof.
    cbv [load_bytes footprint].
    revert dependent a; revert dependent R; revert dependent m; revert dependent n.
    induction n; [solve[cbn; intros []; trivial]|].
    intros [b0 bs] m R a Hsep.
    cbn in Hsep; eapply SeparationLogic.sep_assoc in Hsep.
    cbn [map.getmany_of_tuple tuple.option_all tuple.map tuple.unfoldn].
    erewrite SeparationLogic.get_sep by exact Hsep.
    setoid_rewrite IHn; [exact eq_refl|].
    unfold ptsto_bytes.
    SeparationLogic.ecancel_assumption.
  Qed.

  (*
  Lemma getmany_of_tuple_split: forall (n: nat) (m: mem) (ks: tuple word n) (vs: tuple byte n),
      map.getmany_of_tuple m ks = Some vs ->
      exists (m': mem), map.split m (map.putmany_of_tuple ks vs map.empty) m'.
  Proof.
    induction n; intros.
    - exists m. apply map.split_empty_l. reflexivity.
    - apply map.invert_getmany_of_tuple_Some in H. destruct H as [A B].
      destruct ks as [k ks]. destruct vs as [v vs]. simpl in *.
      specialize IHn with (1 := B). clear B.
      destruct IHn as [m' IH].

      (* if duplicate keys, overall lemma still holds, but can't go one-by-one *)


      assert (map.get m' k = Some v) as A'. {
        apply (map.get_split k) in IH.
        destruct IH as [[B1 B2] | [B1 B2]].
        - exfalso. rewrite A in B1.
Search "disjoint".
          Search map.get map.putmany_of_tuple.


      Search map.get map.split.

      simpl.

  Admitted.*)


  Lemma getmany_of_tuple_split: forall (n: nat) (m: mem) (ks: tuple word n) (vs: tuple byte n),
      map.getmany_of_tuple m ks = Some vs ->
      exists (m': mem), map.split m (map.putmany_of_tuple ks vs map.empty) m'.
  Proof.
    induction n; intros.
    - exists m. apply map.split_empty_l. reflexivity.
    - apply map.invert_getmany_of_tuple_Some in H. destruct H as [A B].
      specialize IHn with (1 := B).
      destruct IHn as [m' IH].
      simpl.
  Admitted.

  Lemma ptsto_bytes_putmany_of_tuple_empty: forall n a bs,
      ptsto_bytes n a bs (map.putmany_of_tuple (footprint a n) bs map.empty).
  Proof.
    induction n; intros.
    - cbv. auto.
    - unfold ptsto_bytes. simpl. unfold sep.
      specialize (IHn (word.add a (word.of_Z 1)) (pair._2 bs)).
      exists (map.put map.empty a (pair._1 bs)).
      unfold map.split.
      exists (map.putmany_of_tuple (footprint (word.add a (word.of_Z 1)) n) (pair._2 bs) map.empty).
      repeat split.
      + admit.
      + admit.
      + exact IHn.
  Admitted.

  Lemma sep_of_load_bytes{weq: Decidable.DecidableEq word}: forall (n: nat) (a: word) (bs: tuple byte n) (m: mem),
      Memory.load_bytes n m a = Some bs ->
      exists R, sep (ptsto_bytes n a bs) R m.
  Proof.
    intros.
    unfold load_bytes, ptsto_bytes in H.
    apply getmany_of_tuple_split in H. destruct H as [m' H].
    unfold sep. exists (eq m'). do 2 eexists. split; [|split; [|reflexivity]].
    - exact H.
    - apply ptsto_bytes_putmany_of_tuple_empty.
  Qed.

  Definition removemany_of_tuple: forall {n: nat}, mem -> tuple word n -> mem :=
    fix rec(n: nat): mem -> tuple word n -> mem :=
      match n as n' return mem -> tuple word n' -> mem with
      | O => fun m ks => m
      | S n' => fun m '(PrimitivePair.pair.mk k ks) => map.remove (rec n' m ks) k
      end.

  Lemma test: forall n1 n2 m a (bs1: tuple byte n1) (bs2: tuple byte n2),
      map.getmany_of_tuple m (footprint a n1) = Some bs1 ->
      map.getmany_of_tuple m (footprint (word.add a (word.of_Z (Z.of_nat n1))) n2) = Some bs2 ->
      exists R, sep (sep (ptsto_bytes n1 a bs1)
                         (ptsto_bytes n2 (word.add a (word.of_Z (Z.of_nat n1))) bs2)) R m.
  Proof.
    induction n1; intros.
    -
  Abort.

  Lemma test0: forall m a n b (bs: tuple byte n),
      map.get m a = Some b ->
      map.getmany_of_tuple m (footprint (word.add a (word.of_Z 1)) n) = Some bs ->
      exists R, sep (ptsto a b) (sep (ptsto_bytes n a bs) R) m.
  Proof.
    intros.

  Abort.

  Lemma build_getmany_of_tuple_Some: forall (n : nat) (k: word) (ks : tuple word n) (v: byte) (vs : tuple byte n) (m : mem),
       map.get m k = Some v ->
       map.getmany_of_tuple m ks = Some vs ->
       map.getmany_of_tuple m ({| pair._1 := k; pair._2 := ks |}: tuple word (S n)) = Some {| pair._1 := v; pair._2 := vs |}.
  Proof.
    intros.
    unfold map.getmany_of_tuple, tuple.option_all, tuple.map.
    rewrite H.
    change (
        match
          map.getmany_of_tuple m ks
        with
        | Some ys => Some {| pair._1 := v; pair._2 := ys |}
        | None => None
        end = Some {| pair._1 := v; pair._2 := vs |}).
    rewrite H0.
    reflexivity.
  Qed.

  Arguments Z.of_nat: simpl never.

  (*
  Lemma sep_of_getmany_of_tuple_S:
    forall (n : nat) (a: word) (vs : tuple byte (S n)) (m : mem),
      (Z.of_nat n < 2 ^ width)%Z ->
      map.getmany_of_tuple m (footprint a (S n)) = Some vs ->
      sep (ptsto a (par._1 vs)) (eq (map.remove m a)

      exists m', map.split m (map.put map.empty a (pair._1 vs)) m' /\
         map.getmany_of_tuple m' (footprint (word.add a (word.of_Z 1)) n) = Some (pair._2 vs).
*)

  Lemma invert_getmany_of_tuple_Some_footprint:
    forall (n : nat) (a: word) (vs : tuple byte (S n)) (m : mem),
      (Z.of_nat n < 2 ^ width)%Z ->
      map.getmany_of_tuple m (footprint a (S n)) = Some vs ->
      exists m', map.split m (map.put map.empty a (pair._1 vs)) m' /\
         map.getmany_of_tuple m' (footprint (word.add a (word.of_Z 1)) n) = Some (pair._2 vs).
  Proof.
    intros until 0. intros D H.
    apply map.invert_getmany_of_tuple_Some in H. destruct H as [B1 B2].
    exists (map.remove m a).
    repeat split.
    - apply map.map_ext. intros.
      pose proof (map.putmany_spec (map.put map.empty a (pair._1 vs)) (map.remove m a) k) as P.
      destruct P as [[v [A B]] | [A B]].
      + rewrite B.
        destruct (word.eqb a k) eqn: E.
        * apply word.eqb_true in E. subst k.
          rewrite map.get_remove_same in A. discriminate.
        * apply word.eqb_false in E.
          rewrite map.get_remove_diff in A by congruence. exact A.
      + rewrite B.
        destruct (word.eqb a k) eqn: E.
        * apply word.eqb_true in E. subst k.
          rewrite map.get_put_same. exact B1.
        * apply word.eqb_false in E.
          rewrite map.get_remove_diff in A by congruence.
          rewrite map.get_put_diff by congruence.
          rewrite map.get_empty. exact A.
    - unfold map.disjoint. intros.
      destruct (word.eqb a k) eqn: E.
        * apply word.eqb_true in E. subst k.
          rewrite map.get_remove_same in H0. discriminate.
        * apply word.eqb_false in E.
          rewrite map.get_put_diff in H by congruence.
          rewrite map.get_empty in H. discriminate.
    - simpl in B2.
      clear -B2 mem_ok word_ok D. destruct vs as [v vs]. simpl in *.
      assert (1 + Z.of_nat n <= 2 ^ width)%Z as X by lia.
      revert B2 D X.
      generalize 1%Z as d.
      clear v.
      revert n a vs.
      induction n; intros; simpl in *.
      + destruct vs. reflexivity.
      + apply map.invert_getmany_of_tuple_Some in B2. simpl in B2. destruct B2 as [A B].
        destruct vs as [v vs]. simpl in *.
        apply build_getmany_of_tuple_Some.
        * rewrite map.get_remove_diff; [assumption|].
          admit. (* from X *)
        * specialize (IHn a vs (d + 1)%Z).
          replace (word.add a (word.of_Z (d + 1)))
             with (word.add (word.add a (word.of_Z d)) (word.of_Z 1)) in IHn by admit.
          apply IHn.
          { assumption. }
          { lia. }
          { lia. }
  Admitted.

  Lemma sep_of_load_bytes_aux: forall (n: nat) (a: word) (bs: tuple byte n) (m: mem) (Q: mem -> Prop),
      sep (fun m0 => Memory.load_bytes n m0 a = Some bs) Q m ->
      exists R, sep (ptsto_bytes n a bs) (sep R Q) m.
  Proof.
    cbv [load_bytes footprint]. unfold ptsto_bytes.
    induction n; intros.
    - cbv [ptsto_bytes array tuple.to_list].
      simpl in *. unfold map.getmany_of_tuple, tuple.option_all in H.
      destruct H as (mp & mq & A & B & C).
      exists (eq mp).
      apply sep_emp_l. split; auto.
      unfold sep. eauto.
    - unfold sep in H.
      destruct H as (mp & mq & A & B & C).
      apply invert_getmany_of_tuple_Some_footprint in B. 2: admit.
      destruct B as (mo & B1 & B2).
      destruct bs as [b bs]. simpl in *.
      specialize (IHn (word.add a (word.of_Z 1)) bs m (sep Q (ptsto a b))).
      destruct IHn as [R IH].
      + match goal with
        | |- sep ?BS (sep Q ?P) m => assert (sep (sep P BS) Q m); [|ecancel_assumption]
        end.
        unfold sep, ptsto, footprint in *. eauto 10.
      + exists R.
        ecancel_assumption.
  Admitted.

  Lemma sep_of_load_bytes'': forall (n: nat) (a: word) (bs: tuple byte n) (m: mem),
      Memory.load_bytes n m a = Some bs ->
      exists R, sep (ptsto_bytes n a bs) R m.
  Proof.
    intros.
    pose proof (sep_of_load_bytes_aux n a bs m (emp True)) as P.
    destruct P as [R P].
    - apply sep_comm. apply sep_emp_l. auto.
    - exists R. ecancel_assumption.
  Qed. (* so far, this looks like the best *)

  Lemma sep_of_load_bytes'{weq: Decidable.DecidableEq word}: forall (n: nat) (a: word) (bs: tuple byte n) (m: mem),
      Memory.load_bytes n m a = Some bs ->
      exists R, sep (ptsto_bytes n a bs) R m.
  Proof.
    cbv [load_bytes footprint]. unfold ptsto_bytes.
    induction n; intros.
    - exists (eq m).
      cbv [ptsto_bytes array tuple.to_list].
      apply sep_emp_l. auto.
    - apply map.invert_getmany_of_tuple_Some in H. simpl in H. destruct H as [A B].

      apply sep_get in A.
      specialize IHn with (1 := B). clear B.
      destruct IHn as [R IH].
      unfold ptsto_bytes in *. simpl.
      set (Q := (array ptsto (word.of_Z 1) (word.add a (word.of_Z 1))
                       (tuple.to_list (PrimitivePair.pair._2 bs)))) in *.
      set (P := (ptsto a (PrimitivePair.pair._1 bs))) in *.
      set (R' := (eq (map.remove m a))) in *.
      exists (eq (removemany_of_tuple m (footprint a (S n)))).
      unfold sep.
      exists (map.putmany_of_tuple (footprint a (S n)) bs map.empty).
      eexists. repeat split.
      + admit.
      + admit.
      + exists (map.put map.empty a (PrimitivePair.pair._1 bs)).
        exists (map.putmany_of_tuple (footprint (word.add a (word.of_Z 1)) n)
                                     (PrimitivePair.pair._2 bs)
                                     map.empty).
        repeat split.
        * admit.
        * admit.
        * subst Q.
          admit.
  Admitted.

  Lemma unchecked_store_bytes_of_sep(a: word)(n: nat)(oldbs bs: tuple byte n)(R: mem -> Prop)(m: mem)
    (Hsep : sep (ptsto_bytes n a oldbs) R m)
    : sep (ptsto_bytes n a bs) R (Memory.unchecked_store_bytes n m a bs).
  Proof.
    revert dependent a; revert dependent R; revert dependent m; revert dependent bs; revert dependent oldbs; revert dependent n.
    induction n; [solve[cbn; intros []; trivial]|].
    intros [oldb0 oldbs] [b0 bs] m R a Hsep.
    unshelve epose proof (IHn oldbs bs (map.put m a b0) (sep (ptsto a b0) R) (word.add a (word.of_Z 1)) _) as IHn2; clear IHn; [|clear Hsep].
    - cbn in Hsep |- *; eapply SeparationLogic.sep_assoc in Hsep.
      unshelve epose proof sep_put _ _ b0 _ _ _ Hsep as Hsep2; clear Hsep.
      + exact Properties.word.eq_or_neq.
      + ecancel_assumption.
    - cbv [unchecked_store_bytes footprint] in *; cbn.
      ecancel_assumption.
  Qed.

  Lemma store_bytes_post_of_sep(a: word)(n: nat)(oldbs bs: tuple byte n)(R post: mem -> Prop)(m: mem)
    (Hsep : sep (ptsto_bytes n a oldbs) R m)
    (Hpost : forall m, sep (ptsto_bytes n a bs) R m -> post m)
    : exists m1, Memory.store_bytes n m a bs = Some m1 /\ post m1.
  Proof.
    cbv [store_bytes]. erewrite load_bytes_of_sep; eauto using unchecked_store_bytes_of_sep.
  Qed.

End Scalars.
