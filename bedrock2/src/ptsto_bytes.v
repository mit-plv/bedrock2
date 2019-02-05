Require Import coqutil.Map.Interface coqutil.Map.Properties bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Semantics bedrock2.Array.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Map.Interface.
Require Import coqutil.Z.div_mod_to_equations.
Import HList List PrimitivePair.
Require Import Lia.
Require Import Coq.ZArith.ZArith.

Open Scope Z_scope.

(* TODO move *)
Local Unset Universe Polymorphism. (* for Add Ring *)
Module word.
  Section WordLemmas.
    Context {width: Z} {word: word.word width} {word_ok: word.ok word}.
    Add Ring wring: (@word.ring_theory width word word_ok).
    Lemma add_assoc: forall (x y z: word), word.add x (word.add y z) = word.add (word.add x y) z.
    Proof. intros. ring. Qed.
  End WordLemmas.
End word.
Set Universe Polymorphism.


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
      assert (0 < 1) as Y by lia.
      assert (1 + Z.of_nat n <= 2 ^ width)%Z as X by lia. clear D.
      revert Y X B2.
      generalize 1%Z as d.
      clear v.
      revert n a vs.
      induction n; intros; simpl in *.
      + destruct vs. reflexivity.
      + apply map.invert_getmany_of_tuple_Some in B2. simpl in B2. destruct B2 as [A B].
        destruct vs as [v vs]. simpl in *.
        apply build_getmany_of_tuple_Some.
        * rewrite map.get_remove_diff; [assumption|].
          clear -X Y word_ok.
          intro C.
          apply (f_equal word.unsigned) in C.
          rewrite word.unsigned_add in C.
          rewrite <- word.wrap_unsigned in C at 2.
          apply Z.sub_move_0_r in C.
          apply (f_equal (fun x => x mod (2 ^ width))) in C.
          change (0 mod 2 ^ width) with 0 in C.
          rewrite <- Zminus_mod in C.
          rewrite Z.add_simpl_l in C.
          rewrite word.unsigned_of_Z in C.
          rewrite Z.mod_mod in C by lia.
          apply Z.mod_divide in C; [|lia].
          unfold Z.divide in C.
          destruct C as [k C].
          subst d.
          assert (0 < 2 ^ width). {
            pose proof word.width_pos.
            apply Z.pow_pos_nonneg; lia.
          }
          assert (0 < k) by nia.
          nia.
        * specialize (IHn a vs (d + 1)%Z).
          replace (word.add a (word.of_Z (d + 1)))
            with (word.add (word.add a (word.of_Z d)) (word.of_Z 1)) in IHn.
          { apply IHn; lia || assumption. }
          { rewrite (morph_add word.ring_morph). rewrite word.add_assoc. reflexivity. }
  Qed.

  Lemma sep_of_load_bytes_aux: forall (n: nat) (a: word) (bs: tuple byte n) (m: mem) (Q: mem -> Prop),
      Z.of_nat n <= 2 ^ width ->
      sep (fun m0 => Memory.load_bytes n m0 a = Some bs) Q m ->
      exists R, sep (ptsto_bytes n a bs) (sep R Q) m.
  Proof.
    cbv [load_bytes footprint]. unfold ptsto_bytes.
    induction n; intros.
    - cbv [ptsto_bytes array tuple.to_list].
      simpl in *. unfold map.getmany_of_tuple, tuple.option_all in H0.
      destruct H0 as (mp & mq & A & B & C).
      exists (eq mp).
      apply sep_emp_l. split; auto.
      unfold sep. eauto.
    - unfold sep in H0.
      destruct H0 as (mp & mq & A & B & C).
      apply invert_getmany_of_tuple_Some_footprint in B; [|lia].
      destruct B as (mo & B1 & B2).
      destruct bs as [b bs]. simpl in *.
      specialize (IHn (word.add a (word.of_Z 1)) bs m (sep Q (ptsto a b))).
      destruct IHn as [R IH].
      + lia.
      + match goal with
        | |- sep ?BS (sep Q ?P) m => assert (sep (sep P BS) Q m); [|ecancel_assumption]
        end.
        unfold sep, ptsto, footprint in *. eauto 10.
      + exists R.
        ecancel_assumption.
  Qed.

  (* The side condition is actually needed: If n was bigger than 2^width,
     ptsto_bytes would star together the same address more than once. *)
  Lemma sep_of_load_bytes: forall (n: nat) (a: word) (bs: tuple byte n) (m: mem),
      Z.of_nat n <= 2 ^ width ->
      Memory.load_bytes n m a = Some bs ->
      exists R, sep (ptsto_bytes n a bs) R m.
  Proof.
    intros.
    pose proof (sep_of_load_bytes_aux n a bs m (emp True)) as P.
    destruct P as [R P].
    - assumption.
    - apply sep_comm. apply sep_emp_l. auto.
    - exists R. ecancel_assumption.
  Qed.

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

  Lemma store_bytes_of_sep(a: word)(n: nat)(oldbs bs: tuple byte n)(R post: mem -> Prop)(m: mem)
    (Hsep : sep (ptsto_bytes n a oldbs) R m)
    (Hpost : forall m, sep (ptsto_bytes n a bs) R m -> post m)
    : exists m1, Memory.store_bytes n m a bs = Some m1 /\ post m1.
  Proof.
    cbv [store_bytes]. erewrite load_bytes_of_sep; eauto using unchecked_store_bytes_of_sep.
  Qed.

End Scalars.
