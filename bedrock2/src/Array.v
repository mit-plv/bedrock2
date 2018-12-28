Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop.
Require Import Coq.Lists.List Coq.ZArith.BinInt. Local Open Scope Z_scope.
Require Import coqutil.Word.Interface coqutil.Word.Properties.

Section Array.
  Context {width : Z} {word : Word.Interface.word width} {Hwidth : 0 <= width} {word_ok : word.ok word}.
  Context {value} {mem : map.map word value} {mem_ok : map.ok mem}.
  Context {T} (element : word -> T -> mem -> Prop) (size : word).
  Fixpoint array (start : word) (xs : list T) :=
    match xs with
    | nil => emp True
    | cons x xs => sep (element start x) (array (word.add start size) xs)
    end.
  Local Infix "*" := sep.

  Lemma array_index_nat xs start n :
    iff1 (array start xs)
      ( array start (firstn n xs) * (
        match hd_error (skipn n xs) with Some x => element (word.add start (word.mul (word.of_Z (Z.of_nat n)) size)) x | None => emp True end *
        array (word.add (word.add start (word.mul (word.of_Z (Z.of_nat n)) size)) size) (tl (skipn n xs)))).
  Proof.
    set (a := (word.add start (word.mul (word.of_Z (Z.of_nat n)) size))).
    destruct (Compare_dec.le_lt_dec (length xs) n) as [H|H].
    { (* TODO(lemma): skipn_all *)
      pose proof (firstn_skipn n xs) as H0.
      rewrite firstn_all2 in * by assumption.
      rewrite <-app_nil_r in H0; apply app_inv_head in H0; rewrite H0; cbn.
      (* FIXME *) ecancel. rewrite sep_emp_True_l. ecancel. }
    rewrite <-(firstn_skipn n xs) at 1.
    replace a with (word.add start (word.mul (word.of_Z (Z.of_nat (length (firstn n xs)))) size)); cycle 1.
    { subst a. rewrite firstn_length_le by Lia.lia. trivial. }
    generalize dependent (skipn n xs); generalize dependent (firstn n xs); clear a n H xs.
    intros xs; revert start; induction xs as [|x xs]; intros start ys.
    { cbn [array hd tl app length Z.of_nat].
      destruct ys; cbn [array length hd tl hd_error]; [solve[repeat ecancel]|].
      rewrite sep_emp_True_l.
      replace (word.add start (word.mul (word.of_Z 0) size)) with start;
        [exact (RelationClasses.reflexivity _)|].
      (* ring. *) admit. }
    { rewrite <-!app_comm_cons; cbn [array length]. rewrite IHxs; clear IHxs.
      rewrite sep_assoc; eapply iff1_sep_cancel, iff1_sep_cancel.
      replace (word.add start (word.mul (word.of_Z (Z.of_nat (S (Datatypes.length xs)))) size))
        with (word.add (word.add start size) (word.mul (word.of_Z (Z.of_nat (Datatypes.length xs))) size));
        [exact (RelationClasses.reflexivity _)|].
      rewrite Znat.Nat2Z.inj_succ, <-Z.add_1_l.
      generalize (Z.of_nat (Datatypes.length xs)); intro z.
      (* ring. *) admit. }
  Admitted.

  Lemma array_index xs start i :
    iff1 (array start xs)
      ( array start (firstn (Z.to_nat (word.unsigned i)) xs) * (
        match hd_error (skipn (Z.to_nat (word.unsigned i)) xs) with Some x => element (word.add start (word.mul i size)) x |None=>emp True end *
        array (word.add (word.add start (word.mul i size)) size) (tl (skipn (Z.to_nat (word.unsigned i)) xs))) ).
  Proof.
    set (n := Z.to_nat (word.unsigned i)).
    replace i with ((word.of_Z (Z.of_nat n))); cycle 1.
    { subst n. rewrite Znat.Z2Nat.id, word.of_Z_unsigned; trivial.
      eapply word.unsigned_range. }
    eapply array_index_nat.
  Qed.

  Context (default : T).
  Lemma array_index_nat_inbounds xs start n (H : (n < length xs)%nat) :
    iff1 (array start xs)
      ( array start (firstn n xs) * (
        element (word.add start (word.mul (word.of_Z (Z.of_nat n)) size)) (hd default (skipn n xs)) *
        array (word.add (word.add start (word.mul (word.of_Z (Z.of_nat n)) size)) size) (tl (skipn n xs)))).
  Proof.
    pose proof array_index_nat xs start n.
    rewrite <-(firstn_skipn n xs), app_length in H.
    destruct (skipn n xs) in *; cbn [hd hd_error] in *; [exfalso|assumption].
    cbn [length] in H. rewrite PeanoNat.Nat.add_0_r in H.
    rewrite firstn_length in H. Lia.lia.
  Qed.

  Lemma array_index_inbounds xs start i (H : word.unsigned i < Z.of_nat (length xs)) :
    iff1 (array start xs)
      ( array start (firstn (Z.to_nat (word.unsigned i)) xs) * (
        element (word.add start (word.mul i size)) (hd default (skipn (Z.to_nat (word.unsigned i)) xs)) *
        array (word.add (word.add start (word.mul i size)) size) (tl (skipn (Z.to_nat (word.unsigned i)) xs)) ) ).
  Proof.
    pose proof array_index xs start i.
    set (n := Z.to_nat (word.unsigned i)) in *.
    rewrite <-(firstn_skipn n xs), app_length in H.
    destruct (skipn n xs) in *; cbn [hd hd_error] in *; [exfalso|assumption].
    cbn [length] in H. rewrite PeanoNat.Nat.add_0_r in H.
    cbv [n] in H. rewrite firstn_length, Znat.Nat2Z.inj_min, Znat.Z2Nat.id in H; [Lia.lia|].
    eapply word.unsigned_range.
  Qed.
End Array.
