Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop.
Require Import Coq.Lists.List Coq.ZArith.BinInt. Local Open Scope Z_scope.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.Lia.

Section Array.
  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context {value} {mem : map.map word value} {mem_ok : map.ok mem}.
  Context {T} (element : word -> T -> mem -> Prop) (size : word).
  Fixpoint array (start : word) (xs : list T) :=
    match xs with
    | nil => emp True
    | cons x xs => sep (element start x) (array (word.add start size) xs)
    end.

  Local Infix "*" := sep.

  Lemma array_cons x xs start:
    iff1 (array start (x :: xs)) (sep (element start x) (array (word.add start size) xs)).
  Proof. reflexivity. Qed.

  Lemma array_append xs ys start:
    iff1 (array start (xs ++ ys))
         (array start xs * array (word.add start (word.of_Z (word.unsigned size * Z.of_nat (length xs)))) ys).
  Proof.
    revert ys start. induction xs; intros ys start.
    - simpl.
      match goal with
      | |- iff1 _ (sep _ (array ?mid _)) => replace mid with start; cycle 1
      end.
      { eapply word.unsigned_inj.
        repeat (rewrite ?word.unsigned_add, ?word.unsigned_of_Z, ?Z.mul_0_r, ?Z.mod_0_l, ?Z.add_0_r, ?word.wrap_unsigned || unfold word.wrap); trivial. }
      cancel.
    - rewrite <- app_comm_cons. rewrite array_cons. simpl.
      specialize (IHxs ys (word.add start size)). simpl in IHxs.
      rewrite IHxs.
      cancel.
      (* TODO this step should be done by an automatic semi-canceler *)
      match goal with
      | |- iff1 (seps (array ?addr1 ys :: nil)) (seps (array ?addr2 ys :: nil)) =>
        replace addr1 with addr2; [reflexivity|]
      end.
      { eapply word.unsigned_inj.
        repeat (rewrite ?word.unsigned_add, ?word.unsigned_of_Z, ?Z.mul_0_r, ?Z.mul_1_r, ?Z.mod_0_l, ?Z.add_0_r, ?Z.mul_add_distr_l, ?word.wrap_unsigned, ?Zdiv.Zplus_mod_idemp_r, ?Zdiv.Zplus_mod_idemp_l || unfold word.wrap); trivial.
        f_equal.
        blia. }
  Qed.

  Lemma array_append_DEPRECATED xs ys start:
    iff1 (array start (xs ++ ys))
         (array start xs * array (word.add start (word.mul size (word.of_Z (Zcomplements.Zlength xs)))) ys).
  Proof.
    rewrite Zcomplements.Zlength_correct.
    etransitivity; [eapply array_append|].
    repeat Morphisms.f_equiv.
    eapply word.unsigned_inj.
    repeat (rewrite ?word.unsigned_of_Z, ?word.unsigned_mul, ?Zdiv.Zmult_mod_idemp_r || unfold word.wrap).
    reflexivity.
  Qed.

  Lemma array_index_nat xs start n :
    iff1 (array start xs)
      ( array start (firstn n xs) * (
        match hd_error (skipn n xs) with Some x => element (word.add start (word.of_Z (word.unsigned size*Z.of_nat n))) x | None => emp True end *
        array (word.add (word.add start (word.of_Z (word.unsigned size*Z.of_nat n))) size) (tl (skipn n xs)))).
  Proof.
    pose proof (firstn_skipn n xs) as H.
    remember (firstn n xs) as A in *; remember (skipn n xs) as B in *; rewrite <-H.
    etransitivity; [eapply array_append|]; eapply iff1_sep_cancel.
    destruct B; cbn [array hd_error tl]; [solve[cancel]|].
    subst A; destruct (Compare_dec.le_le_S_dec (length xs) n) as [Hle|Hle].
    { rewrite firstn_all2, <-app_nil_r in H by assumption; eapply app_inv_head in H; discriminate H. }
    rewrite firstn_length_le by blia; reflexivity.
  Qed.

  Context {default : T}.
  Lemma array_index_nat_inbounds xs start n (H : (n < length xs)%nat) :
    iff1 (array start xs)
       (array start (firstn n xs) *
       (element (word.add start (word.of_Z (word.unsigned size * Z.of_nat n))) (hd default (skipn n xs)) *
       array (word.add (word.add start (word.of_Z (word.unsigned size * Z.of_nat n))) size) (tl (skipn n xs)))).
  Proof.
    pose proof array_index_nat xs start n.
    rewrite <-(firstn_skipn n xs), app_length in H.
    destruct (skipn n xs) in *; cbn [tl hd hd_error] in *; [|assumption].
    { cbn [length] in H. rewrite PeanoNat.Nat.add_0_r in H.
      rewrite firstn_length in H. blia. }
  Qed.

  Lemma array_address_inbounds xs start a
    (Hlen : word.unsigned (word.sub a start) < Z.mul (word.unsigned size) (Z.of_nat (length xs)))
    (Hmod : word.unsigned (word.sub a start) mod (word.unsigned size) = 0)
    n (Hn : n = Z.to_nat (word.unsigned (word.sub a start) / word.unsigned size))
    : iff1 (array start xs)
      ( array start (firstn n xs) * (
        element a (hd default (skipn n xs)) *
        array (word.add a size) (tl (skipn n xs)) ) ).
  Proof.
    pose proof word.unsigned_range a.
    pose proof word.unsigned_range size.
    pose proof word.unsigned_range (word.sub a start).
    destruct (Z.eq_dec (word.unsigned size) 0) as [Hz|Hnz].
    { rewrite Hz in *. blia. }
    replace a with (word.add start (word.mul (word.of_Z (Z.of_nat n)) size)); cycle 1.
    { subst n.
      rewrite Znat.Z2Nat.id by (eapply Z.div_pos; blia).
      eapply word.unsigned_inj.
      repeat rewrite ?word.unsigned_add, ?word.unsigned_mul, ?word.unsigned_of_Z.
      repeat (rewrite ?Zdiv.Zmult_mod_idemp_l, ?Zdiv.Zmult_mod_idemp_r, ?Zdiv.Zplus_mod_idemp_r, ?Zdiv.Zplus_mod_idemp_l || unfold word.wrap).
      rewrite Z.mul_comm, <-Zdiv.Z_div_exact_full_2 by trivial.
      repeat (rewrite ?word.unsigned_sub, ?Zdiv.Zminus_mod_idemp_r, ?Zdiv.Zminus_mod_idemp_l, ?Zdiv.Zplus_mod_idemp_r, ?Zdiv.Zplus_mod_idemp_l || unfold word.wrap).
      replace (word.unsigned start + (word.unsigned a - word.unsigned start)) with (word.unsigned a) by blia.
      rewrite Z.mod_small by assumption; trivial. }
    replace (word.mul (word.of_Z (Z.of_nat n)) size) with (word.of_Z (word.unsigned size * Z.of_nat n)); cycle 1.
    { eapply word.unsigned_inj.
      repeat (rewrite ?word.unsigned_of_Z, ?word.unsigned_mul, ?Zdiv.Zmult_mod_idemp_r, ?Zdiv.Zmult_mod_idemp_l || unfold word.wrap).
      f_equal. blia. }
    eapply (array_index_nat_inbounds xs start n); subst n.
    rewrite <-Znat.Nat2Z.id.
    eapply Znat.Z2Nat.inj_lt; try eapply Z.div_pos; try blia; [].
    eapply Z.div_lt_upper_bound; blia.
  Qed.
End Array.
