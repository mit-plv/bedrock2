Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Memory.
Require Import Coq.Lists.List Coq.ZArith.BinInt. Local Open Scope Z_scope.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Tactics.eplace.

Section Array.
  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context {value} {mem : map.map word value} {mem_ok : map.ok mem}.
  Context {T} (element : word -> T -> mem -> Prop) (size : word).
  Fixpoint array (start : word) (xs : list T) :=
    match xs with
    | nil => emp True
    | cons x xs => sep (element start x) (array (word.add start size) xs)
    end.

  Local Open Scope sep_scope.

  Lemma array_cons x xs start:
    iff1 (array start (x :: xs)) (sep (element start x) (array (word.add start size) xs)).
  Proof. reflexivity. Qed.

  Lemma array_nil start:
    iff1 (array start nil) (emp True).
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

  Lemma array_append' xs ys start:
    iff1 (array start (xs ++ ys))
         (array start xs * array (word.add start
                                           (word.mul size (word.of_Z (Z.of_nat (length xs))))) ys).
  Proof.
    etransitivity; [eapply array_append|].
    repeat Morphisms.f_equiv.
    eapply word.unsigned_inj.
    repeat (rewrite ?word.unsigned_of_Z, ?word.unsigned_mul, ?Zdiv.Zmult_mod_idemp_r || unfold word.wrap).
    reflexivity.
  Qed.

  Lemma list__tl_skipn {A} n (xs : list A) : tl (skipn n xs) = skipn (S n) xs.
  Proof. revert xs; induction n, xs; auto; []; eapply IHn. Qed.

  Lemma array_index_nat xs start n :
    iff1 (array start xs)
      ( array start (firstn n xs) * (
        match hd_error (skipn n xs) with Some x => element (word.add start (word.of_Z (word.unsigned size*Z.of_nat n))) x | None => emp True end *
        array (word.add (word.add start (word.of_Z (word.unsigned size*Z.of_nat n))) size) (skipn (S n) xs))).
  Proof.
    pose proof (firstn_skipn n xs) as H.
    rewrite <-!list__tl_skipn.
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
       array (word.add (word.add start (word.of_Z (word.unsigned size * Z.of_nat n))) size) (skipn (S n) xs))).
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
        array (word.add a size) (skipn (S n) xs) ) ).
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
    eplace (word.mul (word.of_Z (Z.of_nat n)) size) with (word.of_Z (word.unsigned size * Z.of_nat n)).
    { eapply word.unsigned_inj.
      repeat (rewrite ?word.unsigned_of_Z, ?word.unsigned_mul, ?Zdiv.Zmult_mod_idemp_r, ?Zdiv.Zmult_mod_idemp_l || unfold word.wrap).
      f_equal. blia. }
    eapply (array_index_nat_inbounds xs start n); subst n.
    rewrite <-Znat.Nat2Z.id.
    eapply Znat.Z2Nat.inj_lt; try eapply Z.div_pos; try blia; [].
    eapply Z.div_lt_upper_bound; blia.
  Qed.
End Array.

Section ByteArray.
  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context {mem : map.map word byte} {mem_ok : map.ok mem}.
  Local Notation array := (array (mem:=mem) ptsto (word.of_Z 1)).
  Local Infix "*" := sep.

  Lemma bytearray_address_inbounds xs (start : word) a
    (Hlen : word.unsigned (word.sub a start) < Z.of_nat (length xs))
    (i := Z.to_nat (word.unsigned (word.sub a start)))
    : iff1 (array start xs)
      (array start (firstn i xs) * (
        ptsto a (hd (byte.of_Z 0) (skipn i xs)) *
        array (word.add a (word.of_Z 1)) (skipn (S i) xs) ) ).
  Proof.
    eapply array_address_inbounds;
      rewrite ?word.unsigned_of_Z_1, ?Z.mul_1_l, ?Z.mod_1_r, ?Z.div_1_r; auto.
  Qed.

  Lemma bytearray_index_inbounds xs (start iw : word)
    (Hlen : word.unsigned iw < Z.of_nat (length xs))
    (i := Z.to_nat (word.unsigned iw))
    : iff1 (array start xs)
      (array start (firstn i xs) * (
        ptsto (word.add start iw) (hd (byte.of_Z 0) (skipn i xs)) *
        array (word.add (word.add start iw) (word.of_Z 1)) (skipn (S i) xs) ) ).
  Proof.
    rewrite (bytearray_address_inbounds xs start (word.add start iw));
    replace (word.sub (word.add start iw) start) with iw; try (reflexivity || assumption).
    all : rewrite word.word_sub_add_l_same_l; trivial.
  Qed.

  Lemma bytearray_append xs ys start :
    iff1 (array start (xs ++ ys))
         (array start xs * array (word.add start (word.of_Z (Z.of_nat (length xs)))) ys).
  Proof.
    replace (Z.of_nat (length xs))
       with (Z.mul (word.unsigned (word.of_Z 1 : word)) (Z.of_nat (length xs)));
      auto using array_append; []; rewrite word.unsigned_of_Z_1; blia.
  Qed.

  Lemma bytearray_index_merge xs ys (start i : word)
        (H : word.unsigned i = (Z.of_nat (length xs)))
    : iff1 (array start xs * array (word.add start i) ys)
           (array start (xs ++ ys)).
  Proof.
    pose proof word.of_Z_unsigned i as HH; rewrite H in HH.
    subst i; symmetry; apply bytearray_append.
  Qed.

  (** [anybytes] *)
  Import Map.Properties Znat.
  Local Arguments Z.of_nat: simpl never.

  Lemma array_1_to_of_disjoint_list_zip: forall bs m (addr: word),
      array  addr bs m ->
      map.of_disjoint_list_zip (Memory.ftprint addr (Z.of_nat (List.length bs))) bs = Some m.
  Proof.
    unfold map.of_disjoint_list_zip.
    induction bs; intros.
    - simpl in *. unfold emp in *. intuition congruence.
    - simpl in *. unfold sep in *. destruct H as (?&?&(?&Hlr)&?&?).
      specialize IHbs with (1 := ltac:(eassumption)). subst.
      match goal with H:ptsto _ _ ?x |- _ => unfold ptsto in H; subst x end.
      unfold Memory.ftprint in *. rewrite Nat2Z.id in *. simpl.
      rewrite IHbs.
      destruct (map.get _ addr) eqn:?.
      + unfold map.disjoint in *. specialize (Hlr addr).
        rewrite map.get_put_same in Hlr.
        exfalso. eapply Hlr; eauto.
      + f_equal.
        rewrite map.putmany_comm by assumption.
        rewrite <- map.put_putmany_commute.
        f_equal.
        symmetry. apply map.putmany_empty_r.
  Qed.

  Lemma array_1_to_anybytes: forall bs m (addr: word),
      array  addr bs m ->
      Memory.anybytes addr (Z.of_nat (List.length bs)) m.
  Proof.
    unfold Memory.anybytes.
    intros. eauto using array_1_to_of_disjoint_list_zip.
  Qed.

  Lemma of_disjoint_list_zip_to_array_1: forall n (addr: word) bs m,
      map.of_disjoint_list_zip (Memory.ftprint addr (Z.of_nat n)) bs = Some m ->
      array  addr bs m.
  Proof.
    induction n; intros.
    - change (Z.of_nat 0) with 0 in *. unfold Memory.ftprint, map.of_disjoint_list_zip in *. simpl in *.
      destruct bs eqn:?; simpl; subst; unfold emp; intuition congruence.
    - unfold Memory.ftprint, map.of_disjoint_list_zip in H.
      rewrite Nat2Z.id in H.
      simpl in H.
      do 3 match type of H with match ?x with _ => _ end = _ => destruct x eqn:?; try discriminate end.
      inversion H; subst; clear H.
      eapply sep_on_undef_put. 1: assumption. apply IHn. unfold map.of_disjoint_list_zip, Memory.ftprint.
      rewrite Nat2Z.id.
      eassumption.
  Qed.

  Lemma anybytes_to_array_1: forall m (addr: word) n,
      Memory.anybytes addr n m ->
      exists bs, array  addr bs m /\ List.length bs = Z.to_nat n.
  Proof.
    unfold Memory.anybytes.
    intros.
    destruct H as (?&?).
    assert (n < 0 \/ 0 <= n) as C by blia. destruct C as [C | C]. {
      destruct n; try blia.
      unfold Memory.ftprint in H.
      rewrite Z2Nat.inj_neg in H.
      simpl in *.
      unfold map.of_disjoint_list_zip in H. simpl in H. destruct x; try discriminate.
      exists nil. simpl. unfold emp. intuition congruence.
    }
    eexists.
    epose proof of_disjoint_list_zip_to_array_1 (Z.to_nat n) addr _ m as P.
    rewrite Z2Nat.id in P by assumption. split; eauto.
    unfold Memory.ftprint in H.
    apply map.of_disjoint_list_zip_length in H.
    rewrite List.length_unfoldn in H.
    blia.
  Qed.
End ByteArray.
