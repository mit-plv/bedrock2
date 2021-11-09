Require Export
        Rupicola.Lib.Api
        Rupicola.Lib.Arrays
        Rupicola.Lib.Loops
        Rupicola.Lib.WordNotations
        Rupicola.Examples.Net.IPChecksum.Spec.
Require Export
        bedrock2.BasicC32Semantics.

Coercion co_word_of_Z := word.of_Z (word := word).
Coercion co_word_of_byte (b: byte) : word := word_of_byte b.

Definition ip_checksum_upd (chk16: word) (b0 b1: byte) :=
  let/n w16 := b0 |w (b1 <<w 8) in
  let/n chk17 := chk16 +w w16 in
  let/n chk16 := (chk17 &w 0xffff) +w (chk17 >>w 16) in
  chk16.

(* TODO: make a variant that accumulate carries until the end *)
Definition ip_checksum_impl (bs: list byte) : word :=
  let/n chk16 := 0xffff in

  (* Main loop *)
  let/n chk16 :=
    nd_ranged_for_all
      0 (Z.of_nat (List.length bs) / 2)
      (fun chk16 idx =>
         let/n b0 := ListArray.get bs (2 * idx) in
         let/n b1 := ListArray.get bs (2 * idx + 1) in
         let/n chk16 := ip_checksum_upd chk16 b0 b1 in
         chk16) chk16 in

  (* Final iteration *)
  let/n chk16 := if Z.odd (Z.of_nat (List.length bs)) then
                  let/n b0 := ListArray.get bs (Z.of_nat (List.length bs) - 1) in
                  let/n chk16 := ip_checksum_upd chk16 b0 (Byte.x00) in
                  chk16
                else chk16 in

  let/n chk16 := (~w chk16) &w 0xffff in
  chk16.

Section Properties.
  Lemma Z_div_eucl_unique a b q q' r r':
    0 <= r < b \/ b < r <= 0 ->
    0 <= r' < b \/ b < r' <= 0 ->
    a = b * q + r ->
    a = b * q' + r' ->
    (q = q' /\ r = r').
  Proof.
    intros Hr Hr' Hq Hq';
      erewrite (Z.div_unique a b q r Hr Hq);
      erewrite (Z.div_unique a b q' r' Hr' Hq');
      erewrite (Z.mod_unique a b q r Hr Hq);
      erewrite (Z.mod_unique a b q' r' Hr' Hq');
      split; reflexivity.
  Qed.

  Lemma Nat2Z_inj_div_mod a b:
    Z.of_nat (a / b) = Z.of_nat a / Z.of_nat b /\
    Z.of_nat (a mod b) = Z.of_nat a mod Z.of_nat b.
  Proof.
    destruct (Nat.eq_dec b 0) as [->|].
    - destruct a; split; reflexivity.
    - pose (q := (a / b)%nat).
      pose (r := (a mod b)%nat).
      assert (a = b * q + r)%nat as Hnat by (apply Nat_mod_eq'; lia).
      pose (zq := Z.of_nat a / Z.of_nat b).
      pose (zr := Z.of_nat a mod Z.of_nat b).
      assert (Z.of_nat a = Z.of_nat b * zq + zr) as Hz by (apply Z_mod_eq'; lia).
      apply (f_equal Z.of_nat) in Hnat.
      rewrite Nat2Z.inj_add, Nat2Z.inj_mul in Hnat.
      pose proof Nat.mod_bound_pos a b ltac:(lia) ltac:(lia).
      pose proof Z.mod_bound_or (Z.of_nat a) (Z.of_nat b).
      eapply Z_div_eucl_unique; try eassumption.
      all: try lia.
  Qed.

  Lemma Nat2Z_inj_div a b:
    Z.of_nat (a / b) = Z.of_nat a / Z.of_nat b.
  Proof. apply (Nat2Z_inj_div_mod a b). Qed.

  Lemma Nat2Z_inj_mod a b:
    Z.of_nat (a mod b) = Z.of_nat a mod Z.of_nat b.
  Proof. apply (Nat2Z_inj_div_mod a b). Qed.

  Lemma z_range_add from len:
    z_range from (from + len) = z_range' from (Z.to_nat len).
  Proof. unfold z_range; do 2 f_equal; lia. Qed.

  Lemma Nat2Z_inj_odd : forall n,
    Z.odd (Z.of_nat n) = Nat.odd n.
  Proof.
    apply Nat.pair_induction.
    - intros ?? ->; reflexivity.
    - reflexivity.
    - reflexivity.
    - intros; rewrite !Nat2Z.inj_succ, Z.odd_succ_succ. eassumption.
  Qed.

  Lemma Natmod_odd: forall a : nat,
      (a mod 2 = if Nat.odd a then 1 else 0)%nat.
  Proof.
    apply Nat.pair_induction.
    - intros ?? ->; reflexivity.
    - reflexivity.
    - reflexivity.
    - intros.
      replace (S (S n)) with (n + 1 * 2)%nat at 1 by lia.
      rewrite Nat.mod_add by lia.
      eassumption.
  Qed.

  Lemma Natodd_mod : forall a : nat,
      (Nat.odd a = negb (a mod 2 =? 0))%nat.
  Proof.
    intros; rewrite Natmod_odd.
    destruct Nat.odd; reflexivity.
  Qed.

  Lemma nat_div2_spec n:
    ((n = 2 * (n / 2) /\ n mod 2 = 0) \/
     (n = 2 * (n / 2) + 1 /\ n mod 2 = 1))%nat.
  Proof.
    pose proof Nat.mod_bound_pos n 2 ltac:(lia) ltac:(lia).
    pose proof (Nat_mod_eq' n 2 ltac:(lia)).
    assert ((n mod 2 = 0) \/ (n mod 2 = 1))%nat as [Heq | Heq] by lia;
      rewrite Heq in *; lia.
  Qed.

  Lemma nd_ranged_for_all_combine2 {A} (f: A -> byte -> byte -> A) (bs: list byte) n acc:
    (n >= length bs)%nat ->
    (let acc := nd_ranged_for_all
                 0 (Z.of_nat n / 2)
                 (fun acc idx =>
                    f acc
                      (ListArray.get bs (2 * idx))
                      (ListArray.get bs (2 * idx + 1)))
                 acc in
     if Z.odd (Z.of_nat n) then f acc (ListArray.get bs (Z.of_nat n - 1)) default
     else acc) =
      (nd_ranged_for_all
         0 (Z.of_nat (Nat.div_up n 2))
         (fun acc idx =>
            f acc
              (ListArray.get bs (2 * idx))
              (ListArray.get bs (2 * idx + 1)))
         acc).
  Proof.
    intros.
    rewrite div_up_eqn.
    rewrite Nat2Z.inj_add.
    rewrite <- !fold_left_as_nd_ranged_for_all.
    rewrite (z_range_app 0 (Z.of_nat (n / 2)) (_ + _)) by lia.
    rewrite fold_left_app.
    rewrite Nat2Z_inj_div.
    set (fold_left _ (z_range 0 _) _) as prefix.
    rewrite z_range_add, Nat2Z.id.
    rewrite Nat2Z_inj_odd, Natodd_mod.
    destruct (nat_div2_spec n) as [(Heq, ->) | (Heq, ->)];
      cbn [Nat.eqb negb z_range' List.fold_left].
    - reflexivity.
    - rewrite <- Nat2Z_inj_div.
      f_equal.
      + f_equal; lia.
      + unfold ListArray.get, cast, Convertible_Z_nat; rewrite nth_overflow by lia;
          reflexivity.
  Qed.

  Lemma fold_left_push_fn {A A' B}
        (f: A -> B -> A)
        (f': A' -> B -> A')
        (g: A -> A')
        (P: A -> Prop):
    forall (l: list B),
      (forall a0 a, List.In a l -> P a0 -> P (f a0 a)) ->
      (forall a0 a, List.In a l -> P a0 -> g (f a0 a) = f' (g a0) a) ->
      forall (a0: A),
        P a0 ->
        g (fold_left f l a0) = fold_left f' l (g a0).
  Proof.
    induction l; simpl; intros HP Hg a0 Pa0.
    - reflexivity.
    - rewrite IHl, Hg; eauto.
  Qed.

  Definition word_onec_add16 w1 w2 :=
    let sum := word.add (word := word) w1 w2 in
    word.add (word.and sum (word.of_Z 65535)) (word.sru sum (word.of_Z 16)).

  Lemma word_unsigned_onec_add w1 w2:
    let z1 := word.unsigned w1 in
    let z2 := word.unsigned w2 in
    0 <= z1 < 2 ^ 16 ->
    0 <= z2 < 2 ^ 16 ->
    word.unsigned (word_onec_add16 w1 w2) =
    onec_add16 z1 z2.
  Proof.
    intros; unfold onec_add16, word_onec_add16.
    pose proof Z_land_leq_right (z1 + z2) 0xffff ltac:(lia) ltac:(lia).
    pose proof Z_shiftr_add_carry 16 16 z1 z2 ltac:(lia) ltac:(lia) ltac:(lia).

    all: subst z1 z2.
    repeat (rewrite ?word.unsigned_add, ?word.unsigned_and_nowrap;
            rewrite ?word.unsigned_sru_shamtZ by lia;
            rewrite ?word.unsigned_of_Z_nowrap, ?word.Z_land_wrap_l by lia).
    rewrite_strat (repeat (innermost word.wrap_small)).

    all: lia.
  Qed.

  Lemma word_unsigned_onec_add' z1 z2:
    0 <= z1 < 2 ^ 16 ->
    0 <= z2 < 2 ^ 16 ->
    onec_add16 z1 z2 =
    word.unsigned (word_onec_add16 (word.of_Z z1) (word.of_Z z2)).
  Proof.
    intros; rewrite word_unsigned_onec_add;
      rewrite !word.unsigned_of_Z_nowrap; try lia.
  Qed.

  Lemma word_morph_onec_add z1 z2:
    0 <= z1 < 2 ^ 16 ->
    0 <= z2 < 2 ^ 16 ->
    word.of_Z (onec_add16 z1 z2) = word_onec_add16 (word.of_Z z1) (word.of_Z z2).
  Proof.
    pose proof onec_add16_loose_bounds z1 z2.
    intros; apply word.unsigned_inj;
      rewrite word_unsigned_onec_add;
      rewrite !word.unsigned_of_Z_nowrap; try lia.
  Qed.

  Lemma nth_chunk {A} k (Hk: (k <> 0)%nat) (bs: list A) i d
        (Hi : (i < Nat.div_up (length bs) k)%nat) :
    nth i (chunk k bs) d = firstn k (skipn (i*k) bs).
  Proof.
    pose proof nth_error_chunk k Hk bs i Hi as Hn.
    eapply nth_error_nth in Hn; eassumption.
  Qed.

  Lemma nth_seq len: forall i start d,
    (i < len)%nat ->
    nth i (seq start len) d = (i + start)%nat.
  Proof.
    induction len; destruct i; intros; simpl; try lia.
    rewrite IHlen; lia.
  Qed.

  Lemma nth_inj {A} n : forall (l l': list A) d,
    length l = n ->
    length l' = n ->
    (forall i, (i < n)%nat -> nth i l d = nth i l' d) ->
    l = l'.
  Proof.
    induction n; destruct l, l'; cbn [List.length]; intros * ?? Hi; try lia.
    - reflexivity.
    - f_equal.
      + apply (Hi 0%nat ltac:(lia)).
      + eapply IHn; eauto; intros i0 Hi0.
        apply (Hi (S i0)%nat ltac:(lia)).
  Qed.

  Lemma nth_repeat {A} (a d: A): forall n i,
      (i < n)%nat ->
      nth i (repeat a n) d = a.
  Proof.
    induction n; destruct i; simpl; intros; try lia.
    - reflexivity.
    - apply IHn; lia.
  Qed.

  Lemma nth_repeat_default {A} (d: A): forall n i,
      nth i (repeat d n) d = d.
  Proof.
    intros; destruct (Nat.lt_ge_cases i n).
    - rewrite nth_repeat by lia; reflexivity.
    - rewrite nth_overflow by (rewrite repeat_length; lia); reflexivity.
  Qed.

  Lemma map_seq_nth_slice {A} (l: list A) (d: A) :
    forall len start,
      List.map (fun idx => nth idx l d) (seq start len) =
      List.firstn len (List.skipn start l) ++
      repeat d (start + len - Nat.max start (List.length l)).
  Proof.
    intros.
    eapply @nth_inj with (d := d); intros.
    - rewrite map_length, seq_length; reflexivity.
    - rewrite app_length, firstn_length, repeat_length, skipn_length; lia.
    - destruct (Nat.lt_ge_cases i (List.length (List.firstn len (List.skipn start l))));
        [rewrite app_nth1 by lia | rewrite app_nth2 by lia].
      all: rewrite <- nth_nth_nth_map with (dn := List.length l) by lia.
      all: rewrite nth_seq by lia.
      + rewrite nth_firstn, nth_skipn by lia; reflexivity.
      + rewrite firstn_length, skipn_length in *.
        rewrite nth_overflow, nth_repeat_default by lia.
        reflexivity.
  Qed.

  Lemma map_seq_nth_slice_le {A} (l: list A) (d: A) :
    forall len start,
      (start + len <= List.length l)%nat ->
      List.map (fun idx => nth idx l d) (seq start len) =
      List.firstn len (List.skipn start l).
  Proof.
    intros; rewrite map_seq_nth_slice.
    replace (_ + _ - _)%nat with 0%nat by lia; simpl.
    rewrite app_nil_r; reflexivity.
  Qed.

  Lemma le_combine_nth_chunk n (bs: list byte) idx dd:
    n <> 0%nat ->
    (idx < Nat.div_up (Datatypes.length bs) n)%nat ->
    le_combine (nth idx (chunk n bs) dd) =
    le_combine (List.map (fun idx => nth idx bs Byte.x00) (seq (idx * n) n)).
  Proof.
    intros.
    rewrite nth_chunk by assumption.
    rewrite map_seq_nth_slice, le_combine_app_0.
    reflexivity.
  Qed.

  Lemma In_map_combine_in_bounds n (Hn: n <> 0%nat) bs a:
    In a (List.map le_combine (chunk n bs)) ->
    0 <= a < 2 ^ (8 * Z.of_nat n).
  Proof.
    intros; eapply (Forall_In (Forall_le_combine_in_bounds n bs ltac:(lia)));
      eassumption.
  Qed.

  Lemma ip_checksum_impl_ok bs:
    ip_checksum_impl bs = word.of_Z (ip_checksum bs).
  Proof.
    unfold ip_checksum, ip_checksum_impl, nlet, co_word_of_byte, co_word_of_Z.
    rewrite nd_ranged_for_all_combine2 by lia.
    rewrite <- fold_left_as_nd_ranged_for_all.
    rewrite word.morph_and, word.morph_not.
    erewrite fold_left_push_fn
      with (f' := fun w z => word_onec_add16 w (word.of_Z z))
           (P := fun x => in_bounds 16 x); cycle 1.
    { intros.
      eapply onec_add16_bounds; try eassumption.
      eapply (In_map_combine_in_bounds 2); eassumption || lia. }
    { intros * Hin%(In_map_combine_in_bounds 2 ltac:(lia)) Ha0.
      eapply word_morph_onec_add; eassumption. }
    { red; lia. }
    { rewrite (copying_fold_left_as_ranged_fold_left _ (List.map _ _)).
      rewrite map_length, length_chunk by lia.
      do 2 f_equal; apply fold_left_Proper; try reflexivity; []. {
        intros * Hin%z_range_sound.
        unfold ip_checksum_upd, nlet, co_word_of_byte, co_word_of_Z.
        rewrite nth_error_nth' with (d := le_combine [default; default])
          by (rewrite map_length, length_chunk; lia).
        rewrite !map_nth, le_combine_nth_chunk by lia.
        cbn [le_combine seq List.map].
        rewrite word.morph_or, Z.lor_0_r, word.morph_shiftl by lia.
        unfold word_onec_add16, ListArray.get, cast, Convertible_Z_nat.
        repeat (lia || f_equal).
      }
    }
  Qed.

  Lemma ip_checksum_impl_ok' bs:
    ip_checksum bs = word.unsigned (ip_checksum_impl bs).
  Proof.
    rewrite ip_checksum_impl_ok, word.unsigned_of_Z_nowrap.
    - reflexivity.
    - pose proof ip_checksum_bounds bs; lia.
  Qed.
End Properties.
