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
#[export] Hint Unfold co_word_of_Z co_word_of_byte : compiler_cleanup.

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
                  ip_checksum_upd chk16 b0 (Byte.x00)
                else chk16 in

  let/n chk16 := (~w chk16) &w 0xffff in
  chk16.

Section Properties.
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
    rewrite Nat.div_up_eqn by lia.
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
