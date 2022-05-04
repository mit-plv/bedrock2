Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Memory.
Require Import Coq.Lists.List Coq.ZArith.BinInt. Local Open Scope Z_scope.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Z.Lia Coq.micromega.Lia.
Require Import coqutil.Byte.
Require Import Coq.Arith.PeanoNat.
Require Import coqutil.Word.LittleEndianList.
Require Import bedrock2.Array bedrock2.Scalars.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.

  Arguments le_combine: simpl nomatch.
  Arguments le_split : simpl nomatch.
  Arguments Z.mul: simpl nomatch.

  Lemma bytes_per_range sz:
    0 < Z.of_nat (Memory.bytes_per (width := width) sz) < 2 ^ width.
  Proof using BW. (* Cop out by depending on BW; the previous proof was too bad: *)
    clear -BW. destruct sz; simpl.
    all: try (destruct width_cases as [-> | ->]; split; reflexivity).
  Qed.

  Lemma testbit_byte_unsigned_ge b n:
    8 <= n ->
    Z.testbit (byte.unsigned b) n = false.
  Proof.
    intros;
      erewrite prove_Zeq_bitwise.testbit_above;
      eauto using byte.unsigned_range;
      lia.
  Qed.

  Lemma byte_unsigned_land (b1 b2: byte) :
    byte.unsigned (byte.and b1 b2) =
    Z.land (byte.unsigned b1) (byte.unsigned b2).
  Proof.
    unfold byte.and; rewrite byte.unsigned_of_Z.
    unfold byte.wrap; rewrite <- Z.land_ones.
    1: bitblast.Z.bitblast.
    1: rewrite testbit_byte_unsigned_ge.
    all: lia.
  Qed.

  Lemma byte_unsigned_xor (b1 b2: byte) :
    byte.unsigned (byte.xor b1 b2) =
      Z.lxor (byte.unsigned b1) (byte.unsigned b2).
  Proof.
    unfold byte.xor; rewrite byte.unsigned_of_Z.
    unfold byte.wrap; rewrite <- Z.land_ones.
    1: bitblast.Z.bitblast.
    1: rewrite !testbit_byte_unsigned_ge.
    all: reflexivity || lia.
  Qed.

  Lemma byte_xor_comm b1 b2:
    byte.xor b1 b2 = byte.xor b2 b1.
  Proof. unfold byte.xor; rewrite Z.lxor_comm; reflexivity. Qed.

  Lemma Z_land_le_combine bs1 : forall bs2,
      Z.land (le_combine bs1) (le_combine bs2) =
      le_combine (List.map (fun '(x, y) => byte.and x y) (combine bs1 bs2)).
  Proof.
    induction bs1.
    - reflexivity.
    - destruct bs2; [ apply Z.land_0_r | ]; cbn -[Z.shiftl] in *.
      rewrite <- IHbs1, !byte_unsigned_land, !Z.shiftl_land.
      bitblast.Z.bitblast.
      assert (l < 0 \/ 8 <= i) as [Hlt | Hge] by lia.
      + rewrite !(Z.testbit_neg_r _ l) by assumption.
        rewrite !Bool.orb_false_r; reflexivity.
      + rewrite !testbit_byte_unsigned_ge by lia.
        simpl; reflexivity.
  Qed.

  Definition in_bounds n x :=
    0 <= x < 2 ^ n.

  Lemma forall_in_bounds l n:
    0 <= n ->
    (Forall (in_bounds n) l) <-> (forall i, in_bounds n (nth i l 0)).
  Proof.
    intros; pose proof Z.pow_pos_nonneg 2 n.
    rewrite List.Forall_nth_default' with (d := 0);
      unfold in_bounds; reflexivity || lia.
  Qed.

  Lemma le_combine_in_bounds bs n:
    (length bs <= n)%nat ->
    in_bounds (8 * Z.of_nat n) (le_combine bs).
  Proof.
    unfold in_bounds; intros.
    pose proof le_combine_bound bs.
    pose proof Zpow_facts.Zpower_le_monotone 2 (8 * Z.of_nat (length bs)) (8 * Z.of_nat n)
         ltac:(lia) ltac:(lia); lia.
  Qed.

  Lemma Forall_le_combine_in_bounds n zs:
    (0 < n)%nat ->
    Forall (in_bounds (8 * Z.of_nat n)) (List.map le_combine (List.chunk n zs)).
  Proof.
    intros; eapply Forall_map, Forall_impl.
    - intros a; apply le_combine_in_bounds.
    - eapply Forall_impl; [ | apply List.Forall_chunk_length_le ];
        simpl; intros; lia.
  Qed.

  Lemma le_split_0_l z:
    le_split 0 z = nil.
  Proof. reflexivity. Qed.

  Lemma le_split_0_r n:
    le_split n 0 = repeat Byte.x00 n.
  Proof.
    induction n.
    - reflexivity.
    - unfold le_split; fold le_split.
      rewrite Z.shiftr_0_l, IHn; reflexivity.
  Qed.

  Open Scope list_scope.

  Lemma le_split_zeroes : forall m n z,
      0 <= z < 2 ^ (8 * Z.of_nat n) ->
      le_split (n + m) z = le_split n z ++ le_split m 0.
  Proof.
    induction n; cbn -[Z.pow Z.of_nat Z.shiftr]; intros * (Hle & Hlt).
    - replace z with 0 by lia; reflexivity.
    - rewrite IHn, !le_split_0_r; try reflexivity; [].
      rewrite Z.shiftr_div_pow2 by lia; split.
      + apply Z.div_pos; lia.
      + replace (8 * Z.of_nat (S n))%Z with (8 + 8 * Z.of_nat n)%Z in Hlt by lia.
        rewrite Z.pow_add_r in Hlt by lia.
        apply Z.div_lt_upper_bound; lia.
  Qed.

  Lemma flat_map_le_split_combine_chunk:
    forall bs n,
      (0 < n)%nat ->
      (length bs mod n)%nat = 0%nat ->
      flat_map (le_split n) (List.map le_combine (List.chunk n bs)) = bs.
  Proof.
    intros.
    rewrite flat_map_concat_map, map_map, List.map_ext_id, List.concat_chunk; [reflexivity|].
    intros * Hin;
      pose proof (List.Forall_In (@List.Forall_chunk_length_mod _ n ltac:(lia) _) Hin);
      pose proof (List.Forall_In (@List.Forall_chunk_length_le _ n ltac:(lia) _) Hin);
      cbv beta in *.
    rewrite split_le_combine'; reflexivity || lia.
  Qed.

  Lemma map_le_combine_chunk_split:
    forall zs n,
      (0 < n)%nat ->
      List.map le_combine (List.chunk n (flat_map (le_split n) zs)) =
      List.map (fun z => z mod 2 ^ (Z.of_nat n * 8)) zs.
  Proof.
    induction zs; simpl; intros.
    - reflexivity.
    - rewrite List.chunk_app by (rewrite ?length_le_split, ?Nat.mod_same; lia).
      rewrite map_app, IHzs by lia.
      rewrite le_combine_chunk_split by lia; reflexivity.
  Qed.

  Lemma map_le_combine_chunk_split_le:
    forall zs n,
      (0 < n)%nat ->
      Forall (in_bounds (8 * Z.of_nat n)) zs ->
      List.map le_combine (List.chunk n (flat_map (le_split n) zs)) = zs.
  Proof.
    intros * Hlt Hle; rewrite map_le_combine_chunk_split by lia.
    apply List.map_ext_id.
    intros * Hin%(List.Forall_In Hle).
    apply Z.mod_small.
    rewrite Z.mul_comm; assumption.
  Qed.

  Lemma map_unsigned_of_Z_le_combine bs:
    let k := Z.to_nat (bytes_per_word width) in
    List.map (fun z : Z => word.unsigned (word := word) (word.of_Z z))
             (List.map le_combine (List.chunk k bs)) =
    List.map le_combine (List.chunk k bs).
  Proof.
    cbv zeta. rewrite List.map_ext_id; [ reflexivity | ].
    intros * Hin.
    apply word.unsigned_of_Z_nowrap.
    pose proof word.width_pos.
    eapply List.Forall_In in Hin.
    2: eapply Forall_le_combine_in_bounds.
    1: unfold in_bounds in Hin.
    all: unfold bytes_per_word in *.
    2: PreOmega.Z.to_euclidean_division_equations; lia.
    split. 1: apply Hin.
    eapply Z.lt_le_trans.
    1: apply Hin.
    apply Z.pow_le_mono_r; destruct width_cases;
      PreOmega.Z.to_euclidean_division_equations; lia.
  Qed.

  Lemma le_combine_nth_chunk n (bs: list byte) idx dd:
    n <> 0%nat ->
    (idx < List.Nat.div_up (Datatypes.length bs) n)%nat ->
    le_combine (nth idx (List.chunk n bs) dd) =
    le_combine (List.map (fun idx => nth idx bs Byte.x00) (seq (idx * n) n)).
  Proof.
    intros.
    rewrite List.nth_chunk by assumption.
    rewrite List.map_seq_nth_slice, le_combine_app_0.
    reflexivity.
  Qed.

  Lemma In_map_combine_in_bounds n (Hn: n <> 0%nat) bs a:
    In a (List.map le_combine (List.chunk n bs)) ->
    0 <= a < 2 ^ (8 * Z.of_nat n).
  Proof.
    intros; eapply (List.Forall_In (Forall_le_combine_in_bounds n bs ltac:(lia)));
      eassumption.
  Qed.

  Definition bs2zs n (bs: list byte) : list Z :=
    List.map le_combine (List.chunk n bs).
  Definition zs2bs n (zs: list Z): list byte :=
    List.flat_map (le_split n) zs.

  Lemma bs2zs2bs n bs:
    (0 < n)%nat ->
    (List.length bs mod n = 0)%nat ->
    zs2bs n (bs2zs n bs) = bs.
  Proof. apply flat_map_le_split_combine_chunk. Qed.

  Lemma zs2bs2zs n zs:
    (0 < n)%nat ->
    bs2zs n (zs2bs n zs) =
    List.map (fun z => z mod 2 ^ (Z.of_nat n * 8)) zs.
  Proof. apply map_le_combine_chunk_split. Qed.

  Lemma zs2bs2zs_le n zs:
    (0 < n)%nat ->
    Forall (in_bounds (8 * Z.of_nat n)) zs ->
    bs2zs n (zs2bs n zs) = zs.
  Proof. apply map_le_combine_chunk_split_le. Qed.

  Definition zs2ws := List.map (word.of_Z (word := word)).
  Definition ws2zs := List.map (word.unsigned (word := word)).

  Lemma ws2zs2ws ws:
    zs2ws (ws2zs ws) = ws.
  Proof.
    unfold zs2ws, ws2zs; rewrite map_map; apply List.map_ext_id.
    intros; apply word.of_Z_unsigned.
  Qed.

  Lemma zs2ws2zs zs:
    ws2zs (zs2ws zs) =
    List.map word.wrap zs.
  Proof.
    unfold zs2ws, ws2zs; rewrite map_map; apply map_ext.
    intros; apply word.unsigned_of_Z.
  Qed.

  Lemma zs2ws2zs_le zs:
    Forall (in_bounds width) zs ->
    ws2zs (zs2ws zs) = zs.
  Proof.
    unfold zs2ws, ws2zs; intros Hzs.
    rewrite map_map; apply List.map_ext_id; intros z Hin%(List.Forall_In Hzs).
    apply word.unsigned_of_Z_nowrap; assumption.
  Qed.

  Definition bs2ws n (bs: list byte) : list word :=
    zs2ws (bs2zs n bs).
  Definition ws2bs n (ws: list word): list byte :=
    zs2bs n (ws2zs ws).

  Section Properties.
    Open Scope nat_scope.

    Lemma zs2ws_length zs :
      length (zs2ws zs) = length zs.
    Proof. apply map_length. Qed.

    Lemma bs2zs_length' n bs :
      n <> 0 ->
      length (bs2zs n bs) = List.Nat.div_up (length bs) n.
    Proof.
      unfold bs2zs; intros.
      rewrite map_length, List.length_chunk, List.Nat.div_up_eqn.
      all: auto.
    Qed.

    Lemma div_up_mod_eq a b:
      b <> 0 ->
      a mod b = 0 ->
      List.Nat.div_up a b = a / b.
    Proof. intros H0 Hm; rewrite List.Nat.div_up_eqn, Hm; auto. Qed.

    Lemma bs2zs_length n bs :
      (n <> 0)%nat ->
      (length bs mod n = 0)%nat ->
      length (bs2zs n bs) = (length bs / n)%nat.
    Proof.
      intros; rewrite bs2zs_length', div_up_mod_eq by assumption; reflexivity.
    Qed.

    Lemma bs2ws_length' n bs:
      n <> 0 ->
      length (bs2ws n bs) = List.Nat.div_up (length bs) n.
    Proof.
      unfold bs2ws. rewrite zs2ws_length.
      apply bs2zs_length'.
    Qed.

    Lemma bs2ws_length n bs:
      n <> 0 ->
      length bs mod n = 0 ->
      length (bs2ws n bs) = length bs / n.
    Proof.
      intros; rewrite bs2ws_length', div_up_mod_eq by assumption; reflexivity.
    Qed.

    Lemma ws2zs_length ws :
      length (ws2zs ws) = length ws.
    Proof. apply map_length. Qed.

    Lemma zs2bs_length n zs :
      length (zs2bs n zs) = n * length zs.
    Proof.
      unfold zs2bs.
      apply List.flat_map_const_length; apply length_le_split.
    Qed.

    Lemma ws2bs_length n bs:
      length (ws2bs n bs) = n * length bs.
    Proof.
      unfold ws2bs.
      rewrite zs2bs_length, ws2zs_length; reflexivity.
    Qed.

    Lemma bs2ws2bs bs:
      let sz := Syntax.access_size.word in
      let n := Memory.bytes_per (width := width) sz in
      (List.length bs mod n = 0)%nat ->
      ws2bs n (bs2ws n bs) = bs.
    Proof using word_ok BW.
      clear mem mem_ok.
      cbv zeta. intros. unfold ws2bs, bs2ws. rewrite zs2ws2zs.
      rewrite List.map_ext_id.
      - apply bs2zs2bs. 2: assumption.
        pose proof (bytes_per_range Syntax.access_size.word). lia.
      - intros. unfold bs2zs in H0.
        eapply In_map_combine_in_bounds in H0.
        2: destruct width_cases; subst; cbv; discriminate 1.
        unfold word.wrap. apply Z.mod_small.
        cbn in H0.
        destruct width_cases; subst width; cbn in H0; lia.
    Qed.
  End Properties.

  Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  Lemma bytes_of_truncated_scalar sz ptr a:
    Lift1Prop.iff1
      (truncated_scalar sz ptr a)
      (array (word := word) ptsto (word.of_Z 1) ptr
             (le_split (Memory.bytes_per (width:=width) sz) a)).
  Proof.
    unfold truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes.
    rewrite HList.tuple.to_list_of_list; reflexivity.
  Qed.

  Lemma bytes_of_truncated_scalars : forall sz zs ptr,
    let n := Memory.bytes_per (width := width) sz in
    let wn := (word.of_Z (Z.of_nat n)) in
    Lift1Prop.iff1
      (array (word := word) (truncated_scalar sz) wn ptr zs)
      (array (word := word) ptsto (word.of_Z 1) ptr (zs2bs n zs)).
  Proof.
    induction zs; simpl; intros.
    - reflexivity.
    - intros; rewrite array_append.
      rewrite <- IHzs.
      rewrite word.unsigned_of_Z_1, Z.mul_1_l.
      rewrite length_le_split.
      rewrite bytes_of_truncated_scalar.
      reflexivity.
  Qed.

  Lemma truncated_scalars_of_bytes ptr bs sz:
    let n := Memory.bytes_per (width := width) sz in
    let wn := word.of_Z (Z.of_nat n) in
    (length bs mod n = 0)%nat ->
    Lift1Prop.iff1
      (array (word := word) ptsto (word.of_Z 1) ptr bs)
      (array (word := word) (truncated_scalar sz) wn ptr (bs2zs n bs)).
  Proof.
    pose proof bytes_per_range sz.
    intros. replace bs with (zs2bs n (bs2zs n bs)) at 1.
    1: symmetry; apply bytes_of_truncated_scalars.
    apply bs2zs2bs. 2: assumption. lia.
  Qed.

  Lemma Z_pow_divide' p q t:
    0 <= q ->
    0 <= t ->
    (p ^ q | p ^ (q + t)).
  Proof.
    intros; rewrite Z.pow_add_r by assumption.
    apply Z.divide_mul_l; reflexivity.
  Qed.

  Lemma Z_pow_divide p q1 q2:
    0 <= q1 <= q2 ->
    (p ^ q1 | p ^ q2).
  Proof.
    intros; replace q2 with (q1 + (q2 - q1)) by lia.
    apply Z_pow_divide'; lia.
  Qed.

  Lemma le_split_mod (n: nat) m z:
    Z.of_nat n * 8 <= m ->
    le_split n (z mod 2 ^ m) = le_split n z.
  Proof.
    unfold word.wrap; rewrite le_split_mod; symmetry; rewrite le_split_mod.
    f_equal.
    pose proof word.width_pos.
    pose proof Z.pow_pos_nonneg 2.
    apply Znumtheory.Zmod_div_mod; try lia.
    apply Z_pow_divide; lia.
  Qed.

  Lemma le_split_wrap sz z:
    let n := Memory.bytes_per (width := width) sz in
    le_split n (word.wrap z) = le_split n z.
  Proof.
    pose proof width_at_least_32.
    pose proof word.width_nonneg.
    apply le_split_mod; destruct sz; [simpl; lia.. | ].
    destruct width_cases as [-> | ->]; simpl; reflexivity.
  Qed.

  Lemma truncated_scalar_wrap sz ptr z:
    Lift1Prop.iff1
      (truncated_scalar (word := word) sz ptr (word.wrap z))
      (truncated_scalar (word := word) sz ptr z).
  Proof.
    unfold truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes.
    rewrite !le_split_wrap; reflexivity.
  Qed.

  Lemma truncated_words_of_truncated_scalars : forall sz zs ptr,
    let wn := (word.of_Z (Z.of_nat (Memory.bytes_per (width := width) sz))) in
    Lift1Prop.iff1
      (array (word := word) (truncated_scalar sz) wn ptr zs)
      (array (word := word) (truncated_word sz) wn ptr (zs2ws zs)).
  Proof.
    unfold truncated_word; induction zs; simpl; intros.
    - reflexivity.
    - rewrite word.unsigned_of_Z.
      rewrite truncated_scalar_wrap.
      rewrite IHzs; reflexivity.
  Qed.

  Lemma truncated_scalars_of_truncated_words : forall sz ws ptr,
    let wn := (word.of_Z (Z.of_nat (Memory.bytes_per (width := width) sz))) in
    Lift1Prop.iff1
      (array (word := word) (truncated_word sz) wn ptr ws)
      (array (word := word) (truncated_scalar sz) wn ptr (ws2zs ws)).
  Proof.
    intros; replace ws with (zs2ws (ws2zs ws)) at 1 by auto using ws2zs2ws.
    symmetry; apply truncated_words_of_truncated_scalars.
  Qed.

  Lemma bytes_of_truncated_words : forall sz ws ptr,
    let n := Memory.bytes_per (width := width) sz in
    let wn := (word.of_Z (Z.of_nat n)) in
    Lift1Prop.iff1
      (array (word := word) (truncated_word sz) wn ptr ws)
      (array (word := word) ptsto (word.of_Z 1) ptr (ws2bs n ws)).
  Proof.
    cbv zeta; intros.
    rewrite truncated_scalars_of_truncated_words.
    apply bytes_of_truncated_scalars.
  Qed.

  Lemma truncated_words_of_bytes ptr bs sz:
    let n := Memory.bytes_per (width := width) sz in
    let wn := word.of_Z (Z.of_nat n) in
    (length bs mod n = 0)%nat ->
    Lift1Prop.iff1
      (array (word := word) ptsto (word.of_Z 1) ptr bs)
      (array (word := word) (truncated_word sz) wn ptr (bs2ws n bs)).
  Proof.
    cbv zeta; intros.
    rewrite truncated_scalars_of_bytes by eassumption.
    apply truncated_words_of_truncated_scalars.
  Qed.

  Lemma bytes_of_words : forall ws ptr,
    let sz := Syntax.access_size.word in
    let n := Memory.bytes_per (width := width) sz in
    let wn := word.of_Z (Z.of_nat n) in
    Lift1Prop.iff1
      (array (word := word) scalar wn ptr ws)
      (array (word := word) ptsto (word.of_Z 1) ptr (ws2bs n ws)).
  Proof. apply bytes_of_truncated_words. Qed.

  Lemma words_of_bytes ptr bs:
    let sz := Syntax.access_size.word in
    let n := Memory.bytes_per (width := width) sz in
    let wn := word.of_Z (Z.of_nat n) in
    (length bs mod n = 0)%nat ->
    Lift1Prop.iff1
      (array (word := word) ptsto (word.of_Z 1) ptr bs)
      (array (word := word) scalar wn ptr (bs2ws n bs)).
  Proof. apply truncated_words_of_bytes. Qed.

End with_parameters.
