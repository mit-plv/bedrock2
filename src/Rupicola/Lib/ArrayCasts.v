Require Import Rupicola.Lib.Core.
Require Import coqutil.Word.LittleEndianList.

Section with_parameters.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Definition bs2zs n (bs: list byte) : list Z :=
    List.map le_combine (chunk n bs).
  Definition zs2bs n (zs: list Z): list byte :=
    List.flat_map (le_split n) zs.

  Lemma bs2zs2bs n bs:
    (0 < n)%nat ->
    (length bs mod n = 0)%nat ->
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
    unfold zs2ws, ws2zs; rewrite map_map; apply map_ext_id.
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
    rewrite map_map; apply map_ext_id; intros z Hin%(Forall_In Hzs).
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
      length (bs2zs n bs) = Nat.div_up (length bs) n.
    Proof.
      unfold bs2zs; intros.
      rewrite map_length, length_chunk, div_up_eqn.
      all: auto.
    Qed.

    Lemma div_up_mod_eq a b:
      b <> 0 ->
      a mod b = 0 ->
      Nat.div_up a b = a / b.
    Proof. intros H0 Hm; rewrite div_up_eqn, Hm; auto. Qed.

    Lemma bs2zs_length n bs :
      (n <> 0)%nat ->
      (length bs mod n = 0)%nat ->
      length (bs2zs n bs) = (length bs / n)%nat.
    Proof.
      intros; rewrite bs2zs_length', div_up_mod_eq by assumption; reflexivity.
    Qed.

    Lemma bs2ws_length' n bs:
      n <> 0 ->
      length (bs2ws n bs) = Nat.div_up (length bs) n.
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
      apply flat_map_const_length; apply length_le_split.
    Qed.

    Lemma ws2bs_length n bs:
      length (ws2bs n bs) = n * length bs.
    Proof.
      unfold ws2bs.
      rewrite zs2bs_length, ws2zs_length; reflexivity.
    Qed.
  End Properties.

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
    intros; replace bs with (zs2bs n (bs2zs n bs)) at 1 by auto using bs2zs2bs with lia.
    symmetry; apply bytes_of_truncated_scalars.
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
    apply Znumtheory.Zmod_div_mod; try eauto with lia.
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
    let sz := access_size.word in
    let n := Memory.bytes_per (width := width) sz in
    let wn := word.of_Z (Z.of_nat n) in
    Lift1Prop.iff1
      (array (word := word) scalar wn ptr ws)
      (array (word := word) ptsto (word.of_Z 1) ptr (ws2bs n ws)).
  Proof. apply bytes_of_truncated_words. Qed.

  Lemma words_of_bytes ptr bs:
    let sz := access_size.word in
    let n := Memory.bytes_per (width := width) sz in
    let wn := word.of_Z (Z.of_nat n) in
    (length bs mod n = 0)%nat ->
    Lift1Prop.iff1
      (array (word := word) ptsto (word.of_Z 1) ptr bs)
      (array (word := word) scalar wn ptr (bs2ws n bs)).
  Proof. apply truncated_words_of_bytes. Qed.
End with_parameters.
