From Coq Require List.
Require Import bedrock2.Memory.
Require Import Rupicola.Lib.Core.
Require Import Rupicola.Lib.Notations.

Module InlineTable.
  Section InlineTable.
    Context {K V: Type}.
    Context {HD: HasDefault V}.
    Context {Conv: Convertible K nat}.

    Definition t := list V.
    Definition get (a: t) (k: K) : V :=
      List.nth (cast k) a default.
  End InlineTable.

  Arguments t : clear implicits.
End InlineTable.

Section __.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {mem: map.map word Byte.byte}.
  Context {locals: map.map String.string word}.
  Context {env: map.map String.string (list String.string * list String.string * Syntax.cmd)}.
  Context {ext_spec: bedrock2.Semantics.ExtSpec}.
  Context {word_ok : word.ok word} {mem_ok : map.ok mem}.
  Context {locals_ok : map.ok locals}.
  Context {env_ok : map.ok env}.
  Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

  Context {K: Type}.
  Context {Conv: Convertible K nat}.

  Context {HD_byte: HasDefault Byte.byte}.
  Context {HD_word: HasDefault word}.

  Section Any.
    Context {V: Type}.
    Context {HD: HasDefault V}.
    Context (ConvV: Convertible V byte).

    Lemma compile_inlinetable_get_any_as_byte : forall {tr mem locals functions},
      forall (idx: K) (t: InlineTable.t V),
        let v := InlineTable.get t idx in
        forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
          var idx_expr,

          let n := cast idx in
          (n < List.length t)%nat ->
          (Z.of_nat (List.length t) <= 2 ^ width) ->

          WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat n)) ->

          (let v := v in
           <{ Trace := tr;
              Memory := mem;
              Locals := map.put locals var (word_of_byte (cast v));
              Functions := functions }>
             k_impl
           <{ pred (k v eq_refl) }>) ->

          <{ Trace := tr;
             Memory := mem;
             Locals := locals;
             Functions := functions }>
            (cmd.seq
               (cmd.set var (expr.inlinetable
                               access_size.one
                               (List.map cast t)
                               idx_expr))
               k_impl)
          <{ pred (nlet_eq [var] v k) }>.
    Proof.
      intros; repeat straightline.
      exists (word_of_byte (cast v)); split; repeat straightline; eauto.
      eapply WeakestPrecondition_dexpr_expr; eauto.
      eexists; split; eauto.
      unfold load, load_Z, load_bytes, map.getmany_of_tuple; simpl.
      rewrite OfListWord.map.get_of_list_word.
      rewrite word.unsigned_of_Z_nowrap, Nat2Z.id by lia.
      rewrite nth_error_nth' with (d := cast default)
        by (rewrite map_length; lia).
      rewrite map_nth.
      setoid_rewrite LittleEndianList.le_combine_1.
      reflexivity.
    Qed.
  End Any.

  Lemma compile_inlinetable_get_byte : forall {tr mem locals functions},
    forall (idx: K) (t: InlineTable.t byte),
      let v := InlineTable.get t idx in
      forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      var idx_expr,

      let n := cast idx in
      (n < List.length t)%nat ->
      (Z.of_nat (List.length t) <= 2 ^ width) ->

      WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat n)) ->

      (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var (word_of_byte v);
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->

      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
        (cmd.seq
           (cmd.set var (expr.inlinetable access_size.one t idx_expr))
           k_impl)
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
    intros.
    rewrite <- (map_id t).
    apply compile_inlinetable_get_any_as_byte;
      eauto.
  Qed.

  Definition word_to_bytes (z : word) : list byte:=
    LittleEndianList.le_split (Z.to_nat (width / 8)) (word.unsigned z).

  (* Turns a table of 32-bit words stored in Zs into
     a table of bytes *)
  Definition to_byte_table : list word -> list byte :=
    flat_map word_to_bytes.

  Lemma map_fold_empty_id (f : mem -> word -> Init.Byte.byte -> mem) m
    : (forall m k v, f m k v = map.put m k v) ->
      map.fold f map.empty m = m.
  Proof.
    intros; apply map.fold_spec; intros; subst; auto.
  Qed.

  Lemma of_list_word_at_0 (xs : list byte)
    : OfListWord.map.of_list_word xs
      = OfListWord.map.of_list_word_at (word.of_Z 0 : word) xs.
  Proof.
    unfold OfListWord.map.of_list_word_at.
    unfold MapKeys.map.map_keys.
    unfold OfListWord.map.of_list_word.
    induction xs; simpl.
    { rewrite map.fold_empty; auto. }
    {
      rewrite <- seq_shift.
      rewrite map_map.

      rewrite word.unsigned_of_Z_0.
      cbn.
      rewrite map_fold_empty_id; [ reflexivity | ..].
      {
        intros.
        rewrite word.ring_theory.(Radd_0_l).
        reflexivity.
      }
    }
  Qed.

  Lemma HList_tuple_of_list_to_list:
    forall {A : Type} n (xs : HList.tuple A n) eqn,
      HList.tuple.of_list (HList.tuple.to_list xs)
      = eq_rect_r _ xs eqn.
  Proof.
    induction n; destruct xs; cbn in *; intros.
    - destruct eq_rect_r; reflexivity.
    - rewrite (IHn _2 ltac:(eauto using eq_add_S)).
      revert eqn; generalize (List.length (HList.tuple.to_list _2)).
      intros; inversion eqn; subst.
      rewrite (Eqdep_dec.UIP_refl_nat _ (eq_add_S _ _ _)).
      rewrite (Eqdep_dec.UIP_refl_nat _ eqn).
      reflexivity.
  Qed.

  Lemma load_of_list_word a b b1 b2 b3 n
    : Z.of_nat (List.length (a ++ b)) <= 2 ^ width ->
      b = (b1 ++ b2 ++ b3)%list ->
      n = Z.of_nat (length b1) ->
      width = 8* Z.of_nat (List.length b2) ->
      load access_size.word (OfListWord.map.of_list_word (a ++ b)) (word.of_Z (Z.of_nat (length a) + n))
      = load access_size.word (OfListWord.map.of_list_word b) (word.of_Z n : word).
  Proof.
    intros. subst b. subst n.
    assert (Z.of_nat (List.length (b1 ++ b2 ++ b3)) <= 2 ^ width).
    {
      rewrite app_length in H.
      rewrite Nat2Z.inj_add in H.
      lia.
    }
    rewrite !of_list_word_at_0.
    erewrite !load_word_of_sep;
      try reflexivity;
      match goal with
        [|- ?P (OfListWord.map.of_list_word_at ?p ?xs)] =>
         assert (array ptsto (word.of_Z 1) p xs
                       (OfListWord.map.of_list_word_at p xs)) as H1;
           [apply ptsto_bytes.array1_iff_eq_of_list_word_at; eauto using mem_ok|
           generalize dependent (OfListWord.map.of_list_word_at p xs); intros]
      end.
    {
      repeat seprewrite_in (@array_append width word) H1.
      rewrite !word.ring_morph_mul in H1.
      rewrite !word.of_Z_unsigned in H1.
      rewrite !word.ring_theory.(Rmul_1_l) in H1.
      rewrite <-!word.ring_morph_add in H1.
      simpl in H1.

      seprewrite_in (scalar_of_bytes (word.of_Z (Z.of_nat (length b1))) b2 H2) H1.
      ecancel_assumption.
    }
    {
      repeat seprewrite_in @array_append H1.
      rewrite !word.ring_morph_mul in H1.
      rewrite !word.of_Z_unsigned in H1.
      rewrite !word.ring_theory.(Rmul_1_l) in H1.
      rewrite <-!word.ring_morph_add in H1.
      simpl in H1.

      seprewrite_in scalar_of_bytes H1; auto.
      ecancel_assumption.
    }
  Qed.

  Lemma length_word_to_bytes a :
    List.length (word_to_bytes a) = Z.to_nat (width / 8).
  Proof. eapply LittleEndianList.length_le_split. Qed.

  Lemma length_to_byte_table t :
    List.length (to_byte_table t) = (Z.to_nat (width / 8) * List.length t)%nat.
  Proof.
    unfold to_byte_table.
    erewrite List.flat_map_const_length; [ reflexivity | ].
    eauto using length_word_to_bytes.
  Qed.

  Lemma length_of_to_bytes a :
    width = 8 * Z.of_nat (List.length (word_to_bytes a)).
  Proof.
    rewrite length_word_to_bytes, Z2Nat.id.
    pose proof width_mod_8; apply Z_div_exact_2; lia.
    pose proof word.width_pos; apply Z.div_pos; lia.
  Qed.

  Lemma load_from_word_table t n d
    : Z.of_nat (length (to_byte_table t)) <= 2 ^ width ->
      (n < length t)%nat ->
      load access_size.word
           (OfListWord.map.of_list_word (to_byte_table t))
           (word.of_Z (width/8 * Z.of_nat n))
      = Some (nth n t d).
  Proof.
    intros table_bounds.
    revert n; induction t; intro n; destruct n; intros; try (simpl in *; lia).
    {
      rewrite Z.mul_0_r.
      rewrite of_list_word_at_0.
      assert (array ptsto (word.of_Z 1) (word.of_Z 0)
                    (word_to_bytes a ++ to_byte_table t)
                    (OfListWord.map.of_list_word_at
                       (word.of_Z 0 : word)
                       (word_to_bytes a ++ to_byte_table t))).
      {
        eapply ptsto_bytes.array1_iff_eq_of_list_word_at; auto using mem_ok.
      }
      seprewrite_in @array_append H0.
      seprewrite_in @scalar_of_bytes H0; auto.
      apply length_of_to_bytes.
      eapply load_word_of_sep.
      assert ((LittleEndianList.le_combine (word_to_bytes a)) = word.unsigned a).
      {
        unfold word_to_bytes.
        rewrite LittleEndianList.le_combine_split, Z2Nat.id.
        {
          replace (width/8 *8) with width.
          rewrite word.wrap_unsigned; auto.
          pose proof width_mod_8.
          destruct width_cases as [H' | H']; rewrite H'; compute; auto.
        }
        {
          pose proof width_at_least_32.
          apply Z.div_pos; lia.
        }
      }
      {
        simpl in *.
        match type of H0 with
        | context [scalar _ ?e] =>
          assert (e = a)
        end.
        {
          rewrite <- word.of_Z_unsigned.
          f_equal.
          exact H1.
        }
        rewrite H2 in H0.
        ecancel_assumption.
      }
    }
    {
      cbn [nth].
      replace (width/8 * Z.of_nat (S n)) with (width/8 + (width/8* Z.of_nat n)) by lia.
      unfold to_byte_table; simpl; fold to_byte_table.
      match goal with
        [|- load _ _ (word.of_Z (?w + _)) = _ ] =>
        assert (w = Z.of_nat (List.length (word_to_bytes a)))
      end.
      {
        unfold word_to_bytes.
        rewrite LittleEndianList.length_le_split, Z2Nat.id; try lia.
        destruct width_cases as [H' | H']; rewrite H';
          intro cmp; inversion cmp.
      }
      rewrite H0 at 1.
      erewrite load_of_list_word.
      apply IHt.
      (*{ inversion cell_bounds; assumption. }*)
      {
        unfold word_to_bytes in table_bounds;
        simpl in table_bounds;
        fold word_to_bytes in table_bounds.
        rewrite app_length in table_bounds.
        lia.
      }
      { simpl in H; lia. }
      { simpl in table_bounds; lia. }
      { rewrite <- (List.firstn_skipn (Z.to_nat (width/8 * Z.of_nat n)) (to_byte_table t)).
        f_equal.
        match goal with
          [|- ?l = _] =>
          rewrite <- (List.firstn_skipn (Z.to_nat (width / 8)) l)
        end.
        f_equal.
      }
      {
        rewrite firstn_length_le.
        rewrite Z2Nat.id; try lia.
        rewrite Z2Nat.inj_mul; try lia.
        rewrite Nat2Z.id.
        rewrite length_to_byte_table.
        simpl in H.
        nia.
      }
      {
        rewrite firstn_length_le; try lia.
        {
          rewrite Z2Nat.id; try lia.
          pose proof width_mod_8.
          apply Z_div_exact_2; auto; lia.
        }
        {
          rewrite skipn_length.
          rewrite Z2Nat.inj_mul; try lia.
          rewrite Nat2Z.id.
          rewrite length_to_byte_table.
          simpl in H.
          nia.
        }
      }
    }
  Qed.

  Lemma compile_inlinetable_get_word : forall {tr mem locals functions},
    forall {idx: K} {t},
    let v := InlineTable.get t idx in
    forall {P} {pred: P v -> predicate} {k: nlet_eq_k P v} {k_impl}
      var idx_expr,

      let n := cast idx in
      (n < List.length t)%nat ->
      (Z.of_nat (List.length (to_byte_table t)) <= 2 ^ width) ->

      WeakestPrecondition.dexpr mem locals idx_expr (word.of_Z (Z.of_nat n)) ->

      (let v := v in
         <{ Trace := tr;
            Memory := mem;
            Locals := map.put locals var v;
            Functions := functions }>
         k_impl
         <{ pred (k v eq_refl) }>) ->

      <{ Trace := tr;
         Memory := mem;
         Locals := locals;
         Functions := functions }>
      (cmd.seq (cmd.set
                  var
                  (expr.inlinetable access_size.word (to_byte_table t)
                                    (expr.op bopname.mul (expr.literal (width / 8))
                                             idx_expr)))
               k_impl)
      <{ pred (nlet_eq [var] v k) }>.
  Proof.
    intros; repeat straightline.
    exists v; split; repeat straightline; eauto.
    eapply WeakestPrecondition_dexpr_expr; eauto.
    eexists; split; eauto.
    unfold v0; rewrite <- word.ring_morph_mul.
    apply load_from_word_table; auto.
  Qed.
End __.

#[export] Hint Extern 1 (WP_nlet_eq (InlineTable.get _ _)) =>
  simple eapply @compile_inlinetable_get_byte; shelve : compiler.
#[export] Hint Extern 1 (WP_nlet_eq (InlineTable.get _ _)) =>
  simple eapply @compile_inlinetable_get_word; shelve : compiler.
#[export] Hint Extern 5 (WP_nlet_eq (InlineTable.get _ _)) =>
  simple eapply @compile_inlinetable_get_any_as_byte; shelve : compiler.
