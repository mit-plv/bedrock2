Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Semantics bedrock2.Array coqutil.Word.LittleEndian.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Map.Interface. (* coercions word and rep *)
Require Import coqutil.Word.Properties.
Require Import coqutil.Z.div_mod_to_equations.
Require Import coqutil.Z.bitblast.
Require Import coqutil.Z.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Macros.symmetry.
Require Import bedrock2.ptsto_bytes.
Import HList List.

Section Scalars.
  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.

  Context {mem : map.map word byte} {mem_ok : map.ok mem}.
  Implicit Types (m : mem).

  Definition littleendian (n : nat) (addr : word) (value : Z) : mem -> Prop :=
    ptsto_bytes n addr (LittleEndian.split n value).

  Definition truncated_scalar sz addr (value:Z) : mem -> Prop :=
    littleendian (bytes_per (width:=width) sz) addr value.

  Definition truncated_word sz addr (value: word) : mem -> Prop :=
    truncated_scalar sz addr (word.unsigned value).

  Notation scalar8 := ptsto (only parsing).

  Definition scalar16 := truncated_word Syntax.access_size.two.
  Definition scalar32 := truncated_word Syntax.access_size.four.
  Definition scalar := truncated_word Syntax.access_size.word.

  Definition truncate_Z n value := Z.land value (Z.ones (Z.of_nat n * 8)).

  Definition truncate_word(sz: Syntax.access_size)(w: word): word :=
    word.of_Z (truncate_Z (bytes_per (width := width) sz) (word.unsigned w)).

  Lemma load_Z_of_sep sz addr (value: Z) R m
    (Hsep : sep (truncated_scalar sz addr value) R m)
    : Memory.load_Z sz m addr = Some (truncate_Z (bytes_per (width:=width) sz) value).
  Proof.
    cbv [truncate_Z load scalar littleendian load_Z] in *.
    erewrite load_bytes_of_sep by exact Hsep; apply f_equal.
    rewrite LittleEndian.combine_split.
    set (x := (Z.of_nat (bytes_per sz) * 8)%Z).
    assert ((0 <= x)%Z) by (subst x; destruct sz; blia).
    rewrite <- Z.land_ones by assumption.
    reflexivity.
  Qed.

  Lemma store_Z_of_sep sz addr (oldvalue value: Z) R m (post:_->Prop)
    (Hsep : sep (truncated_scalar sz addr oldvalue) R m)
    (Hpost : forall m, sep (truncated_scalar sz addr value) R m -> post m)
    : exists m1, Memory.store_Z sz m addr value = Some m1 /\ post m1.
  Proof. eapply store_bytes_of_sep; [eapply Hsep|eapply Hpost]. Qed.

  Lemma load_of_sep sz addr (value: word) R m
    (Hsep : sep (truncated_word sz addr value) R m)
    : Memory.load sz m addr = Some (truncate_word sz value).
  Proof.
    cbv [load truncate_word truncated_word] in *.
    erewrite load_Z_of_sep; eauto.
  Qed.

  Lemma store_of_sep sz addr (oldvalue value: word) R m (post:_->Prop)
    (Hsep : sep (truncated_word sz addr oldvalue) R m)
    (Hpost : forall m, sep (truncated_word sz addr value) R m -> post m)
    : exists m1, Memory.store sz m addr value = Some m1 /\ post m1.
  Proof.
    cbv [store truncate_word truncated_word] in *.
    eapply store_Z_of_sep; eauto.
  Qed.

  Lemma load_one_of_sep addr value R m
    (Hsep : sep (scalar8 addr value) R m)
    : Memory.load Syntax.access_size.one m addr = Some (word.of_Z (byte.unsigned value)).
  Proof.
    cbv [load load_Z load_bytes bytes_per footprint tuple.unfoldn map.getmany_of_tuple tuple.option_all tuple.map].
    erewrite get_sep by exact Hsep; repeat f_equal.
    cbv [LittleEndian.combine PrimitivePair.pair._1].
    eapply Z.lor_0_r.
  Qed.

  Lemma load_two_of_sep addr value R m
    (Hsep : sep (scalar16 addr value) R m)
    : Memory.load Syntax.access_size.two m addr = Some (truncate_word Syntax.access_size.two value).
  Proof. eapply load_of_sep. exact Hsep. Qed.

  Lemma load_four_of_sep addr value R m
    (Hsep : sep (scalar32 addr value) R m)
    : Memory.load Syntax.access_size.four m addr = Some (truncate_word Syntax.access_size.four value).
  Proof. eapply load_of_sep. exact Hsep. Qed.

  Lemma truncate_word_nop_32bit(W32: width = 32)(value: word):
    truncate_word Syntax.access_size.four value = value.
  Proof.
    cbv [truncate_word truncate_Z bytes_per bytes_per_word].
    eapply Properties.word.unsigned_inj.
    rewrite !word.unsigned_of_Z.
    rewrite <-Properties.word.wrap_unsigned at 2.
    eapply Z.bits_inj'; intros i Hi.
    rewrite W32 at 4.
    repeat ((rewrite ?bitblast.Z.testbit_mod_pow2, ?bitblast.Z.testbit_ones, ?Z.lor_spec, ?Z.shiftl_spec, ?Z.shiftr_spec, ?Z.land_spec by blia) || unfold word.wrap).
    rewrite W32 at 1.
    destruct (Z.ltb_spec0 i 32); cbn [andb]; trivial; [].
    destruct (Z.testbit (word.unsigned value) i); cbn [andb]; trivial; [].
    cbn.
    destruct (Z.leb_spec0 0 i); try blia; cbn [andb];
    eapply Z.ltb_lt; blia.
  Qed.

  Lemma load_four_of_sep_32bit(W32: width = 32) addr value R m
    (Hsep : sep (scalar32 addr value) R m)
    : Memory.load Syntax.access_size.four m addr = Some value.
  Proof.
    eapply load_of_sep in Hsep. rewrite Hsep. f_equal. apply truncate_word_nop_32bit. assumption.
  Qed.

  Lemma load_word_of_sep addr value R m
    (Hsep : sep (scalar addr value) R m)
    : Memory.load Syntax.access_size.word m addr = Some value.
  Proof.
    cbv [load].
    erewrite load_Z_of_sep by exact Hsep; f_equal.
    cbv [truncate_Z bytes_per bytes_per_word].
    eapply Properties.word.unsigned_inj.
    rewrite !word.unsigned_of_Z.
    rewrite <-Properties.word.wrap_unsigned at 2.
    eapply Z.bits_inj'; intros i Hi.
    pose proof word.width_pos (width:=width).
    repeat ((rewrite ?bitblast.Z.testbit_mod_pow2, ?bitblast.Z.testbit_ones, ?Z.lor_spec, ?Z.shiftl_spec, ?Z.shiftr_spec, ?Z.land_spec by blia) || unfold word.wrap).
    destruct (Z.ltb_spec0 i width); cbn [andb]; trivial; [].
    destruct (Z.testbit (word.unsigned value) i); cbn [andb]; trivial; [].
    destruct (Z.leb_spec0 0 i); try blia; cbn [andb];
    eapply Z.ltb_lt;
    rewrite Z2Nat.id; Z.div_mod_to_equations; Lia.nia.
  Qed.

  Lemma store_one_of_sep addr (oldvalue : byte) (value : word) R m (post:_->Prop)
    (Hsep : sep (scalar8 addr oldvalue) R m)
    (Hpost : forall m, sep (scalar8 addr (byte.of_Z (word.unsigned value))) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.one m addr value = Some m1 /\ post m1.
  Proof.
    eapply (store_bytes_of_sep _ 1 (PrimitivePair.pair.mk _ tt)); cbn; [ecancel_assumption|].
    cbv [LittleEndian.split].
    intros; eapply Hpost; ecancel_assumption.
  Qed.

  Local Ltac byte_bitblast :=
    apply byte.unsigned_inj;
    rewrite ?byte.unsigned_of_Z; cbv [byte.wrap];
    rewrite ?word.unsigned_of_Z; cbv [word.wrap];
    Z.bitblast.

  Lemma shrink_upper_bound: forall x b1 b2,
      0 <= x < b1 ->
      b1 <= b2 ->
      0 <= x < b2.
  Proof. blia. Qed.

  Lemma store_two_of_sep addr (oldvalue : word) (value : word) R m (post:_->Prop)
    (Hsep : sep (scalar16 addr oldvalue) R m)
    (Hpost : forall m, sep (scalar16 addr (truncate_word Syntax.access_size.two value)) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.two m addr value = Some m1 /\ post m1.
  Proof.
    cbv [scalar16 truncate_Z truncated_word truncate_word truncated_scalar littleendian ptsto_bytes bytes_per tuple.to_list LittleEndian.split PrimitivePair.pair._1 PrimitivePair.pair._2 array] in Hsep, Hpost.
    eapply (store_bytes_of_sep _ 2 (PrimitivePair.pair.mk _ (PrimitivePair.pair.mk _ tt))); cbn; [ecancel_assumption|].
    cbv [LittleEndian.split].
    intros; eapply Hpost.
    assert (word.unsigned value = word.unsigned value mod 2 ^ width) as E. {
      symmetry. apply Z.mod_small. apply word.unsigned_range.
    }
    rewrite E in *.
    pose proof word.width_pos.
    use_sep_assumption.
    cancel.
    cancel_seps_at_indices 0%nat 0%nat; [f_equal; byte_bitblast|].
    cancel_seps_at_indices 0%nat 0%nat; [f_equal; byte_bitblast|].
    reflexivity.
  Qed.

  Lemma store_four_of_sep addr (oldvalue : word) (value : word) R m (post:_->Prop)
    (Hsep : sep (scalar32 addr oldvalue) R m)
    (Hpost : forall m, sep (scalar32 addr (truncate_word Syntax.access_size.four value)) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.four m addr value = Some m1 /\ post m1.
  Proof.
    cbv [scalar32 truncate_Z truncated_word truncate_word truncated_scalar littleendian ptsto_bytes bytes_per tuple.to_list LittleEndian.split PrimitivePair.pair._1 PrimitivePair.pair._2 array] in Hsep, Hpost.
    eapply (store_bytes_of_sep _ 4 (PrimitivePair.pair.mk _ (PrimitivePair.pair.mk _ (PrimitivePair.pair.mk _ (PrimitivePair.pair.mk _ tt))))); cbn; [ecancel_assumption|].
    cbv [LittleEndian.split].
    intros; eapply Hpost.
    rewrite word.unsigned_of_Z.
    assert (word.unsigned value = word.unsigned value mod 2 ^ width) as E. {
      symmetry. apply Z.mod_small. apply word.unsigned_range.
    }
    rewrite E in *.
    pose proof word.width_pos.
    use_sep_assumption.
    cancel.
    cancel_seps_at_indices 0%nat 0%nat; [f_equal; byte_bitblast|].
    cancel_seps_at_indices 0%nat 0%nat; [f_equal; byte_bitblast|].
    cancel_seps_at_indices 0%nat 0%nat; [f_equal; byte_bitblast|].
    cancel_seps_at_indices 0%nat 0%nat; [f_equal; byte_bitblast|].
    reflexivity.
  Qed.

  Lemma store_four_of_sep_32bit(W32: width = 32) addr (oldvalue : word) (value : word) R m (post:_->Prop)
    (Hsep : sep (scalar32 addr oldvalue) R m)
    (Hpost : forall m, sep (scalar32 addr value) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.four m addr value = Some m1 /\ post m1.
  Proof.
    eapply store_four_of_sep. 1: exact Hsep. intros. eapply Hpost.
    rewrite truncate_word_nop_32bit in H; assumption.
  Qed.

  Lemma store_word_of_sep addr (oldvalue value: word) R m (post:_->Prop)
    (Hsep : sep (scalar addr oldvalue) R m)
    (Hpost : forall m, sep (scalar addr value) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.word m addr value = Some m1 /\ post m1.
  Proof. eapply store_bytes_of_sep; [eapply Hsep|eapply Hpost]. Qed.

  Context (width_lower_bound: 32 <= width).

  Lemma scalar16_of_bytes a l (H : List.length l = 2%nat) :
    Lift1Prop.iff1 (array ptsto (word.of_Z 1) a l)
                   (scalar16 a (word.of_Z (LittleEndian.combine _ (HList.tuple.of_list l)))).
  Proof.
    do 2 (destruct l as [|?x l]; [discriminate|]). destruct l; [|discriminate].
    cbv [scalar16 truncated_word truncated_scalar littleendian ptsto_bytes.ptsto_bytes].
    eapply Morphisms.eq_subrelation; [exact _|].
    f_equal.
    rewrite word.unsigned_of_Z. cbv [word.wrap]; rewrite Z.mod_small.
    { erewrite LittleEndian.split_combine; exact eq_refl. }
    erewrite <-(LittleEndian.split_combine _ (HList.tuple.of_list (x :: x0 :: nil)%list)).
    erewrite LittleEndian.combine_split.
    cbn -[tuple.of_list Z.pow].
    eapply shrink_upper_bound.
    - eapply Z.mod_pos_bound; reflexivity.
    - eapply Z.pow_le_mono_r; blia.
  Qed.

  (*essentially duplicates of the previous lemma...*)
  Lemma scalar32_of_bytes a l (H : List.length l = 4%nat) :
    Lift1Prop.iff1 (array ptsto (word.of_Z 1) a l)
                   (scalar32 a (word.of_Z (LittleEndian.combine _ (HList.tuple.of_list l)))).
  Proof.
    do 4 (destruct l as [|?x l]; [discriminate|]). destruct l; [|discriminate].
    cbv [scalar32 truncated_word truncated_scalar littleendian ptsto_bytes.ptsto_bytes].
    eapply Morphisms.eq_subrelation; [exact _|].
    f_equal.
    rewrite word.unsigned_of_Z. cbv [word.wrap]; rewrite Z.mod_small.
    { erewrite LittleEndian.split_combine; exact eq_refl. }
    erewrite <-(LittleEndian.split_combine _ (HList.tuple.of_list (x :: x0 :: x1 :: x2 :: nil)%list)).
    erewrite LittleEndian.combine_split.
    cbn -[tuple.of_list Z.pow].
    eapply shrink_upper_bound.
    - eapply Z.mod_pos_bound; reflexivity.
    - eapply Z.pow_le_mono_r; blia.
  Qed.

  Lemma scalar_of_bytes a l (H : width = 8 * Z.of_nat (length l)) :
    Lift1Prop.iff1 (array ptsto (word.of_Z 1) a l)
                   (scalar a (word.of_Z (LittleEndian.combine _ (HList.tuple.of_list l)))).
  Proof.
    cbv [scalar truncated_word truncated_scalar littleendian ptsto_bytes]. subst width.
    replace (bytes_per Syntax.access_size.word) with (length l). 2: {
      unfold bytes_per, bytes_per_word. clear.
      Z.div_mod_to_equations. blia.
    }
    rewrite word.unsigned_of_Z. cbv [word.wrap]; rewrite Z.mod_small.
    { erewrite LittleEndian.split_combine.
      rewrite tuple.to_list_of_list. reflexivity. }
    apply LittleEndian.combine_bound.
  Qed.

  Local Infix "$+" := map.putmany (at level 70).
  Local Notation "xs $@ a" := (map.of_list_word_at a xs) (at level 10, format "xs $@ a").
  Local Infix "*" := sep : type_scope.
  Local Open Scope sep_scope.
  Import Syntax.
  Lemma load_four_bytes_of_sep_at bs a R m (Hsep: (eq(bs$@a)*R) m) (Hl : length bs = 4%nat):
    load access_size.four m a = Some (word.of_Z (LittleEndian.combine _ (HList.tuple.of_list bs))).
  Proof.
    seprewrite_in (symmetry! (array1_iff_eq_of_list_word_at(map:=mem))) Hsep.
    { rewrite Hl. etransitivity. 2:eapply Z.pow_le_mono_r; try eassumption. all:blia. }
    unshelve seprewrite_in open_constr:(Scalars.scalar32_of_bytes _ _ _) Hsep; shelve_unifiable; trivial.
    erewrite @Scalars.load_four_of_sep; shelve_unifiable; try exact _; eauto.
    f_equal.
    unfold truncate_word, truncate_Z.
    f_equal.
    rewrite word.unsigned_of_Z.
    rewrite Z.land_ones by blia.
    cbv [word.wrap]. simpl (Z.of_nat _ * _)%Z.
    rewrite (Z.mod_small (LittleEndian.combine (length bs) (tuple.of_list bs)) (2 ^ width)). 2: {
      eapply shrink_upper_bound.
      - eapply LittleEndian.combine_bound.
      - eapply Z.pow_le_mono_r; blia.
    }
    apply Z.mod_small.
    eapply shrink_upper_bound.
    - eapply LittleEndian.combine_bound.
    - rewrite Hl. reflexivity.
  Qed.

  Lemma uncurried_load_four_bytes_of_sep_at bs a R (m : mem)
    (H: (eq(bs$@a)*R) m /\ length bs = 4%nat) :
    load access_size.four m a = Some (word.of_Z (LittleEndian.combine _ (HList.tuple.of_list bs))).
  Proof. eapply load_four_bytes_of_sep_at; eapply H. Qed.

  Lemma Z_uncurried_load_four_bytes_of_sep_at bs a R (m : mem)
    (H: (eq(bs$@a)*R) m /\ Z.of_nat (length bs) = 4) :
    load access_size.four m a = Some (word.of_Z (LittleEndian.combine _ (HList.tuple.of_list bs))).
  Proof. eapply load_four_bytes_of_sep_at; try eapply H; blia. Qed.

  (*
  Lemma store_four_of_sep addr (oldvalue : word32) (value : word) R m (post:_->Prop)
    (Hsep : sep (scalar32 addr oldvalue) R m)
    (Hpost : forall m, sep (scalar32 addr (word.of_Z (word.unsigned value))) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.four m addr value = Some m1 /\ post m1.
  Proof.
  *)
End Scalars.

Notation scalar8 := ptsto (only parsing).
Notation ptsto_word := scalar (only parsing).
