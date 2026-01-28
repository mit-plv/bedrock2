Require Import coqutil.Map.Interface coqutil.Map.Memory coqutil.Map.Separation coqutil.Map.SeparationMemory bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Array coqutil.Word.LittleEndianList.
Require Import bedrock2.Memory.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Map.Interface. (* coercions word and rep *)
Require Import coqutil.Word.Properties.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Z.div_mod_to_equations.
Require Import coqutil.Z.bitblast.
Require Import coqutil.Z.Lia Coq.micromega.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Macros.symmetry.
Import HList List.

Section Scalars.
  Context {width : Z} {BW: Bitwidth width} {word : Word.Interface.word width} {word_ok : word.ok word}.

  Context {mem : map.map word byte} {mem_ok : map.ok mem}.
  Implicit Types (m : mem).

  Definition truncated_scalar sz addr (value:Z) : mem -> Prop :=
    (le_split (bytes_per (width:=width) sz) value) $@ addr.

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
    : load_Z m addr (Memory.bytes_per (width:=width) sz) = Some (truncate_Z (bytes_per (width:=width) sz) value).
  Proof.
    cbv [truncated_scalar] in *; extract_ex1_and_emp_in_hyps.
    erewrite load_Z_of_sep; eauto; rewrite ?length_le_split; f_equal.
    2: case BW as [ [ -> | -> ] ], sz; cbv; discriminate.
    cbv [truncate_Z]; rewrite le_combine_split, Z.land_ones; trivial; lia.
  Qed.

  Lemma store_Z_of_sep sz addr (oldvalue value: Z) R m (post:_->Prop)
    (Hsep : sep (truncated_scalar sz addr oldvalue) R m)
    (Hpost : forall m, sep (truncated_scalar sz addr value) R m -> post m)
    : exists m1, Memory.store_Z m addr (Memory.bytes_per (width:=width) sz) value = Some m1 /\ post m1.
  Proof.
    cbv [truncated_scalar] in *; extract_ex1_and_emp_in_hyps.
    edestruct uncurried_store_Z_of_sep; intuition eauto; rewrite ?length_le_split in *; trivial.
    1: case BW as [ [ -> | -> ] ], sz; cbv; discriminate.
    eexists; split. { eassumption. }
    eapply Hpost; extract_ex1_and_emp_in_goal; eauto.
  Qed.

  Lemma load_of_sep sz addr (value: word) R m
    (Hsep : sep (truncated_word sz addr value) R m)
    : Memory.load sz m addr = Some (truncate_word sz value).
  Proof.
    cbv [load truncate_word truncated_word] in *.
    erewrite load_Z_of_sep; cbv [option_map]; eauto.
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
    cbv [load load_Z Map.Memory.load_bytes bytes_per Map.Memory.footprint List.map List.seq List.option_all].
    erewrite get_sep, le_combine_1; trivial.
    rewrite Properties.word.add_0_r; eauto.
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
    cbv [store store_Z bytes_per LittleEndianList.le_split].
    cbv [store_bytes load_bytes unchecked_store_bytes footprint List.option_all List.map List.seq List.length].
    erewrite word.add_0_r, get_sep by eauto.
    eexists; split; eauto; eapply Hpost.
    rewrite map.of_list_word_singleton.
    rewrite <-Properties.map.put_putmany_commute, Properties.map.putmany_empty_r.
    eapply sep_put; eauto.
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
    (Hpost : forall m, sep (scalar16 addr value) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.two m addr value = Some m1 /\ post m1.
  Proof. eapply store_Z_of_sep; eauto. Qed.

  Lemma store_four_of_sep addr (oldvalue : word) (value : word) R m (post:_->Prop)
    (Hsep : sep (scalar32 addr oldvalue) R m)
    (Hpost : forall m, sep (scalar32 addr value) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.four m addr value = Some m1 /\ post m1.
  Proof. eapply store_Z_of_sep; eauto. Qed.

  Lemma store_word_of_sep addr (oldvalue value: word) R m (post:_->Prop)
    (Hsep : sep (scalar addr oldvalue) R m)
    (Hpost : forall m, sep (scalar addr value) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.word m addr value = Some m1 /\ post m1.
  Proof. eapply store_Z_of_sep; eauto. Qed.

  Lemma width_at_least_32: 32 <= width.
  Proof. destruct width_cases; lia. Qed.

  Lemma scalar16_of_bytes a l (H : List.length l = 2%nat) :
    Lift1Prop.iff1 (array ptsto (word.of_Z 1) a l)
                   (scalar16 a (word.of_Z (LittleEndianList.le_combine l))).
  Proof.
    pose proof width_at_least_32.
    cbv [scalar16 truncated_word truncated_scalar].
    rewrite word.unsigned_of_Z_nowrap, split_le_combine'; trivial; cycle 1.
    { eapply shrink_upper_bound; [eapply le_combine_bound|]; eapply Z.pow_le_mono_r; lia. }
    split; intros; extract_ex1_and_emp_in_goal; extract_ex1_and_emp_in_hyps.
    { epose proof length_bytearray_le _ _ _  ltac:(eassumption).
      apply array1_iff_eq_of_list_word_at; trivial. }
    { apply array1_iff_eq_of_list_word_at; eauto.
      case BW as [ [ -> | -> ] ]; blia. }
  Qed.

  (*essentially duplicates of the previous lemma...*)
  Lemma scalar32_of_bytes a l (H : List.length l = 4%nat) :
    Lift1Prop.iff1 (array ptsto (word.of_Z 1) a l)
                   (scalar32 a (word.of_Z (LittleEndianList.le_combine l))).
  Proof.
    pose proof width_at_least_32.
    cbv [scalar32 truncated_word truncated_scalar].
    rewrite word.unsigned_of_Z_nowrap, split_le_combine'; trivial; cycle 1.
    { eapply shrink_upper_bound; [eapply le_combine_bound|]; eapply Z.pow_le_mono_r; lia. }
    split; intros; extract_ex1_and_emp_in_goal; extract_ex1_and_emp_in_hyps.
    { epose proof length_bytearray_le _ _ _  ltac:(eassumption).
      apply array1_iff_eq_of_list_word_at; trivial. }
    { apply array1_iff_eq_of_list_word_at; eauto.
      case BW as [ [ -> | -> ] ]; blia. }
  Qed.

  Lemma scalar_of_bytes a l (H : width = 8 * Z.of_nat (length l)) :
    Lift1Prop.iff1 (array ptsto (word.of_Z 1) a l)
                   (scalar a (word.of_Z (LittleEndianList.le_combine l))).
  Proof.
    cbv [scalar truncated_word truncated_scalar].
    replace (bytes_per Syntax.access_size.word) with (length l). 2: {
      unfold bytes_per, bytes_per_word. subst width. clear.
      Z.div_mod_to_equations. blia.
    }
    rewrite word.unsigned_of_Z. cbv [word.wrap]; rewrite Z.mod_small.
    2: subst width; apply LittleEndianList.le_combine_bound.
    rewrite split_le_combine.
    split; intros; extract_ex1_and_emp_in_goal; extract_ex1_and_emp_in_hyps.
    { epose proof length_bytearray_le _ _ _  ltac:(eassumption).
      apply array1_iff_eq_of_list_word_at; trivial. }
    { apply array1_iff_eq_of_list_word_at; eauto.
      case BW as [ [ -> | -> ] ]; blia. }
  Qed.

  Local Infix "$+" := map.putmany (at level 70).
  Local Open Scope sep_scope.
  Import Syntax.
  Lemma load_four_bytes_of_sep_at bs a R m (Hsep: m =* (bs$@a)*R) (Hl : length bs = 4%nat):
    load access_size.four m a = Some (word.of_Z (LittleEndianList.le_combine bs)).
  Proof.
    seprewrite_in (symmetry! (array1_iff_eq_of_list_word_at(map:=mem))) Hsep.
    { rewrite Hl. etransitivity. 2:eapply Z.pow_le_mono_r; try eassumption.
      all: try eapply width_at_least_32. all: blia. }
    unshelve seprewrite_in open_constr:(Scalars.scalar32_of_bytes _ _ _) Hsep; shelve_unifiable; trivial.
    erewrite @Scalars.load_four_of_sep; shelve_unifiable; try exact _; eauto.
    f_equal.
    unfold truncate_word, truncate_Z.
    f_equal.
    rewrite word.unsigned_of_Z.
    rewrite Z.land_ones by blia.
    cbv [word.wrap]. simpl (Z.of_nat _ * _)%Z.
    epose proof le_combine_bound bs as Hll; rewrite Hl in Hll; cbn -[Z.pow] in Hll.
    repeat rewrite Z.mod_small; eauto.
    1,2: eapply shrink_upper_bound, Z.pow_le_mono_r; eauto using width_at_least_32; try blia.
  Qed.

  Lemma uncurried_load_four_bytes_of_sep_at bs a R (m : mem)
    (H: m =* (bs$@a)*R /\ length bs = 4%nat) :
    load access_size.four m a = Some (word.of_Z (LittleEndianList.le_combine bs)).
  Proof. eapply load_four_bytes_of_sep_at; eapply H. Qed.

  Lemma Z_uncurried_load_four_bytes_of_sep_at bs a R (m : mem)
    (H: m =* (bs$@a)*R /\ Z.of_nat (length bs) = 4) :
    load access_size.four m a = Some (word.of_Z (LittleEndianList.le_combine bs)).
  Proof. eapply load_four_bytes_of_sep_at; try eapply H; blia. Qed.

  (*
  Lemma store_four_of_sep addr (oldvalue : word32) (value : word) R m (post:_->Prop)
    (Hsep : sep (scalar32 addr oldvalue) R m)
    (Hpost : forall m, sep (scalar32 addr (word.of_Z (word.unsigned value))) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.four m addr value = Some m1 /\ post m1.
  Proof.
  *)

  Add Ring wring : Properties.word.ring_theory.

  Lemma array_store_of_sep (addr addr' : word) n (oldvalues : list word) (value : word) size sz R m (post:_->Prop)
    (_ : addr' = word.add addr (word.of_Z ((word.unsigned size) * (Z.of_nat n))))
    (Hsep : sep (array (truncated_word sz) size addr oldvalues) R m)
    (_ : (n < length oldvalues)%nat)
    (Hpost : forall m, sep (array (truncated_word sz) size addr (List.upd oldvalues n value)) R m -> post m)
    : exists m1, Memory.store sz m addr' value = Some m1 /\ post m1.
  Proof.
    rewrite <-(List.firstn_nth_skipn _ _ oldvalues (word.of_Z 0) H0) in Hsep.
    do 2 seprewrite_in (array_append (truncated_word sz) size) Hsep.
    seprewrite_in (array_cons (truncated_word sz) size) Hsep.
    seprewrite_in (array_nil (truncated_word sz) size) Hsep.
    rewrite !firstn_length_le in Hsep by Lia.lia.
    subst addr'.
    eapply store_of_sep; try ecancel_assumption.
    intros.
    apply Hpost.
    unfold List.upd, List.upds.
    rewrite (firstn_all2 (n := length oldvalues - n)) by (simpl; blia).
    do 2 seprewrite (array_append (truncated_word sz) size).
    seprewrite (array_cons (truncated_word sz) size).
    seprewrite (array_nil (truncated_word sz) size).
    rewrite !firstn_length_le by Lia.lia; cbn [length Nat.add] in *.
    ecancel_assumption.
  Qed.

  Lemma array_store_of_sep' (addr addr' : word) (oldvalues : list word) (value : word) size sz R m (post:_->Prop)
    (Hsep : sep (array (truncated_word sz) size addr oldvalues) R m)
    (_ : 0 < word.unsigned size)
    (_ : let offset := word.unsigned (word.sub addr' addr) in
         (Z.modulo offset (word.unsigned size) = 0) /\
         (let n := Z.to_nat (offset / word.unsigned size) in (n < List.length oldvalues)%nat /\
    (forall m, sep (array (truncated_word sz) size addr (List.upd oldvalues n value)) R m -> post m)))
    : exists m1, Memory.store sz m addr' value = Some m1 /\ post m1.
  Proof.
    destruct H0.
    destruct H1.
    eapply array_store_of_sep; eauto.
    rewrite Z2Nat.id by (apply Z.div_pos; [apply word.unsigned_range | blia]).
    rewrite <- Z_div_exact_2; [| blia| auto].
    rewrite word.of_Z_unsigned.
    ring.
  Qed.

  Lemma array_load_of_sep addr addr' n (values : list word) size sz R m
    (Hsep : (sep (array (truncated_word sz) size addr values) R m))
    (_ : addr' = (word.add addr (word.of_Z (word.unsigned size * Z.of_nat n))))
    (_ : (n < length values)%nat) :
    Memory.load sz m addr' =
    Some (truncate_word sz (nth n values (word.of_Z 0))).
  Proof.
    rewrite <-(List.firstn_nth_skipn _ _ values (word.of_Z 0) H0) in Hsep.
    do 2 seprewrite_in (array_append (truncated_word sz) size) Hsep.
    seprewrite_in (array_cons (truncated_word sz) size) Hsep.
    seprewrite_in (array_nil (truncated_word sz) size) Hsep.
    rewrite firstn_length, min_l, <-H in Hsep by blia.
    eapply load_of_sep.
    ecancel_assumption.
  Qed.

  Lemma array_load_of_sep' (addr addr': word) (values : list word) size sz R m
    (Hsep : sep (array (truncated_word sz) size addr values) R m)
    (_ : 0 < word.unsigned size)
    : let offset := word.unsigned (word.sub addr' addr) in
      (Z.modulo offset (word.unsigned size) = 0) ->
      (let n := Z.to_nat (offset / word.unsigned size) in (n < List.length values)%nat ->
      Memory.load sz m addr' =
      Some (truncate_word sz (nth n values (word.of_Z 0)))).
  Proof.
    intros.
    eapply array_load_of_sep; eauto.
    subst offset n.
    rewrite Z2Nat.id by (apply Z.div_pos; [apply word.unsigned_range | blia]).
    rewrite <- Z_div_exact_2; [| blia| auto].
    rewrite word.of_Z_unsigned.
    ring.
  Qed.

  Local Ltac Zify.zify_convert_to_euclidean_division_equations_flag ::= constr:(true).

  Lemma byte_wrap_range z:
    0 <= byte.wrap z < 2 ^ width.
  Proof using BW.
    pose proof Z.mod_pos_bound z 8.
    clear dependent word; unfold byte.wrap; destruct width_cases; subst; lia.
  Qed.

  Lemma byte_range_32 z:
    0 <= byte.wrap z < 2 ^ 32.
  Proof using.
    pose proof Z.mod_pos_bound z 8.
    clear dependent word; unfold byte.wrap; lia.
  Qed.

  Lemma byte_range_64 z:
    0 <= byte.wrap z < 2 ^ 64.
  Proof using.
    pose proof Z.mod_pos_bound z 8.
    clear dependent word; unfold byte.wrap; lia.
  Qed.

  Lemma width_mod_8 : width mod 8 = 0.
  Proof using BW. clear -BW. destruct width_cases; subst; reflexivity. Qed.

  Lemma wrap_byte_unsigned b:
    word.wrap (width := width) (byte.unsigned b) =
    byte.unsigned b.
  Proof using BW.
    clear -BW.
    pose proof byte.unsigned_range b.
    unfold word.wrap. rewrite Z.mod_small by (destruct width_cases as [-> | ->]; lia).
    reflexivity.
  Qed.

  Lemma split_bytes_per_len sz:
    forall x : word,
      Datatypes.length
         (LittleEndianList.le_split (Memory.bytes_per (width := width) sz)
                               (word.unsigned x)) =
      Memory.bytes_per (width := width) sz.
  Proof using. intros x. eapply LittleEndianList.length_le_split. Qed.

  Lemma bytes_per_width_bytes_per_word' : forall width,
      width >= 0 ->
      Z.of_nat (Memory.bytes_per (width := width) access_size.word) =
      Memory.bytes_per_word width.
  Proof using. intros; unfold Memory.bytes_per, Memory.bytes_per_word; lia. Qed.

  Lemma bytes_per_width_bytes_per_word :
    Z.of_nat (Memory.bytes_per (width := width) access_size.word) =
    Memory.bytes_per_word width.
  Proof using BW word_ok.
    clear -BW word_ok.
    pose proof word.width_pos.
    apply bytes_per_width_bytes_per_word'; lia.
  Qed.

  Lemma scalar_to_anybytes px x:
    Lift1Prop.impl1 (T := mem)
      (scalar px x)
      (Memory.anybytes px (Memory.bytes_per_word width)).
  Proof.
    cbv [scalar truncated_word truncated_scalar anybytes sepclause_of_map];
      intros ? ?; extract_ex1_and_emp_in_hyps; subst; eexists; split; trivial; []; split;
      rewrite length_le_split, bytes_per_width_bytes_per_word in *; trivial.
   case BW as [ [ -> | -> ] ]; cbv; discriminate.
  Qed.

  Lemma anybytes_to_scalar px:
    Lift1Prop.impl1 (T := mem)
      (Memory.anybytes px (Memory.bytes_per_word width))
      (Lift1Prop.ex1 (scalar px)).
  Proof.
    intros m (bs & Harray & Hlen)%anybytes_to_array_1.
    apply scalar_of_bytes in Harray.
    - eexists; eassumption.
    - rewrite Hlen. clear H. destruct width_cases; subst; reflexivity || lia.
  Qed.

End Scalars.

Notation scalar8 := ptsto (only parsing).
Notation ptsto_word := scalar (only parsing).
