Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Array coqutil.Word.LittleEndianList.
Require Import bedrock2.Semantics.
Require Import bedrock2.Memory.
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
Import HList List Separation.Coercions.

Section Scalars.
  Context {width : Z} {BW : Bitwidth.Bitwidth width} {word : Word.Interface.word width} {word_ok : word.ok word}.

  Context {mem : map.map word byte} {mem_ok : map.ok mem}.
  Context (TODO_Hl : forall sz, Z.of_nat (bytes_per(width:=width) sz) <= 2 ^ width).
  Implicit Types (m : mem).

  Definition littleendian (n : nat) (addr : word) (value : Z) : mem -> Prop :=
    LittleEndianList.le_split n value $@ addr.

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

  Ltac t :=
    try eassumption;
    cbn;
    rewrite ?length_le_split, ?le_combine_split, ?Z.land_ones;
    auto; try Lia.lia.

  Lemma load_of_sep sz addr (value: word) R m
    (Hsep : sep (truncated_word sz addr value) R m)
    : load sz m addr = Some (truncate_word sz value).
  Proof.
    cbv [load store truncate_word truncated_word truncate_Z] in *.
    erewrite ?load_bytes_of_sep; t.
  Qed.

  Lemma store_of_sep sz addr (oldvalue value: word) R m (post:_->Prop)
    (Hsep : sep (truncated_word sz addr oldvalue) R m)
    (Hpost : forall m, sep (truncated_word sz addr value) R m -> post m)
    : exists m1, store sz m addr value = Some m1 /\ post m1.
  Proof.
    cbv [load store store_bytes truncated_word truncated_scalar littleendian truncate_word truncate_Z] in *.
    erewrite ?load_bytes_of_sep; t.
    eexists; split; eauto.
    eapply Hpost, unchecked_store_bytes_of_sep; t.
  Qed.

  Lemma load_one_of_sep addr value R m
    (Hsep : sep (scalar8 addr value) R m)
    : load Syntax.access_size.one m addr = Some (word.of_Z (byte.unsigned value)).
  Proof.
    epose proof byte.unsigned_range value. 
    erewrite load_of_sep with (value:=word.of_Z (byte.unsigned value)); cycle 1;
    cbv [truncated_scalar littleendian truncated_word truncate_word truncate_Z bytes_per byte.wrap le_split ptsto] in *.
    { rewrite map.of_list_word_singleton, word.unsigned_of_Z.
      cbv [word.wrap]; rewrite Z.mod_small; cycle 1.
      { destruct BW as [[|]]; subst; Lia.lia. }
      replace (byte.of_Z (byte.unsigned value)) with value; cycle 1.
      { eapply byte.unsigned_inj; rewrite byte.unsigned_of_Z.
        cbv [byte.wrap]; rewrite Z.mod_small; trivial. }
      eassumption. }
    { rewrite <-byte.wrap_unsigned.
      cbv [truncated_word truncate_word truncate_Z bytes_per byte.wrap].
      rewrite Z.land_ones, word.unsigned_of_Z by Lia.lia; cbn.
      cbv [word.wrap]; repeat rewrite Z.mod_small; trivial.
      all : destruct BW as [[|]]; subst; try Lia.lia. }
  Qed.

  Lemma load_two_of_sep addr value R m
    (Hsep : sep (scalar16 addr value) R m)
    : load Syntax.access_size.two m addr = Some (truncate_word Syntax.access_size.two value).
  Proof. eapply load_of_sep. exact Hsep. Qed.

  Lemma load_four_of_sep addr value R m
    (Hsep : sep (scalar32 addr value) R m)
    : load Syntax.access_size.four m addr = Some (truncate_word Syntax.access_size.four value).
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
    : load Syntax.access_size.four m addr = Some value.
  Proof.
    eapply load_of_sep in Hsep. rewrite Hsep. f_equal. apply truncate_word_nop_32bit. assumption.
  Qed.

  Lemma load_word_of_sep addr value R m
    (Hsep : sep (scalar addr value) R m)
    : load Syntax.access_size.word m addr = Some value.
  Proof.
    erewrite load_of_sep by eassumption; f_equal.
    cbv [truncate_word truncate_Z bytes_per bytes_per_word].
    rewrite Z.land_ones by Lia.lia; rewrite Z.mod_small, word.of_Z_unsigned; trivial.
    destruct (word.unsigned_range value); split; try Lia.lia.
    eapply Z.lt_le_trans; [eassumption|].
    eapply Z.pow_le_mono_r; try Lia.lia.
    destruct Bitwidth.width_cases; clear Hsep; subst width; Z.div_mod_to_equations; Lia.lia.
  Qed.

  Lemma store_one_of_sep addr (oldvalue : byte) (value : word) R m (post:_->Prop)
    (Hsep : sep (scalar8 addr oldvalue) R m)
    (Hpost : forall m, sep (scalar8 addr (byte.of_Z (word.unsigned value))) R m -> post m)
    : exists m1, store Syntax.access_size.one m addr value = Some m1 /\ post m1.
  Proof.
    eapply store_of_sep;
     cbv [truncated_word truncated_scalar littleendian bytes_per le_split];
     rewrite map.of_list_word_singleton; eauto.
   instantiate (1:=word.of_Z(byte.unsigned oldvalue)).
    rewrite word.unsigned_of_Z.
    epose proof byte.unsigned_range oldvalue. 
    cbv [word.wrap]; rewrite Z.mod_small; cycle 1.
    { destruct Bitwidth.width_cases; subst; Lia.lia. }
      replace (byte.of_Z (byte.unsigned oldvalue)) with oldvalue; cycle 1.
      { eapply byte.unsigned_inj; rewrite byte.unsigned_of_Z.
        cbv [byte.wrap]; rewrite Z.mod_small; trivial. }
      eassumption.
  Admitted.

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
    : exists m1, store Syntax.access_size.two m addr value = Some m1 /\ post m1.
  Proof. eapply store_of_sep; [eapply Hsep|eapply Hpost]. Qed.

  Lemma store_four_of_sep addr (oldvalue : word) (value : word) R m (post:_->Prop)
    (Hsep : sep (scalar32 addr oldvalue) R m)
    (Hpost : forall m, sep (scalar32 addr value) R m -> post m)
    : exists m1, store Syntax.access_size.four m addr value = Some m1 /\ post m1.
  Proof. eapply store_of_sep; [eapply Hsep|eapply Hpost]. Qed.

  Lemma store_word_of_sep addr (oldvalue value: word) R m (post:_->Prop)
    (Hsep : sep (scalar addr oldvalue) R m)
    (Hpost : forall m, sep (scalar addr value) R m -> post m)
    : exists m1, store Syntax.access_size.word m addr value = Some m1 /\ post m1.
  Proof.
    let sz := Syntax.access_size.word in
    assert (length (le_split (bytes_per(width:=width) sz) (word.unsigned oldvalue)) = length (le_split (bytes_per(width:=width) sz) (word.unsigned value))) as pf
      by (rewrite 2LittleEndianList.length_le_split; trivial).
    unshelve eapply store_of_sep; [..|eapply Hpost]; destruct pf; [|eassumption].
  Qed.

  Context (width_lower_bound: 32 <= width).

  Lemma scalar16_of_bytes a l (H : List.length l = 2%nat) :
    Lift1Prop.iff1 (l$@a)
                   (scalar16 a (word.of_Z (LittleEndianList.le_combine l))).
  Proof.
    cbv [scalar16 truncated_word truncated_scalar littleendian].
    rewrite word.unsigned_of_Z by (destruct Bitwidth.width_cases; subst; Lia.lia).
    setoid_rewrite <-H.
    cbv [word.wrap]; rewrite Z.mod_small, split_le_combine; [reflexivity|].
    epose proof (le_combine_bound l) as Hb; rewrite H in Hb;
      (destruct Bitwidth.width_cases; subst; Lia.lia).
  Qed.

  (*essentially duplicates of the previous lemma...*)
  Lemma scalar32_of_bytes a l (H : List.length l = 4%nat) :
    Lift1Prop.iff1 (l$@a)
                   (scalar32 a (word.of_Z (LittleEndianList.le_combine l))).
  Proof.
    cbv [scalar32 truncated_word truncated_scalar littleendian].
    rewrite word.unsigned_of_Z by (destruct Bitwidth.width_cases; subst; Lia.lia).
    setoid_rewrite <-H.
    cbv [word.wrap]; rewrite Z.mod_small, split_le_combine; [reflexivity|].
    epose proof (le_combine_bound l) as Hb; rewrite H in Hb;
      (destruct Bitwidth.width_cases; subst; Lia.lia).
  Qed.

  Lemma scalar_of_bytes a l (H : width = 8 * Z.of_nat (length l)) :
    Lift1Prop.iff1 (l$@a)
                   (scalar a (word.of_Z (LittleEndianList.le_combine l))).
  Proof.
    cbv [scalar truncated_word truncated_scalar littleendian]. subst width.
    replace (bytes_per Syntax.access_size.word) with (length l). 2: {
      unfold bytes_per, bytes_per_word. clear.
      Z.div_mod_to_equations. blia.
    }
    rewrite word.unsigned_of_Z. cbv [word.wrap]; rewrite Z.mod_small.
    2: apply LittleEndianList.le_combine_bound.
    rewrite split_le_combine; reflexivity.
  Qed.

  Import Syntax.
  Lemma load_four_bytes_of_sep_at bs a R m (Hsep: ((bs$@a)*R)%sep m) (Hl : length bs = 4%nat):
    load access_size.four m a = Some (word.of_Z (LittleEndianList.le_combine bs)).
  Proof.
    erewrite load_four_of_sep.
    2: seprewrite_by (symmetry! scalar32_of_bytes) eassumption; eassumption.
    f_equal.
    unfold truncate_word, truncate_Z.
    f_equal.
    rewrite word.unsigned_of_Z.
    rewrite Z.land_ones by blia.
    cbv [word.wrap]. simpl (Z.of_nat _ * _)%Z.
    epose proof le_combine_bound bs as Hll; rewrite Hl in Hll; cbn -[Z.pow] in Hll.
    repeat rewrite Z.mod_small; eauto.
    1,2: eapply shrink_upper_bound, Z.pow_le_mono_r; eauto; try blia.
  Qed.

  Lemma uncurried_load_four_bytes_of_sep_at bs a R (m : mem)
    (H: ((bs$@a)*R)%sep m /\ length bs = 4%nat) :
    load access_size.four m a = Some (word.of_Z (LittleEndianList.le_combine bs)).
  Proof. eapply load_four_bytes_of_sep_at; eapply H. Qed.

  Lemma Z_uncurried_load_four_bytes_of_sep_at bs a R (m : mem)
    (H: ((bs$@a)*R)%sep m /\ Z.of_nat (length bs) = 4) :
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
    (Hpost : forall m, sep (array (truncated_word sz) size addr (upd oldvalues n value)) R m -> post m)
    : exists m1, store sz m addr' value = Some m1 /\ post m1.
  Proof.
    rewrite <-(firstn_nth_skipn _ _ oldvalues (word.of_Z 0) H0) in Hsep.
    do 2 seprewrite_in (array_append (truncated_word sz) size) Hsep.
    seprewrite_in (array_cons (truncated_word sz) size) Hsep.
    seprewrite_in (array_nil (truncated_word sz) size) Hsep.
    rewrite !firstn_length_le in Hsep by Lia.lia.
    subst addr'.
    eapply store_of_sep; try ecancel_assumption.
    intros.
    apply Hpost.
    unfold upd, upds.
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
    (forall m, sep (array (truncated_word sz) size addr (upd oldvalues n value)) R m -> post m)))
    : exists m1, store sz m addr' value = Some m1 /\ post m1.
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
    load sz m addr' =
    Some (truncate_word sz (nth n values (word.of_Z 0))).
  Proof.
    rewrite <-(firstn_nth_skipn _ _ values (word.of_Z 0) H0) in Hsep.
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
      load sz m addr' =
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
  
End Scalars.

Notation scalar8 := ptsto (only parsing).
Notation ptsto_word := scalar (only parsing).
