Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Semantics bedrock2.Array coqutil.Word.LittleEndian.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Map.Interface. (* coercions word and rep *)
Require Import coqutil.Z.div_mod_to_equations.
Require Import coqutil.Z.bitblast.
Require Import bedrock2.ptsto_bytes.
Import HList List.

Section Scalars.
  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context {byte : Word.Interface.word 8} {byte_ok : word.ok byte}.
  Context {word16 : Word.Interface.word 16} {word16_ok : word.ok word16}.
  Context {word32 : Word.Interface.word 32} {word32_ok : word.ok word32}.

  Context {mem : map.map word byte} {mem_ok : map.ok mem}.

  Definition littleendian (n : nat) (addr : word) (value : Z) : mem -> Prop :=
    ptsto_bytes n addr (LittleEndian.split n value).

  Definition truncated_scalar sz addr (value:Z) : mem -> Prop :=
    littleendian (bytes_per (width:=width) sz) addr value.

  Notation scalar8 := ptsto (only parsing).

  Definition scalar16 addr (value: word16) : mem -> Prop :=
    truncated_scalar Syntax.access_size.two addr (word.unsigned value).

  Definition scalar32 addr (value: word32) : mem -> Prop :=
    truncated_scalar Syntax.access_size.four addr (word.unsigned value).

  Definition scalar addr (value: word) : mem -> Prop :=
    truncated_scalar Syntax.access_size.word addr (word.unsigned value).

  Lemma load_Z_of_sep sz addr (value: Z) R m
    (Hsep : sep (truncated_scalar sz addr value) R m)
    : Memory.load_Z sz m addr = Some (Z.land value (Z.ones (Z.of_nat (bytes_per (width:=width) sz)*8))).
  Proof.
    cbv [load scalar littleendian load_Z] in *.
    erewrite load_bytes_of_sep by exact Hsep; apply f_equal.
    rewrite LittleEndian.combine_split.
    set (x := (Z.of_nat (bytes_per sz) * 8)%Z).
    assert ((0 <= x)%Z) by (subst x; destruct sz; Lia.lia).
    rewrite <- Z.land_ones by assumption.
    reflexivity.
  Qed.

  Lemma store_Z_of_sep sz addr (oldvalue value: Z) R m (post:_->Prop)
    (Hsep : sep (truncated_scalar sz addr oldvalue) R m)
    (Hpost : forall m, sep (truncated_scalar sz addr value) R m -> post m)
    : exists m1, Memory.store_Z sz m addr value = Some m1 /\ post m1.
  Proof. eapply store_bytes_of_sep; [eapply Hsep|eapply Hpost]. Qed.

  Lemma load_word_of_sep addr value R m
    (Hsep : sep (scalar addr value) R m)
    : Memory.load Syntax.access_size.word m addr = Some value.
  Proof.
    cbv [load].
    erewrite load_Z_of_sep by exact Hsep; f_equal.
    cbv [bytes_per].
    eapply Properties.word.unsigned_inj.
    rewrite !word.unsigned_of_Z.
    rewrite <-Properties.word.wrap_unsigned at 2.
    eapply Z.bits_inj'; intros i Hi.
    pose proof word.width_pos (width:=width).
    repeat rewrite ?bitblast.Z.testbit_mod_pow2, ?bitblast.Z.testbit_ones, ?Z.lor_spec, ?Z.shiftl_spec, ?Z.shiftr_spec, ?Z.land_spec by Lia.lia.
    destruct (Z.ltb_spec0 i width); cbn [andb]; trivial; [].
    destruct (Z.testbit (word.unsigned value) i); cbn [andb]; trivial; [].
    destruct (Z.leb_spec0 0 i); try Lia.lia; cbn [andb]; [].
    eapply Z.ltb_lt.
    rewrite Z2Nat.id; Z.div_mod_to_equations; Lia.nia.
  Qed.

  Lemma load_one_of_sep addr value R m
    (Hsep : sep (scalar8 addr value) R m)
    : Memory.load Syntax.access_size.one m addr = Some (word.of_Z (word.unsigned value)).
  Proof.
    cbv [load load_Z load_bytes bytes_per footprint tuple.unfoldn map.getmany_of_tuple tuple.option_all tuple.map].
    erewrite get_sep by exact Hsep; repeat f_equal.
    cbn.
    eapply Z.lor_0_r.
  Qed.

  Lemma store_one_of_sep addr (oldvalue : byte) (value : word) R m (post:_->Prop)
    (Hsep : sep (scalar8 addr oldvalue) R m)
    (Hpost : forall m, sep (scalar8 addr (word.of_Z (word.unsigned value))) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.one m addr value = Some m1 /\ post m1.
  Proof.
    eapply (store_bytes_of_sep _ 1 (PrimitivePair.pair.mk _ tt)); cbn; [ecancel_assumption|].
    cbv [LittleEndian.split].
    intros; eapply Hpost; ecancel_assumption.
  Qed.

  Lemma store_word_of_sep addr (oldvalue value: word) R m (post:_->Prop)
    (Hsep : sep (scalar addr oldvalue) R m)
    (Hpost : forall m, sep (scalar addr value) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.word m addr value = Some m1 /\ post m1.
  Proof. eapply store_bytes_of_sep; [eapply Hsep|eapply Hpost]. Qed.

End Scalars.

Notation scalar8 := ptsto (only parsing).