Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Semantics bedrock2.Array coqutil.Word.LittleEndian.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Map.Interface. (* coercions word and rep *)
Require Import coqutil.Z.div_mod_to_equations.
Import HList List.

Section Scalars.
  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context {byte : Word.Interface.word 8} {byte_ok : word.ok byte}.
  Context {word16 : Word.Interface.word 16} {word16_ok : word.ok word16}.
  Context {word32 : Word.Interface.word 32} {word32_ok : word.ok word32}.

  Context {mem : map.map word byte} {mem_ok : map.ok mem}.

  Definition littleendian (n : nat) (addr : word) (value : Z) : mem -> Prop :=
    array ptsto (word.of_Z 1) addr (tuple.to_list (LittleEndian.split n value)).

  Definition truncated_scalar sz addr (value:Z) : mem -> Prop :=
    littleendian (bytes_per (width:=width) sz) addr value.

  Definition scalar8 := ptsto.

  Definition scalar16 addr (value: word16) : mem -> Prop :=
    truncated_scalar Syntax.access_size.two addr (word.unsigned value).

  Definition scalar32 addr (value: word32) : mem -> Prop :=
    truncated_scalar Syntax.access_size.four addr (word.unsigned value).

  Definition scalar addr (value: word) : mem -> Prop :=
    truncated_scalar Syntax.access_size.word addr (word.unsigned value).

  (* TODO: factor out getmany_sep and putmany_sep *)
  Lemma load_bytes_sep a n bs R m
    (Hsep : sep (array ptsto (word.of_Z 1) a (tuple.to_list bs)) R m)
    : Memory.load_bytes n m a = Some bs.
  Proof.
    cbv [load_bytes footprint].
    revert dependent a; revert dependent R; revert dependent m; revert dependent n.
    induction n; [solve[cbn; intros []; trivial]|].
    intros [b0 bs] m R a Hsep.
    cbn in Hsep; eapply SeparationLogic.sep_assoc in Hsep.
    cbn [map.getmany_of_tuple tuple.option_all tuple.map tuple.unfoldn].
    erewrite SeparationLogic.get_sep by exact Hsep.
    setoid_rewrite IHn; [exact eq_refl|].
    cbn.
    refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ Hsep); clear Hsep.
    SeparationLogic.ecancel.
  Qed.

  Lemma sep_unchecked_store_bytes a n oldbs bs R m
    (Hsep : sep (array ptsto (word.of_Z 1) a (tuple.to_list (n:=n) oldbs)) R m)
    : sep (array ptsto (word.of_Z 1) a (tuple.to_list bs)) R (Memory.unchecked_store_bytes n m a bs).
  Proof.
    revert dependent a; revert dependent R; revert dependent m; revert dependent bs; revert dependent oldbs; revert dependent n.
    induction n; [solve[cbn; intros []; trivial]|].
    intros [oldb0 oldbs] [b0 bs] m R a Hsep.
    unshelve epose proof (IHn oldbs bs (map.put m a b0) (sep (ptsto a b0) R) (word.add a (word.of_Z 1)) _) as IHn2; clear IHn; [|clear Hsep].
    { cbn in Hsep |- *; eapply SeparationLogic.sep_assoc in Hsep.
      unshelve epose proof sep_put _ _ b0 _ _ _ Hsep as Hsep2; clear Hsep. exact Properties.word.eq_or_neq.
      refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ Hsep2); clear Hsep2.
      SeparationLogic.ecancel. }
    cbv [unchecked_store_bytes footprint] in *; cbn.
    refine (Lift1Prop.subrelation_iff1_impl1 _ _ _ _ _ IHn2); clear IHn2.
    SeparationLogic.ecancel.
  Qed.

  Lemma store_bytes_sep a n oldbs bs R m (post:_->Prop)
    (Hsep : sep (array ptsto (word.of_Z 1) a (tuple.to_list (n:=n) oldbs)) R m)
    (Hpost : forall m, sep (array ptsto (word.of_Z 1) a (tuple.to_list bs)) R m -> post m)
    : exists m1, Memory.store_bytes n m a bs = Some m1 /\ post m1.
  Proof. cbv [store_bytes]. erewrite load_bytes_sep; eauto using sep_unchecked_store_bytes. Qed.

  Lemma combine_split n z :
   LittleEndian.combine n (LittleEndian.split n z) = (z mod 2^(Z.of_nat n*8))%Z.
  Proof.
    revert z; induction n.
    { cbn. intros. rewrite Z.mod_1_r. trivial. }
    { cbn [LittleEndian.split LittleEndian.combine PrimitivePair.pair._1 PrimitivePair.pair._2]; intros.
      erewrite IHn; clear IHn.
      rewrite word.unsigned_of_Z, Nat2Z.inj_succ, Z.mul_succ_l by Lia.lia.
      (* bitwise proof, automatable: *)
      eapply Z.bits_inj'; intros i Hi.
      repeat rewrite ?Z.lor_spec, ?Properties.Z.testbit_mod_pow2, ?Z.shiftl_spec, ?Z.shiftr_spec by Lia.lia.
      destruct (Z.ltb_spec0 i 8); cbn [andb orb].
      { rewrite (Z.testbit_neg_r _ (i-8)) by Lia.lia.
        rewrite Bool.andb_false_r, Bool.orb_false_r.
        destruct (Z.ltb_spec0 i (Z.of_nat n * 8 + 8)); trivial; Lia.lia. }
      { rewrite Z.shiftr_spec by Lia.lia.
        replace (i - 8 + 8)%Z with i by Lia.lia; f_equal.
        destruct
          (Z.ltb_spec0 (i-8) (Z.of_nat n * 8)),
          (Z.ltb_spec0 i (Z.of_nat n * 8 + 8));
          trivial; Lia.lia. } }
  Qed.

  Lemma load_Z_of_sep sz addr (value: Z) R m
    (Hsep : sep (truncated_scalar sz addr value) R m)
    : Memory.load_Z sz m addr = Some (Z.land value (Z.ones (Z.of_nat (bytes_per (width:=width) sz)*8))).
  Proof.
    cbv [load scalar littleendian load_Z] in *.
    erewrite load_bytes_sep by exact Hsep; apply f_equal.
    rewrite combine_split.
    set (x := (Z.of_nat (bytes_per sz) * 8)%Z).
    assert ((0 <= x)%Z) by (subst x; destruct sz; Lia.lia).
    (* bitwise proof, automatable: *)
    eapply Z.bits_inj'; intros i Hi.
    pose proof word.width_pos (width:=width).
    repeat rewrite ?Properties.Z.testbit_mod_pow2, ?Properties.Z.testbit_ones, ?Z.lor_spec, ?Z.shiftl_spec, ?Z.shiftr_spec, ?Z.land_spec by Lia.lia.
    repeat match goal with |- context[(?a <? ?b)%Z]
                           => destruct (Z.ltb_spec0 a b)
           end; try Btauto.btauto.
    destruct (Z.leb_spec0 0 i); cbn; try Btauto.btauto.
    Lia.lia.
  Qed.

  Lemma store_Z_of_sep sz addr (oldvalue value: Z) R m (post:_->Prop)
    (Hsep : sep (truncated_scalar sz addr oldvalue) R m)
    (Hpost : forall m, sep (truncated_scalar sz addr value) R m -> post m)
    : exists m1, Memory.store_Z sz m addr value = Some m1 /\ post m1.
  Proof. eapply store_bytes_sep; [eapply Hsep|eapply Hpost]. Qed.

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
    repeat rewrite ?Properties.Z.testbit_mod_pow2, ?Properties.Z.testbit_ones, ?Z.lor_spec, ?Z.shiftl_spec, ?Z.shiftr_spec, ?Z.land_spec by Lia.lia.
    destruct (Z.ltb_spec0 i width); cbn [andb]; trivial; [].
    destruct (Z.testbit (word.unsigned value) i); cbn [andb]; trivial; [].
    destruct (Z.leb_spec0 0 i); try Lia.lia; cbn [andb]; [].
    eapply Z.ltb_lt.
    rewrite Z2Nat.id; Z.div_mod_to_equations; Lia.nia.
  Qed.

  Lemma store_word_of_sep addr (oldvalue value: word) R m (post:_->Prop)
    (Hsep : sep (scalar addr oldvalue) R m)
    (Hpost : forall m, sep (scalar addr value) R m -> post m)
    : exists m1, Memory.store Syntax.access_size.word m addr value = Some m1 /\ post m1.
  Proof. eapply store_bytes_sep; [eapply Hsep|eapply Hpost]. Qed.

End Scalars.
