Require Import coqutil.Map.Interface bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Lift1Prop bedrock2.Semantics bedrock2.Array coqutil.Word.LittleEndian.
Require Import Coq.Lists.List Coq.ZArith.ZArith.
Require Import coqutil.Word.Interface coqutil.Map.Interface. (* coercions word and rep *)
Require Import coqutil.Z.div_mod_to_equations.
Import HList List.

Section Scalars.
  Context {width : Z} {word : Word.Interface.word width} {word_ok : word.ok word}.
  Context {byte : Word.Interface.word 8} {byte_ok : word.ok byte}.
  Context {mem : map.map word byte} {mem_ok : map.ok mem}.

  Definition littleendian (n : nat) (addr : word) (value : Z) : mem -> Prop :=
    array ptsto (word.of_Z 1) addr (tuple.to_list (LittleEndian.split n value)).

  (* TODO: this definition should also enforce that [value] fits
    within the specified width. Further, it might be better to take [value] as a Z. *)
  Definition scalar sz addr (value:word) : mem -> Prop :=
    littleendian (bytes_per (width:=width) sz) addr (word.unsigned value).
  
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
  
  Lemma load_sep sz addr (value:word) R m
    (Hsep : sep (scalar sz addr value) R m)
    : Memory.load sz m addr = Some (word.and value (word.of_Z (Z.ones (Z.of_nat (bytes_per (width:=width) sz)*8)))).
  Proof.
    cbv [load scalar littleendian] in *.
    erewrite load_bytes_sep by exact Hsep; apply f_equal.
    eapply Properties.word.unsigned_inj.
    rewrite combine_split.
    rewrite word.unsigned_and.
    rewrite !word.unsigned_of_Z.
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
  
  Lemma load_word_sep (sz := Syntax.access_size.word) addr value R m 
    (Hsep : sep (scalar sz addr value) R m)
    : Memory.load sz m addr = Some value.
  Proof.
    erewrite load_sep by exact Hsep; f_equal.
    cbv [bytes_per sz].
    eapply Properties.word.unsigned_inj.
    rewrite !word.unsigned_and, !word.unsigned_of_Z.
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
End Scalars.