Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Map.Separation.
Require Import coqutil.Map.OfListWord.
Require Import bedrock2.Array.
Require Import bedrock2.Scalars.

Import Init.Byte.

Section WithMem.
  Context {width} {BW: Bitwidth width} {word: word width} {mem: map.map word Byte.byte}
          {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Definition anybytes (a : word) (n : Z) (m : mem): Prop :=
    n <= 2^width /\ 
    exists bytes, Z.of_nat (length bytes) = n /\ m = map.of_list_word_at a bytes.

  Lemma anybytes_unique_domain: forall a n m1 m2,
      anybytes a n m1 ->
      anybytes a n m2 ->
      map.same_domain m1 m2.
  Proof.
    unfold anybytes. intros.
    destruct H as [vs1 [? []] ]. destruct H0 as [vs2 [? []] ]. subst.
    cbv [map.same_domain map.sub_domain]; setoid_rewrite map.get_of_list_word_at.
    split; intros ? ? ?%List.nth_error_Some_bound_index;
      eexists; eapply List.nth_error_nth'; Lia.lia.
    Unshelve. all : exact Byte.x00.
  Qed.

  Local Notation array := (array (mem:=mem) ptsto (word.of_Z 1)).
  Lemma array_1_to_anybytes: forall bs m (addr: word),
      array addr bs m ->
      anybytes addr (Z.of_nat (List.length bs)) m.
  Proof.
    cbv [anybytes]; intros.
    split; eauto using Nat2Z.is_nonneg, bytearray_fits_in_address_space; [].
    eapply array1_iff_eq_of_list_word_at in H; eauto.
    eauto using bytearray_fits_in_address_space.
  Qed.

  Lemma anybytes_to_array_1: forall m (addr: word) n,
      anybytes addr n m ->
      exists bs, array  addr bs m /\ List.length bs = Z.to_nat n.
  Proof.
    cbv [anybytes]; intros ? ? ? (?&?&?&?); subst; eexists; split;
      try eapply array1_iff_eq_of_list_word_at; eauto using Nat2Z.id.
  Qed.

  Lemma scalar_to_anybytes px x:
    Lift1Prop.impl1 (T := mem)
      (scalar px x)
      (anybytes px (Memory.bytes_per_word width)).
  Proof.
    intros m H; evar (bs: list byte);
      assert (array px bs m) by
        (subst bs; simple apply H).
    subst bs. erewrite <- bytes_per_width_bytes_per_word, <- split_bytes_per_len.
    rewrite HList.tuple.to_list_of_list in H0.
    eapply array_1_to_anybytes; eauto.
  Qed.

  Lemma anybytes_to_scalar px:
    Lift1Prop.impl1 (T := mem)
      (anybytes px (Memory.bytes_per_word width))
      (Lift1Prop.ex1 (scalar px)).
  Proof.
    intros m (bs & Harray & Hlen)%anybytes_to_array_1.
    apply scalar_of_bytes in Harray.
    - eexists; eassumption.
    - rewrite Hlen. clear H. destruct width_cases; subst; reflexivity || lia.
  Qed.

End WithMem.
