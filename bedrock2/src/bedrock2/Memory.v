Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Coq.Lists.List.
Require Import coqutil.sanity.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList coqutil.Datatypes.List.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics coqutil.Datatypes.Option.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.LittleEndianList.
Require Import bedrock2.Syntax.
Require Import coqutil.Byte.
Require Import coqutil.Map.OfListWord.

Open Scope Z_scope.

Definition bytes_per_word(width: Z): Z := (width + 7) / 8.

Module WithoutTuples. Section Memory.
  Context {width: Z} {word: word width} {mem: map.map word byte}.
  Definition footprint (a : word) (n : nat) : list word :=
    List.map (fun i => word.add a (word.of_Z (Z.of_nat i))) (List.seq 0 n).
  Definition load_bytes (m : mem) (a : word) (n : nat) : option (list byte) :=
    option_all (List.map (map.get m) (footprint a n)).
  Definition unchecked_store_bytes (m : mem) (a : word) (bs : list byte) :=
    map.putmany m (map.of_list_word_at a bs).
  Definition store_bytes (m : mem)(a : word) (bs : list byte): option mem :=
    match load_bytes m a (length bs) with
    | Some _ => Some (unchecked_store_bytes m a bs)
    | None => None (* some addresses were invalid *)
    end.

  Local Notation "a [ i ]" := (List.nth_error a i) (at level 9, format "a [ i ]").

  Lemma length_footprint a n : length (footprint a n) = n.
  Proof. cbv [footprint]. rewrite List.map_length, List.seq_length; trivial. Qed.
  Lemma nth_error_footprint_inbounds a n i (H : lt i n)
    : (footprint a n)[i] = Some (word.add a (word.of_Z (Z.of_nat i))).
  Proof.
    cbv [footprint].
    erewrite List.map_nth_error; trivial.
    rewrite List.nth_error_nth' with (d:=O); rewrite ?List.seq_length; trivial; [].
    rewrite List.seq_nth; trivial.
  Qed.

  Lemma length_load_bytes m a n bs (H : load_bytes m a n = Some bs)
    : length bs = n.
  Proof.
    eapply length_option_all in H.
    pose proof length_footprint a n.
    pose proof List.map_length (map.get m) (footprint a n).
    congruence.
  Qed.
  Lemma nth_error_load_bytes m a n bs (H : load_bytes m a n = Some bs) i (Hi : lt i n)
    : List.nth_error bs i = map.get m (word.add a (word.of_Z (Z.of_nat i))).
  Proof.
    cbv [load_bytes] in *.
    epose proof @nth_error_option_all _ _ _ _ H as Hii.
    rewrite List.map_length, length_footprint in Hii.
    case (Hii Hi) as (b&Hbl&Hbr); clear Hii; rewrite Hbr; clear Hbr.
    erewrite List.map_nth_error in Hbl by eauto using nth_error_footprint_inbounds.
    injection Hbl; congruence.
  Qed.

  Lemma load_bytes_None m a n (H : load_bytes m a n = None)
    : exists i, lt i n /\ map.get m (word.add a (word.of_Z (Z.of_nat i))) = None.
  Proof.
    eapply option_all_None in H; case H as (i&Hi); exists i.
    eapply nth_error_map_Some in Hi; case Hi as (x&Hfx&Hmx).
    pose proof proj1 (List.nth_error_Some (footprint a n) i) ltac:(congruence).
    rewrite length_footprint in H; split; trivial.
    eapply nth_error_footprint_inbounds with (a:=a) in H.
    congruence.
  Qed.

  Lemma load_bytes_all m a n
    (H : forall i, lt i n -> exists b, map.get m (word.add a (word.of_Z (Z.of_nat i))) = Some b)
    : exists bs, load_bytes m a n = Some bs.
  Proof.
    destruct (load_bytes m a n) eqn:HX; eauto.
    eapply load_bytes_None in HX; destruct HX as (?&?&?). firstorder congruence.
    exact nil.
  Qed.

  Import Word.Properties.
  Context {mem_ok: map.ok mem} {word_ok: word.ok word}.
  Local Infix "$+" := map.putmany (at level 70).
  Local Notation "xs $@ a" := (map.of_list_word_at a xs) (at level 10, format "xs $@ a").
  Lemma load_bytes_of_putmany_bytes_at bs a mR n (Hn : length bs = n) (Hl : Z.of_nat n < 2^width)
    : load_bytes (mR $+ bs$@a) a n = Some bs.
  Proof.
    destruct (load_bytes (mR $+ bs$@a) a n) eqn:HN in *; cycle 1.
    { exfalso; eapply load_bytes_None in HN; case HN as (i&?&?).
      case (Properties.map.putmany_spec mR (bs$@a) (word.add a (word.of_Z (BinIntDef.Z.of_nat i)))) as [(?&?&?)| (?&?) ]; try congruence.
      rewrite map.get_of_list_word_at in H1; eapply List.nth_error_None in H1.
      revert H1.
      rewrite word.word_sub_add_l_same_l, word.unsigned_of_Z.
      cbv [word.wrap]; rewrite Z.mod_small, Znat.Nat2Z.id; eauto; blia. }
    transitivity (Some l); try congruence; f_equal; subst n.
    symmetry; eapply List.nth_error_ext_samelength.
    { symmetry; eauto using length_load_bytes. }
    intros.
    pose proof nth_error_load_bytes _ a _ _ HN i ltac:(trivial) as HH.
    epose proof H; eapply List.nth_error_nth' with (d:=Byte.x00) in H.
    erewrite Properties.map.get_putmany_right in HH; cycle 1.
    { rewrite map.get_of_list_word_at.
      rewrite word.word_sub_add_l_same_l, word.unsigned_of_Z.
      cbv [word.wrap]; rewrite Z.mod_small, Znat.Nat2Z.id; eauto; blia. }
    congruence.
  Qed.
End Memory. End WithoutTuples.

Section Memory.
  Context {width: Z} {word: word width} {mem: map.map word byte}.

  Definition bytes_per sz :=
    match sz with
      | access_size.one => 1 | access_size.two => 2 | access_size.four => 4
      | access_size.word => Z.to_nat (bytes_per_word width)
    end%nat.

  Definition load_Z(sz: access_size)(m: mem)(a: word): option Z :=
    match WithoutTuples.load_bytes m a (bytes_per sz) with
    | Some bs => Some (LittleEndianList.le_combine bs)
    | None => None
    end.

  Definition store_Z(sz: access_size)(m: mem)(a: word)(v: Z): option mem :=
    WithoutTuples.store_bytes m a (LittleEndianList.le_split (bytes_per sz) v).

  Definition load(sz: access_size)(m: mem)(a: word): option word :=
    match load_Z sz m a with
    | Some v => Some (word.of_Z v)
    | None => None
    end.

  Definition store(sz: access_size)(m: mem)(a: word)(v: word): option mem :=
    store_Z sz m a (word.unsigned v).


  Section Deprecated. (* The below functions needlessly use tuples for what can be done with lists *)


  (* deprecated since 2025 *)
  Definition footprint(a: word)(sz: nat): tuple word sz :=
    tuple.unfoldn (fun w => word.add w (word.of_Z 1)) sz a.

  (* deprecated since 2025 *)
  Definition load_bytes(sz: nat)(m: mem)(addr: word): option (tuple byte sz) :=
    map.getmany_of_tuple m (footprint addr sz).

  (* deprecated since 2025 *)
  Definition unchecked_store_bytes(sz: nat)(m: mem)(a: word)(bs: tuple byte sz): mem :=
    map.putmany_of_tuple (footprint a sz) bs m.

  (* deprecated since 2025 *)
  Definition store_bytes(sz: nat)(m: mem)(a: word)(v: tuple byte sz): option mem :=
    match load_bytes sz m a with
    | Some _ => Some (unchecked_store_bytes sz m a v)
    | None => None (* some addresses were invalid *)
    end.

  Context {mem_ok: map.ok mem}.
  Context {word_ok: word.ok word}.

  Lemma to_list_footprint a sz :
    tuple.to_list (footprint a sz) = WithoutTuples.footprint a sz.
  Proof.
    revert a; induction sz; cbn; intros; f_equal.
    { rewrite Properties.word.add_0_r; trivial. }
    { cbv [footprint] in IHsz. rewrite IHsz, <-List.seq_shift, List.map_map.
      eapply List.map_ext; intros.
      rewrite Nat2Z.inj_succ; cbv [BinInt.Z.succ]; rewrite Properties.word.ring_morph_add.
      rewrite <-!Properties.word.add_assoc; f_equal.
      rewrite Properties.word.add_comm; f_equal. }
  Qed.

  Lemma anybytes_unique_domain: forall a n m1 m2,
      anybytes a n m1 ->
      anybytes a n m2 ->
      map.same_domain m1 m2.
  Proof.
    unfold anybytes. intros.
    destruct H as [vs1 ?]. destruct H0 as [vs2 ?].
    eapply map.of_disjoint_list_zip_same_domain; eassumption.
  Qed.

  Lemma to_list_getmany_of_tuple [key value] [map : map.map key value] sz ks (m : map) :
    option_map tuple.to_list (map.getmany_of_tuple m (sz:=sz) ks) =
    option_all (List.map (map.get m) (tuple.to_list ks)).
  Proof.
    induction sz; cbn; trivial.
    case map.get; trivial; intros.
    erewrite <-IHsz; clear IHsz. cbv [map.getmany_of_tuple].
    case tuple.option_all; trivial.
  Qed.

  Lemma to_list_load_bytes sz m a :
    option_map tuple.to_list (load_bytes sz m a) = WithoutTuples.load_bytes m a sz.
  Proof.
    cbv [load_bytes]. rewrite to_list_getmany_of_tuple, to_list_footprint; trivial.
  Qed.

  Lemma unchecked_store_bytes_correct sz m a bs :
    unchecked_store_bytes sz m a bs = WithoutTuples.unchecked_store_bytes m a (tuple.to_list bs).
  Proof.
    cbv [unchecked_store_bytes WithoutTuples.unchecked_store_bytes].
    revert a; induction sz; cbn; intros; rewrite ?map.of_list_word_nil, ?map.putmany_empty_r; trivial.
    rewrite map.of_list_word_at_cons, <-map.put_putmany_commute; f_equal.
    erewrite <-IHsz; trivial.
  Qed.

  Lemma store_bytes_correct sz m a bs :
    store_bytes sz m a bs = WithoutTuples.store_bytes m a (tuple.to_list bs).
  Proof.
    cbv [store_bytes WithoutTuples.store_bytes].
    rewrite <-to_list_load_bytes, tuple.length_to_list; case load_bytes as []; cbn; trivial.
    rewrite unchecked_store_bytes_correct; trivial.
  Qed.
  End Deprecated.
End Memory.
