Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Coq.Lists.List.
Require Import coqutil.sanity.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList coqutil.Datatypes.List.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics coqutil.Datatypes.Option.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.LittleEndianList.
Require Import bedrock2.Notations bedrock2.Syntax.
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

  Definition ftprint(a: word)(n: Z): list word :=
    List.unfoldn (fun w => word.add w (word.of_Z 1)) (Z.to_nat n) a.

  Definition anybytes(a: word)(n: Z)(m: mem): Prop :=
    exists bytes: list byte, map.of_disjoint_list_zip (ftprint a n) bytes = Some m.

  Definition footprint(a: word)(sz: nat): tuple word sz :=
    tuple.unfoldn (fun w => word.add w (word.of_Z 1)) sz a.

  Definition load_bytes(sz: nat)(m: mem)(addr: word): option (tuple byte sz) :=
    map.getmany_of_tuple m (footprint addr sz).

  Definition unchecked_store_bytes(sz: nat)(m: mem)(a: word)(bs: tuple byte sz): mem :=
    map.putmany_of_tuple (footprint a sz) bs m.

  Definition store_bytes(sz: nat)(m: mem)(a: word)(v: tuple byte sz): option mem :=
    match load_bytes sz m a with
    | Some _ => Some (unchecked_store_bytes sz m a v)
    | None => None (* some addresses were invalid *)
    end.

  Definition bytes_per sz :=
    match sz with
      | access_size.one => 1 | access_size.two => 2 | access_size.four => 4
      | access_size.word => Z.to_nat (bytes_per_word width)
    end%nat.

  Definition load_Z(sz: access_size)(m: mem)(a: word): option Z :=
    match load_bytes (bytes_per sz) m a with
    | Some bs => Some (LittleEndianList.le_combine (tuple.to_list bs))
    | None => None
    end.

  Definition store_Z(sz: access_size)(m: mem)(a: word)(v: Z): option mem :=
    store_bytes _ m a (tuple.of_list (LittleEndianList.le_split (bytes_per sz) v)).

  Definition load(sz: access_size)(m: mem)(a: word): option word :=
    match load_Z sz m a with
    | Some v => Some (word.of_Z v)
    | None => None
    end.

  Definition store(sz: access_size)(m: mem)(a: word)(v: word): option mem :=
    store_Z sz m a (word.unsigned v).

  Lemma load_None: forall sz m a,
      8 <= width -> (* note: [0 < width] is sufficient *)
      map.get m a = None ->
      load sz m a = None.
  Proof.
    intros. destruct sz; cbv [load load_Z load_bytes map.getmany_of_tuple footprint bytes_per bytes_per_word tuple.option_all tuple.map tuple.unfoldn];
    try solve [ rewrite H0; reflexivity].
    destruct (Z.to_nat ((width + 7) / 8)) eqn: E.
    - exfalso.
      assert (0 < (width + 7) / 8) as A. {
        apply Z.div_str_pos. blia.
      }
      change O with (Z.to_nat 0) in E.
      apply Z2Nat.inj in E; blia.
    - cbv [tuple.option_all tuple.map tuple.unfoldn].
      rewrite H0.
      reflexivity.
  Qed.

  Context {mem_ok: map.ok mem}.
  Context {word_ok: word.ok word}.

  Lemma store_preserves_domain: forall sz m a v m',
      store sz m a v = Some m' -> map.same_domain m m'.
  Proof.
    destruct sz;
      cbv [store store_Z store_bytes bytes_per load_bytes unchecked_store_bytes];
      intros;
      (destruct_one_match_hyp; [|discriminate]);
      inversion_option;
      subst;
      eapply map.putmany_of_tuple_preserves_domain;
      eassumption.
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

End Memory.
