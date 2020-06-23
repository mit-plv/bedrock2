Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Coq.Lists.List.
Require Import coqutil.sanity.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList coqutil.Datatypes.List.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics coqutil.Datatypes.Option.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.LittleEndian.
Require Import bedrock2.Notations bedrock2.Syntax.
Require Import coqutil.Byte.

Open Scope Z_scope.

Definition bytes_per_word(width: Z): Z := (width + 7) / 8.

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
    | Some bs => Some (LittleEndian.combine _ bs)
    | None => None
    end.

  Definition store_Z(sz: access_size)(m: mem)(a: word)(v: Z): option mem :=
    store_bytes (bytes_per sz) m a (LittleEndian.split _ v).

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
