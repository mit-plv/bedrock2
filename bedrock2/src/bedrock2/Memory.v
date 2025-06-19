Require Export coqutil.Map.OfListWord coqutil.Map.Memory.

From Coq Require Import ZArith Lia.
Require Coq.Lists.List.
Require Import coqutil.sanity.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList coqutil.Datatypes.List.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics coqutil.Datatypes.Option.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.LittleEndianList.
Require Import bedrock2.Syntax.
Require Import coqutil.Byte.

Open Scope Z_scope.

Definition bytes_per_word width : Z := (width + 7) / 8.

Definition bytes_per {width} sz :=
  match sz with
    | access_size.one => 1 | access_size.two => 2 | access_size.four => 4
    | access_size.word => Z.to_nat (bytes_per_word width)
  end%nat.

Definition load {width} {word : word width} {mem : map.map word byte}
  sz (m : mem) (a: word): option word :=
  match load_Z m a (bytes_per (width:=width) sz) with
  | Some z => Some (word.of_Z z)
  | None => None
  end.

Definition store {width} {word : word width} {mem : map.map word byte}
  sz (m : mem) (a v : word) : option mem :=
  store_Z m a (bytes_per (width:=width) sz) (word.unsigned v).

Definition anybytes {width} {word : word width} {mem : map.map word byte}
  (a : word) (n : Z) (m : mem) :=
  exists bs: list byte, map.of_list_word_at a bs = m /\
  Z.of_nat (length bs) = n /\ Z.of_nat (length bs) <= 2 ^ width.

Lemma anybytes_unique_domain {width} {word : word width} {mem : map.map word byte}
  {mem_ok: map.ok mem} {word_ok: word.ok word} a n (m1 m2 : mem) :
  anybytes a n m1 -> anybytes a n m2 -> map.same_domain m1 m2.
Proof.
  cbv [anybytes]; intros (?&?&?) (?&?&?); subst.
  cbv [map.same_domain map.sub_domain].
  setoid_rewrite @map.get_of_list_word_at; try exact _; split; intros *.
  2: destruct List.nth_error eqn:A, (List.nth_error x) eqn:B.
  1: destruct List.nth_error eqn:A, (List.nth_error x0) eqn:B.
  all: intros; try congruence; eauto.
  all: rewrite List.nth_error_None in B.
  all: epose proof proj1 ((List.nth_error_Some _ _)) as HH; rewrite A in HH.
  all : specialize (HH ltac:(discriminate)); lia.
Qed.

Module Deprecated. (* The below functions needlessly use tuples for what can be done with lists *)
Section Deprecated.
  Context {width: Z} {word: word width} {mem: map.map word byte}.
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
    tuple.to_list (footprint a sz) = coqutil.Map.Memory.footprint a sz.
  Proof.
    revert a; induction sz; cbn; intros; f_equal.
    { rewrite Properties.word.add_0_r; trivial. }
    { cbv [footprint] in IHsz. rewrite IHsz, <-List.seq_shift, List.map_map.
      eapply List.map_ext; intros.
      rewrite Nat2Z.inj_succ; cbv [BinInt.Z.succ]; rewrite Properties.word.ring_morph_add.
      rewrite <-!Properties.word.add_assoc; f_equal.
      rewrite Properties.word.add_comm; f_equal. }
  Qed.

  Lemma to_list_load_bytes sz m a :
    option_map tuple.to_list (load_bytes sz m a) = coqutil.Map.Memory.load_bytes m a sz.
  Proof.
    cbv [load_bytes]. rewrite map.to_list_getmany_of_tuple, to_list_footprint; trivial.
  Qed.

  Lemma unchecked_store_bytes_correct sz m a bs :
    unchecked_store_bytes sz m a bs = coqutil.Map.Memory.unchecked_store_bytes m a (tuple.to_list bs).
  Proof.
    cbv [unchecked_store_bytes coqutil.Map.Memory.unchecked_store_bytes].
    revert a; induction sz; cbn; intros; rewrite ?map.of_list_word_nil, ?map.putmany_empty_r; trivial.
    rewrite map.of_list_word_at_cons, <-map.put_putmany_commute; f_equal.
    erewrite <-IHsz; trivial.
  Qed.

  Lemma store_bytes_correct sz m a bs :
    store_bytes sz m a bs = coqutil.Map.Memory.store_bytes m a (tuple.to_list bs).
  Proof.
    cbv [store_bytes coqutil.Map.Memory.store_bytes].
    rewrite <-to_list_load_bytes, tuple.length_to_list; case load_bytes as []; cbn; trivial.
    rewrite unchecked_store_bytes_correct; trivial.
  Qed.
End Deprecated.
End Deprecated.
