Require Export coqutil.Map.OfListWord coqutil.Map.Memory.

From Coq Require Import ZArith Lia.
Require Coq.Lists.List.
Require Import coqutil.sanity.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.List.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics coqutil.Datatypes.Option.
Require Import BinIntDef coqutil.Word.Bitwidth coqutil.Word.LittleEndianList.
Require Import bedrock2.Syntax.
Require Import coqutil.Byte.

Open Scope Z_scope.

Definition bytes_per_word width : Z := (width + 7) / 8.

Definition bytes_per {width} sz :=
  match sz with
    | access_size.one => 1 | access_size.two => 2 | access_size.four => 4
    | access_size.word => Z.to_nat (bytes_per_word width)
  end%nat.

Definition load {width} {mem : map.map (bits width) byte}
  sz (m : mem) (a: bits width): option (bits width) :=
  match load_Z m a (bytes_per (width:=width) sz) with
  | Some z => Some (bits.of_Z width z)
  | None => None
  end.

Definition store {width} {mem : map.map (bits width) byte}
  sz (m : mem) (a v : bits width) : option mem :=
  store_Z m a (bytes_per (width:=width) sz) (Zmod.unsigned v).

Definition anybytes {width} {mem : map.map (bits width) byte}
  (a : bits width) (n : Z) (m : mem) :=
  exists bs: list byte, map.of_list_word_at a bs = m /\
  Z.of_nat (length bs) = n /\ Z.of_nat (length bs) <= 2 ^ width.

Lemma anybytes_unique_domain {width} {BW: Bitwidth width} {mem : map.map (bits width) byte}
  {mem_ok: map.ok mem} a n (m1 m2 : mem) :
  anybytes a n m1 -> anybytes a n m2 -> map.same_domain m1 m2.
Proof.
  cbv [anybytes]; intros (?&?&?) (?&?&?); subst.
  cbv [map.same_domain map.sub_domain].
  setoid_rewrite (map.get_of_list_word_at width_pos); split; intros *.
  2: destruct List.nth_error eqn:A, (List.nth_error x) eqn:B.
  1: destruct List.nth_error eqn:A, (List.nth_error x0) eqn:B.
  all: intros; try congruence; eauto.
  all: rewrite List.nth_error_None in B.
  all: epose proof proj1 ((List.nth_error_Some _ _)) as HH; rewrite A in HH.
  all : specialize (HH ltac:(discriminate)); lia.
Qed.
