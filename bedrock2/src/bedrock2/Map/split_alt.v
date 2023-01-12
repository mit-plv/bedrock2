Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.Map.Separation.
Require Export bedrock2.Map.DisjointUnion.

Module map. Section __.
  Context {key value} {map : map.map key value} {ok: map.ok map}.
  Context {key_eqb: key -> key -> bool} {key_eq_dec: EqDecider key_eqb}.

  Lemma split_alt: forall {m m1 m2: map}, map.split m m1 m2 <-> mmap.split m m1 m2.
  Proof.
    unfold map.split, mmap.split, mmap.du, map.du, mmap.of_option. split; intros; fwd.
    - eapply map.disjointb_spec in Hp1. rewrite Hp1. reflexivity.
    - split. 1: reflexivity. eapply map.disjointb_spec. assumption.
  Qed.
End __. End map.
