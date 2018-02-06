Require Import Coq.Lists.List.
Import ListNotations.
Require Import Coq.omega.Omega.
Require Import bbv.Word.
Require Import riscv.Decidable.
Require Import compiler.Tactics.
Require Import compiler.ListLib.
Require Import compiler.TotalMap.

Section MemBank.

  Variable D: Set.

  Inductive MemBank: nat -> Set :=
  | MemBankLeaf(value: D): MemBank 0
  | MemBankNode{n: nat}(left right: MemBank n): MemBank (S n).

  Definition destructLeaf(m: MemBank 0): D. inversion m. assumption. Defined.

  Definition destructNode{n: nat}(m: MemBank (S n)): MemBank n * MemBank n.
    inversion m. exact (left, right).
  Defined.

  Lemma destructNode_spec: forall n (m: MemBank (S n)),
    let (left, right) := destructNode m in m = MemBankNode left right.
  Admitted.

  Definition destructWS{n: nat}(w: word (S n)): bool * word n.
    inversion w. split; assumption.
  Defined.

  Fixpoint mbget{n: nat}: MemBank n -> word n -> D :=
    match n as n return MemBank n -> word n -> D with
    | 0 => fun m i => destructLeaf m
    | S n0 => fun m i =>
        let p1 := destructNode m in
        let (l, r) := p1 in
        let p2 := destructWS i in
        let (b, w) := p2 in
        if b then mbget r w else mbget l w
    end.

  Fixpoint mbset{n: nat}: MemBank n -> word n -> D -> MemBank n :=
    match n as n return MemBank n -> word n -> D -> MemBank n with
    | 0 => fun m i v => MemBankLeaf v
    | S n0 => fun m i v =>
        let p1 := destructNode m in
        let (l, r) := p1 in
        let p2 := destructWS i in
        let (b, w) := p2 in
        if b then (MemBankNode l (mbset r w v)) else (MemBankNode (mbset l w v) r)
    end.

  Fixpoint mbfill(n: nat)(v: D): MemBank n :=
    match n with
    | O => MemBankLeaf v
    | S n0 => MemBankNode (mbfill n0 v) (mbfill n0 v)
    end.

End MemBank.

Arguments mbget {D} {n} (m) (a).
Arguments mbset {D} {n} (m) (a) (v).
Arguments mbfill {D} (n) (v).
Arguments destructNode {D} {n} (m).
  
(* Eval cbv in (mbset (mbset (mbset (mbset (mbfill 4 0) $0 10) $8 11) $4 12) $12 13). *)

Instance MemBank_TotalMap(n: nat)(V: Set): TotalMap (MemBank V n) (word n) V := {|
  get := mbget;
  put := mbset;
|}.
- induction n; intros.
  + pose proof (shatter_word_0 k). subst k. reflexivity.
  + pose proof (shatter_word_S k) as P. destruct P as [b [w E]]. subst k.
    pose proof (destructNode_spec _ _ m).
    simpl.
    destruct (destructNode m) as [left right] eqn: E.
    destruct b; simpl; apply IHn.
- induction n; intros.
  + pose proof (shatter_word_0 k1). pose proof (shatter_word_0 k2). subst. contradiction.
  + pose proof (shatter_word_S k1) as P. destruct P as [b1 [w1 E1]].
    pose proof (shatter_word_S k2) as P. destruct P as [b2 [w2 E2]].
    subst.
    pose proof (destructNode_spec _ _ m).
    simpl.
    destruct (destructNode m) as [left right] eqn: E.
    destruct b1; destruct b2; simpl; try apply IHn; congruence.
Defined.
