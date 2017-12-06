Require Import bbv.Word.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.PeanoNat.
Require Import compiler.Decidable.

Definition t: word 4 := $3.

Definition zcast{sz: nat}(sz': nat)(n: word sz): word sz'.
  destruct (Nat.compare sz sz') eqn: E.
  - apply nat_compare_eq in E. rewrite E in n. exact n.
  - apply nat_compare_Lt_lt in E.
Abort. (*
nat_compare_Gt_gt
forall n m : nat, (n ?= m) = Gt -> n > m
nat_compare_Lt_lt
forall n m : nat, (n ?= m) = Lt -> n < m
nat_compare_eq
*)

(* TODO we should also have a signed version, but there's no zToWord, only wordToZ *)
Definition zcast{sz: nat}(sz': nat)(n: word sz): word sz' :=
  natToWord sz' (wordToNat n).

(* old approach:
Definition zcast{sz: nat}(sz': nat)(n: word sz): word sz'.
  destruct (dec (sz <= sz')).
  - replace sz' with (sz + (sz' - sz)) by (apply le_plus_minus_r; assumption).
    exact (zext n _).
  - replace sz with ((sz - sz') + sz') in n.
    exact (split2 _ _ n).
    apply Nat.sub_add.
    apply Nat.lt_nge in n0.
    apply Nat.lt_le_incl. assumption.
Defined.
*)

Eval cbv in (zcast 1 t).

(*
Definition zcast{sz: nat}(sz': nat)(n: word sz): word sz'.
  destruct (dec (sz < sz')).
  - replace sz' with (sz + (sz' - sz)) by omega.
    exact (zext n _).
  - replace sz with ((sz - sz') + sz') in n by omega.
    exact (split2 _ _ n).
Defined.
too expensive to calculate
*)
