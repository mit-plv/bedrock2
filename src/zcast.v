Require Import bbv.Word.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.PeanoNat.
Require Import compiler.Decidable.

Definition t: word 4 := wneg $3.

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

(*
Definition zToWord(sz: nat)(z: BinNums.Z): word sz :=
  match z with
  | BinNums.Z0 => $0
  | BinNums.Zpos n => $ (BinPos.Pos.to_nat n)
  | BinNums.Zneg n => wneg $ (BinPos.Pos.to_nat n)
  end.
*)

(* TODO move to bbv *)
Definition ZToWord(sz: nat)(n: BinNums.Z): word sz :=
  match n with
  | BinNums.Z0 => $0
  | BinNums.Zpos p => posToWord sz p
  | BinNums.Zneg p => wneg (posToWord sz p)
  end.

(* signed cast *)
Definition scast{sz: nat}(sz': nat)(n: word sz): word sz' :=
  ZToWord sz' (wordToZ n).

(* unsigned cast *)
Definition ucast{sz: nat}(sz': nat)(n: word sz): word sz' :=
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

Eval cbv in t.
Eval cbv in (scast 8 t).

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
