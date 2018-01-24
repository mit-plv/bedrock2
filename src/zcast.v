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

(*
(* signed cast *)
Definition scast{sz: nat}(sz': nat)(n: word sz): word sz' :=
  ZToWord sz' (wordToZ n).

(* unsigned cast *)
Definition ucast{sz: nat}(sz': nat)(n: word sz): word sz' :=
  natToWord sz' (wordToNat n).
*)

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

(*
Eval cbv in t.
Eval cbv in (scast 8 t).
*)

(*
Lemma split_into_diff: forall (a b: nat), b < a -> a = b + (a - b).
  intros. apply le_plus_minus. apply Nat.lt_le_incl. assumption.
Defined.

Definition ext_cast(ext: forall sz1 : nat, word sz1 -> forall sz2 : nat, word (sz1 + sz2))
  {sz: nat}(sz': nat)(n: word sz): word sz'.
  destruct (dec (sz < sz')).
  - replace sz' with (sz + (sz' - sz)).
    + exact (ext _ n _).
    + symmetry. apply split_into_diff. assumption.
  - replace sz with ((sz - sz') + sz') in n.
    + exact (split2 _ _ n).
    + apply Nat.sub_add. apply Nat.le_ngt. assumption.
Defined.
*)

(* Transport equality, only matching on eq_refl in contradictory cases, to make sure
   terms using this function reduce *)
Fixpoint nat_cast (P : nat -> Type) {n m} : n = m -> P n -> P m.
  refine match n, m return n = m -> P n -> P m with
         | O, O => fun _ => id
         | S n, S m => fun pf => @nat_cast (fun n => P (S n)) n m (f_equal pred pf)
         | _, _ => fun pf => match _ pf : False with end
         end;
    clear; abstract congruence.
Defined. (* thx Jason *)

Lemma nat_cast_eq_rect: forall (P : nat -> Type),
  forall (n m : nat)  (e: n = m) (pn: P n),
  nat_cast P e pn = eq_rect n P pn m e.
Proof.
  destruct e.
  revert dependent P; induction n; simpl; intros.
  - reflexivity.
  - rewrite IHn. reflexivity.
Qed. (* thx Clement *)

Lemma nat_cast_proof_irrel: forall (P : nat -> Type),
  forall (n m : nat)  (e1 e2: n = m) (pn: P n),
  nat_cast P e1 pn = nat_cast P e2 pn.
Proof.
  destruct e1.
  revert dependent P; induction n; simpl; intros.
  - reflexivity.
  - erewrite IHn. reflexivity.
Qed.

Lemma nat_cast_same: forall (P: nat -> Type) (s: nat) (n: P s),
  nat_cast P eq_refl n = n.
Proof.
  intros. rewrite nat_cast_eq_rect. reflexivity.
Qed.

Lemma nat_cast_fuse: forall (P: nat -> Type) (n1 n2 n3: nat) (e12: n1 = n2) (e23: n2 = n3) (x: P n1),
  nat_cast P e23 (nat_cast P e12 x) = nat_cast P (eq_trans e12 e23) x.
Proof.
  destruct e12.
  destruct e23.
  intros.
  rewrite nat_cast_same.
  reflexivity.
Qed.

Require Import Omega.

(* This function implements the following expression:
  "if sz' > sz then (ext sz n (sz' - sz)) else (split2 (sz - sz') sz' n)"
But in order to get the types right, it needs to be much more complicated. *)
Definition ext_cast(ext: forall sz1 : nat, word sz1 -> forall sz2 : nat, word (sz1 + sz2))
  {sz: nat}(sz': nat)(n: word sz): word sz'.
  destruct (Compare_dec.gt_dec sz' sz) as [H|H].
  { refine (nat_cast word _ (ext sz n (sz' - sz))).
    clear -H; abstract omega. }
  { refine (split2 (sz - sz') sz' (nat_cast word _ n)).
    clear -H; abstract omega. }
Defined.

Definition signed_cast{sz: nat}: forall (sz': nat) (n: word sz), word sz' := ext_cast sext.

Definition unsigned_cast{sz: nat}: forall (sz': nat) (n: word sz), word sz' := ext_cast zext.

Eval cbv in t.
Eval cbv in (signed_cast 8 t).

Definition scast{sz: nat}(sz': nat)(n: word sz): word sz' :=
  signed_cast sz' n.

Definition ucast{sz: nat}(sz': nat)(n: word sz): word sz' :=
  unsigned_cast sz' n.
