Require Import bbv.Word.
Require Import bbv.DepEqNat.
Require Import Coq.Arith.Compare_dec.
Require Import Coq.Arith.Minus.
Require Import Coq.Arith.PeanoNat.
Require Import Omega.
Require Import riscv.util.Decidable.

(* TODO move to bbv *)
Definition ZToWord(sz: nat)(n: BinNums.Z): word sz :=
  match n with
  | BinNums.Z0 => $0
  | BinNums.Zpos p => posToWord sz p
  | BinNums.Zneg p => wneg (posToWord sz p)
  end.

(* A very simple definition of bit width cast. Reasons for abandoning it were:
   - not bit-oriented
   - it seemed slow (even though I believe now the slowness had a completely different cause)
*)

(* signed cast *)
Definition scast{sz: nat}(sz': nat)(n: word sz): word sz' :=
  ZToWord sz' (wordToZ n).

(* unsigned cast *)
Definition ucast{sz: nat}(sz': nat)(n: word sz): word sz' :=
  natToWord sz' (wordToNat n).


(* Bit-oriented approach, reason for abandoning it:
   - This definition matches on opaque proofs, so it doesn't reduce and we can't run examples
     inside Coq. *)

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

Lemma split_into_diff: forall (a b: nat), b < a -> a = b + (a - b).
  intros. apply le_plus_minus. apply Nat.lt_le_incl. assumption.
Defined.

Definition ext_cast_nonred(ext: forall sz1 : nat, word sz1 -> forall sz2 : nat, word (sz1 + sz2))
  {sz: nat}(sz': nat)(n: word sz): word sz'.
  destruct (dec (sz < sz')).
  - replace sz' with (sz + (sz' - sz)).
    + exact (ext _ n _).
    + symmetry. apply split_into_diff. assumption.
  - replace sz with ((sz - sz') + sz') in n.
    + exact (split2 _ _ n).
    + apply Nat.sub_add. apply Nat.le_ngt. assumption.
Defined.



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
