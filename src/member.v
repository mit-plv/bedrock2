(* eq_member_dec based on Clement's solution posted on PLV mailing list in May 2017 *)
Require Import Coq.Arith.PeanoNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import riscv.Decidable.

Inductive member{T: Type}: list T -> Type :=
  | member_here: forall h t, member (h :: t)
  | member_there: forall h t, member t -> member (h :: t).

Fixpoint member2nat{T: Type}{xs: list T}(m: member xs): nat :=
 match m with
 | member_here x xs => 0
 | member_there x xs m' => 1 + member2nat m'
 end.

Open Scope list_scope.

Definition destruct_members{T: Type}{xs: list T}(m: member xs):
  match xs return (member xs -> Prop) with
  | nil => fun m => False
  | x :: xs' => fun m => m = member_here x xs' \/ exists m', m = member_there x xs' m'
  end m.
Proof.
  destruct m.
  - left; reflexivity.
  - right; exists m; reflexivity.
Defined.

(* when returning "Set", we cannot match on the \/ of the above destruct_members, therefore
   a different destruct_member below: *)

Definition destruct_member{T: Type}{xs: list T}(m: member xs)(R: Type):
  match xs return (member xs -> Type) with
  | nil => fun m => False
  | x :: xs' => fun m => (m = member_here x xs' -> R) ->
                         (forall m', m = member_there x xs' m' -> R) -> R
  end m.
Proof.
  destruct m; intros C1 C2.
  - apply (C1 eq_refl).
  - apply (C2 _ eq_refl).
Defined.

Lemma members2nat_inj: forall {T: Type} {xs: list T} (m m': member xs),
   member2nat m = member2nat m' ->
   m = m'.
Proof.
  intros.
  induction m;
  apply (destruct_member m'); intros; subst; simpl in *; try congruence.
  rewrite (IHm m'0); auto.
Defined.

Definition eq_member_dec{T: Type}(xs : list T): DecidableEq (member xs).
  intros m m'. unfold Decidable.
  refine (if Nat.eq_dec (member2nat m) (member2nat m') then _ else _).
  - apply members2nat_inj in e. left; assumption.
  - right. intro H. apply n. f_equal. assumption.
Defined.


Module ReductionTest.

  Parameter v1 v2 v3: nat.

  Definition ll := [v1; v2; v3].

  Definition mm: member ll := member_there v1 _ (member_here v2 [v3]).

  Definition mm': member ll := member_there v1 _ (member_there v2 _ (member_here v3 [])).

  Goal (if (eq_member_dec ll mm mm') then 1 else 0) = 0. Proof. cbv. reflexivity. Qed.

End ReductionTest.


Fixpoint member_app_r{T: Type}(l1 l2: list T)(m: member l1): member (l1 ++ l2).
  destruct l1.
  - inversion m.
  - destruct m.
    + apply member_here.
    + rewrite <- app_comm_cons. apply member_there.
      apply member_app_r. exact m.
Defined.

Fixpoint member_app_l{T: Type}(l1 l2: list T)(m: member l2): member (l1 ++ l2).
  destruct l1.
  - exact m.
  - rewrite <- app_comm_cons. apply member_there.
    apply member_app_l. exact m.
Defined.

Definition member_app_13{T: Type}(l1 l2 l3: list T)(m: member l1): member (l1 ++ l2 ++ l3).
  apply member_app_r.
  exact m.
Defined.

Definition member_app_23{T: Type}(l1 l2 l3: list T)(m: member l2): member (l1 ++ l2 ++ l3).
  apply member_app_l.
  apply member_app_r.
  exact m.
Defined.

Definition member_app_33{T: Type}(l1 l2 l3: list T)(m: member l3): member (l1 ++ l2 ++ l3).
  apply member_app_l.
  apply member_app_l.
  exact m.
Defined.

Fixpoint member_get{T: Type}{l: list T}(m: member l): T :=
  match m with
  | member_here h _ => h
  | member_there _ t m0 => member_get m0
  end.

Fixpoint member_remove{T: Type}(dec: DecidableEq T)(r: T)(l: list T)(m: member l)
  (ne: member_get m <> r) {struct m}: member (remove dec r l).
  destruct m.
  - (* here *)
    simpl in *. destruct (dec r h).
    + subst. contradiction.
    + apply member_here.
  - (* there *)
    simpl in *. destruct (dec r h).
    + subst. apply (member_remove _ _ _ _ _ ne).
    + apply member_there. apply (member_remove _ _ _ _ _ ne).
Defined.
