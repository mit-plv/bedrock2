Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.BitOps.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.rewr.
Require Import coqutil.Z.Lia.


Section Lemmas.
  Context {width: Z} {word: word.word width} {word_ok: word.ok word}.

  Add Ring wring: (@word.ring_theory width word word_ok).

  Lemma add_0_l: forall x, word.add (word.of_Z 0) x = x. Proof. intros. ring. Qed.
  Lemma add_0_r: forall x, word.add x (word.of_Z 0) = x. Proof. intros. ring. Qed.
  Lemma mul_0_l: forall x, word.mul (word.of_Z 0) x = word.of_Z 0. Proof. intros. ring. Qed.
  Lemma mul_0_r: forall x, word.mul x (word.of_Z 0) = word.of_Z 0. Proof. intros. ring. Qed.
  Lemma mul_1_l: forall x, word.mul (word.of_Z 1) x = x. Proof. intros. ring. Qed.
  Lemma mul_1_r: forall x, word.mul x (word.of_Z 1) = x. Proof. intros. ring. Qed.

  Lemma sextend_width_nop: forall (w v: Z),
    w = width ->
    word.of_Z (BitOps.signExtend w v) = word.of_Z v.
  Proof.
    intros. subst. unfold BitOps.signExtend. apply word.unsigned_inj.
    rewrite! word.unsigned_of_Z.
    pose proof (@word.width_pos _ _ word_ok).
    pose proof (Z.pow_pos_nonneg 2 width).
    unfold word.wrap.
    remember (2 ^ width) as M.
    remember (2 ^ (width - 1)) as M2.
    rewrite Z.add_mod by blia.
    rewrite Zminus_mod by blia.
    rewrite Z.mod_mod by blia.
    rewrite <- (Z.mod_mod M2 M) at 2 by blia.
    rewrite <- Zminus_mod by blia.
    rewrite Z.add_simpl_r.
    rewrite Z.mod_mod by blia.
    reflexivity.
  Qed.


End Lemmas.

Ltac simpl_Zcsts :=
  repeat so fun hyporgoal => match hyporgoal with
         | context [Z.add ?a ?b] =>
           match isZcst a with true => idtac end;
           match isZcst b with true => idtac end;
           let r := eval cbv in (Z.add a b) in change (Z.add a b) with r in *
         | context [Z.sub ?a ?b] =>
           match isZcst a with true => idtac end;
           match isZcst b with true => idtac end;
           let r := eval cbv in (Z.sub a b) in change (Z.sub a b) with r in *
         | context [Z.mul ?a ?b] =>
           match isZcst a with true => idtac end;
           match isZcst b with true => idtac end;
           let r := eval cbv in (Z.mul a b) in change (Z.mul a b) with r in *
         | context [Z.of_nat ?x] =>
           match isnatcst x with true => idtac end;
           let r := eval cbv in (Z.of_nat x) in change (Z.of_nat x) with r in *
         end.

Ltac simpl_word_exprs_getEq OK t :=
  match t with
  | context[ @word.add ?wi ?wo (word.of_Z 0) ?x ] => constr:(@add_0_l wi wo OK x)
  | context[ @word.add ?wi ?wo ?x (word.of_Z 0) ] => constr:(@add_0_r wi wo OK x)
  | context[ @word.mul ?wi ?wo (word.of_Z 0) ?x ] => constr:(@mul_0_l wi wo OK x)
  | context[ @word.mul ?wi ?wo ?x (word.of_Z 0) ] => constr:(@mul_0_r wi wo OK x)
  | context[ @word.mul ?wi ?wo (word.of_Z 1) ?x ] => constr:(@mul_1_l wi wo OK x)
  | context[ @word.mul ?wi ?wo ?x (word.of_Z 1) ] => constr:(@mul_1_r wi wo OK x)
  | context[ word.of_Z (BitOps.signExtend ?w ?v)] => constr:(@sextend_width_nop _ _ OK w v)
  end.

Hint Rewrite
     Nat2Z.inj_succ
     Nat2Z.inj_add
     Nat2Z.inj_mul
     List.app_length
  : rew_simpl_Z_nat.

Hint Unfold
     Z.succ
  : unf_simpl_Z_nat.

Ltac simpl_Z_nat_getEq t :=
  match t with
  (* no assumptions: *)
  | context[ Z.of_nat (S ?n) ] => constr:(Nat2Z.inj_succ n)
  | context[ Z.of_nat (?n + ?m) ] => constr:(Nat2Z.inj_add n m)
  | context[ Z.of_nat (?n * ?m) ] => constr:(Nat2Z.inj_mul n m)
  | context[ length (?l1 ++ ?l2) ] => constr:(List.app_length l1 l2)
  (* only assumption: 0 <= a *)
  | context[ Z.of_nat (Z.to_nat ?a) ] => constr:(Z2Nat.id a)
  end.

Ltac simpl_Z_nat_step :=
  (* NOTE: For consistency with Coq's "rewrite", "rewr" adopts the same unintuitive
     priorities between "by" and "||", namely that "||" binds stronger than "by".
     For instance,
        rewrite ?Z.mul_assoc by fail || rewrite Z.add_assoc by fail
     is
        rewrite ?Z.mul_assoc by (fail || rewrite Z.add_assoc by fail)
     instead of
        (rewrite ?Z.mul_assoc by fail) || (rewrite Z.add_assoc by fail)
     and "rewr" does the same, so we do need parentheses here *)
  (rewr simpl_Z_nat_getEq in * by assumption) ||
  autounfold with unf_simpl_Z_nat in * ||
  cbn [List.length] in * ||
  simpl_Zcsts.

Ltac simpl_Z_nat := repeat simpl_Z_nat_step.

Ltac simpl_word_exprs OK :=
  simpl_Z_nat;
  lazymatch type of OK with
  | @word.ok ?width ?Inst =>
    rewr (simpl_word_exprs_getEq OK) in * by (reflexivity || congruence)
  | _ => fail 10000 "wordok is not of type word.ok"
  end.

Ltac solve_word_eq OK :=
  match goal with
  | |- @eq (@word.rep _ _) ?x ?y =>
    tryif (assert_succeeds (assert (word.sub x x = word.of_Z 0) by ring))
    then idtac
    else fail 10000 "ring is not available, did you forget 'Add Ring'?"
  | _ => fail 1 "wrong shape of goal"
  end;
  subst;
  try reflexivity;
  clear;
  simpl;
  simpl_word_exprs OK;
  (ring || (try reflexivity)).
