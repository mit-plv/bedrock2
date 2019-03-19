Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.BitOps.
Require Import coqutil.Tactics.Tactics.


Local Unset Universe Polymorphism. (* for Add Ring *)

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
    word.of_Z (BitOps.sextend w v) = word.of_Z v.
  Proof.
    intros. subst. unfold BitOps.sextend. apply word.unsigned_inj.
    rewrite! word.unsigned_of_Z.
    pose proof (@word.width_pos _ _ word_ok).
    pose proof (Z.pow_pos_nonneg 2 width).
    remember (2 ^ width) as M.
    remember (2 ^ (width - 1)) as M2.
    rewrite Z.add_mod by omega. (* lia fails! *)
    rewrite Zminus_mod by omega.
    rewrite Z.mod_mod by omega.
    rewrite <- (Z.mod_mod M2 M) at 2 by omega.
    rewrite <- Zminus_mod by omega.
    rewrite Z.add_simpl_r.
    rewrite Z.mod_mod by omega.
    reflexivity.
  Qed.


End Lemmas.

(* If "rewrite (sextend_width_nop (word_ok := OK))" encounters a term of the form
   "(word.of_Z ?v)", it will instantiate ?v to "(BitOps.sextend ?w0 ?v0)" and replace
   "(word.of_Z ?v)" by the RHS of the lemma, i.e. again "(word.of_Z ?Goal11)", so
   no useful progress is made. This tactic prevents this from happending. *)
Ltac rewrite_sextend_width_nop OK :=
  so fun hyporgoal => match hyporgoal with
  | context[word.of_Z (BitOps.sextend ?w ?v)] =>
    rewrite (@sextend_width_nop _ _ OK w v) in * by (reflexivity || congruence)
  end.

Ltac simpl_word_exprs_step OK :=
  let t := (assumption || symmetry; assumption || reflexivity) in
  first [ rewrite (add_0_l (word_ok := OK)) in * by t
        | rewrite (add_0_r (word_ok := OK)) in * by t
        | rewrite (mul_0_l (word_ok := OK)) in * by t
        | rewrite (mul_0_r (word_ok := OK)) in * by t
        | rewrite (mul_1_l (word_ok := OK)) in * by t
        | rewrite (mul_1_r (word_ok := OK)) in * by t
        | rewrite_sextend_width_nop OK ].

Ltac simpl_word_exprs OK :=
  lazymatch type of OK with
  | @word.ok ?width ?Inst => repeat simpl_word_exprs_step OK
  | _ => fail 10000 "wordok is not of type word.ok"
  end.

Ltac solve_word_eq OK :=
  match goal with
  | |- @eq (@word.rep _ _) _ _ => idtac
  | _ => fail 1 "wrong shape of goal"
  end;
  subst;
  try reflexivity;
  clear;
  simpl;
  repeat (autorewrite with rew_Zlength; simpl);
  (ring || (simpl_word_exprs OK; try reflexivity)).
