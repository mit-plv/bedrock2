Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Z.BitOps.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Z.Lia.


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
         | context [?op ?a ?b] =>
           match isZcst a with true => idtac end;
           match isZcst b with true => idtac end;
           match op with
           | Z.add => idtac
           | Z.sub => idtac
           | Z.mul => idtac
           end;
           let r := eval cbv in (op a b) in change (op a b) with r in *
         | context [Z.of_nat ?x] =>
           match isnatcst x with true => idtac end;
           let r := eval cbv in (Z.of_nat x) in change (Z.of_nat x) with r in *
         end.

Ltac simpl_word_exprs_step OK :=
  so fun hyporgoal => match hyporgoal with
  (* If "rewrite (add_0_l (word_ok := OK))" encounters a term of the form
     "(word.add ?v otherstuff)", it will instantiate ?v to "word.of_Z 0" and replace
     "(word.add ?v otherstuff)" by "otherstuff". Explicit matching prevents this from happening. *)
  | context[ @word.add ?wi ?wo (word.of_Z 0) ?x ] => rewrite (@add_0_l wi wo OK x) in *

  (* similar problems for the other lemmas: *)
  | context[ @word.add ?wi ?wo ?x (word.of_Z 0) ] => rewrite (@add_0_r wi wo OK x) in *
  | context[ @word.mul ?wi ?wo (word.of_Z 0) ?x ] => rewrite (@mul_0_l wi wo OK x) in *
  | context[ @word.mul ?wi ?wo ?x (word.of_Z 0) ] => rewrite (@mul_0_r wi wo OK x) in *
  | context[ @word.mul ?wi ?wo (word.of_Z 1) ?x ] => rewrite (@mul_1_l wi wo OK x) in *
  | context[ @word.mul ?wi ?wo ?x (word.of_Z 1) ] => rewrite (@mul_1_r wi wo OK x) in *

   (* If "rewrite (sextend_width_nop (word_ok := OK))" encounters a term of the form
      "(word.of_Z ?v)", it will instantiate ?v to "(BitOps.sextend ?w0 ?v0)" and replace
      "(word.of_Z ?v)" by the RHS of the lemma, i.e. again "(word.of_Z ?Goal11)", so
      no useful progress is made. This explicit matching prevents this from happening. *)
  | context[word.of_Z (BitOps.signExtend ?w ?v)] =>
    rewrite (@sextend_width_nop _ _ OK w v) in * by (reflexivity || congruence)
  end.

Require Import riscv.Utility.ListLib.
Hint Rewrite @Zlength_nil @Zlength_cons @Zlength_app: rew_Zlength.

Ltac simpl_word_exprs OK :=
  autorewrite with rew_Zlength in *;
  simpl_Zcsts;
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
