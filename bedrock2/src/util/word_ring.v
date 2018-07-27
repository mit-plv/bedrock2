Require Import Coq.ZArith.BinInt.
Require Import Coq.ZArith.Znat.
Require Import bbv.WordScope.
Require Import Coq.Lists.List.

Lemma Z4four: forall sz, ZToWord sz 4 = $4.
Proof.
  intros. change 4%Z with (Z.of_nat 4).
  apply ZToWord_Z_of_nat.
Qed.

Ltac ringify wXLEN :=
  repeat match goal with
         | |- context [natToWord ?sz (S ?x)] =>
           tryif (unify x O)
           then fail
           else (progress rewrite (natToWord_S sz x))
         | |- _ => change (natToWord wXLEN 1) with (wone wXLEN)
                 || change (natToWord wXLEN 0) with (wzero wXLEN)
                 || rewrite! natToWord_plus
                 || rewrite! natToWord_mult
                 || rewrite! Nat2Z.inj_add
                 || rewrite <-! Z.sub_0_l
                 || rewrite! Z.mul_sub_distr_r
                 || rewrite! Z.mul_add_distr_r
                 || rewrite! ZToWord_minus
                 || rewrite! ZToWord_plus
                 || rewrite! ZToWord_mult
                 || rewrite! ZToWord_Z_of_nat
                 || rewrite! Z4four
                 || rewrite! ZToWord_0
                 || rewrite! wzero'_def
         end.

Ltac solve_word_eq_old wXLEN :=
  match goal with
  | |- @eq (word _) _ _ => idtac
  | _ => fail 1 "wrong shape of goal"
  end;
  subst;
  clear;
  simpl;
  repeat (rewrite app_length; simpl);
  ringify wXLEN;
  try ring.    

Section Test.
  Variable (sz: nat).

  Add Ring word_sz_ring : (wring sz).

  Goal forall (a b c: word sz), ((a ^+ b) ^- b) ^* c ^* $1 = a ^* c ^* $1.
  Proof.
    intros. ring.
  Qed.

  (* Note: does not test ringity and solve_word_eq yet *)
End Test.
