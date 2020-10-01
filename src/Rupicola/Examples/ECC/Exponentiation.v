Require Import Rupicola.Lib.Api.
Require Import Rupicola.Examples.ECC.Field.
Local Open Scope Z_scope.

Require Import bedrock2.NotationsCustomEntry.
Require Import bedrock2.NotationsInConstr.

Section S.
  Context {semantics : Semantics.parameters}
          {semantics_ok : Semantics.parameters_ok semantics}.
  Context {field_parameters : FieldParameters}.
  Context {bignum_representaton : BignumRepresentation}.
  Existing Instances spec_of_mul spec_of_square spec_of_add
           spec_of_sub spec_of_scmula24 spec_of_inv spec_of_bignum_copy
           spec_of_bignum_literal.

  Context {relax_bounds :
             forall X : bignum,
               bounded_by tight_bounds X ->
               bounded_by loose_bounds X}.
  Hint Resolve relax_bounds : compiler.

  Section Gallina.
    Local Notation "0" := (0 mod M).
    Local Notation "1" := (1 mod M).
    Local Infix "+" := (fun x y => (x + y) mod M).
    Local Infix "-" := (fun x y => (x - y) mod M).
    Local Infix "*" := (fun x y => (x * y) mod M).
    Local Infix "^" := (fun x y => (x ^ y) mod M).

    Definition exp_by_squaring_6 (x : Z) : Z :=
      let/d x2 := x ^ 2 in
      let/d x3 := x2 * x in
      let/d x6 := x3 ^ 2 in
      x6.

    Lemma mod_equal :
      forall a b m, a = b -> a mod m = b mod m.
    Proof.
      intros. rewrite H. lia.
    Qed.

    Lemma mod_exp :
      forall m, m <> 0 -> forall b a, ((a mod m) ^ Zpos b) mod m = (a ^ Zpos b) mod m.
    Proof.
    induction b; intros.
    - rewrite Pos2Z.pos_xI.
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_1_r.
      rewrite Z.pow_twice_r.
      rewrite <- Z.mul_mod_idemp_l by assumption.
      remember (((a mod m) ^ Z.pos b * (a mod m) ^ Z.pos b) mod m) as A.
      rewrite Z.mul_mod_idemp_r by assumption.
      rewrite Z.mul_mod in HeqA by assumption.
      rewrite IHb in HeqA.
      rewrite <- Z.mul_mod in HeqA by assumption.
      rewrite HeqA.
      rewrite Z.mul_mod_idemp_l by assumption.
      apply mod_equal.
      rewrite Z.pow_add_r by lia.
      rewrite Z.pow_twice_r.
      lia.
    - rewrite Pos2Z.pos_xO.
      rewrite Z.pow_twice_r.
      rewrite Z.mul_mod by assumption.
      rewrite IHb.
      rewrite <- Z.mul_mod by assumption.
      apply mod_equal.
      rewrite Z.pow_twice_r.
      reflexivity.
    - repeat rewrite Z.pow_1_r.
      rewrite Z.mod_mod by assumption.
      reflexivity.
    Qed.

    Fixpoint exp_by_squaring (x : Z) (n : positive) : Z :=
      match n with
      | xH => x mod M
      | xO n' => let/d res := exp_by_squaring x n' in res^2
      | xI n' => let/d res := exp_by_squaring x n' in
                 let/d res := res^2 in
                 x * res
      end.

    Lemma let_equal :
      forall A B (val : A) (body_l body_r : A -> B),
        (let x := val in body_l x = body_r x)
        -> (let/d x := val in body_l x) = (let/d y := val in body_r y).
    Proof.
      intros. unfold dlet. assumption.
    Qed.

    Lemma let_nested :
      forall A (a : A) (val1 : A) (body1 body2 : A -> A),
        a = (let/d x := val1 in let/d y := body1 x in body2 y)
        -> a = (let/d y := let/d x := val1 in body1 x in body2 y).
    Proof.
      intros. assumption.
    Qed.

    Ltac tac :=
      intros;
      match goal with
      | [ |- _ = let/d _ := let/d _ := _ in _ in _] =>
        eapply let_nested
      | [ |- _ = let/d x := _ in _] =>
        eapply let_equal with (body_l := fun _ => _)
      end.

    Lemma rewrite :
      {rewritten : Z -> Z & forall x, rewritten x = exp_by_squaring x 11}.
    Proof.
      cbv beta delta [exp_by_squaring].
      eexists.
      repeat tac.
      reflexivity.
    Defined.

    Definition rewritten :=
      Eval simpl in projT1 (rewrite).

    Print rewritten.

    Lemma exp_by_squaring_correct :
      M <> 0 -> forall n x, exp_by_squaring x n = x ^ (Zpos n).
    Proof.
      induction n; intros; cbn [exp_by_squaring]; unfold dlet.
      - rewrite IHn.
        rewrite mod_exp by assumption.
        rewrite Z.mul_mod_idemp_r by assumption.
        apply mod_equal.
        rewrite Pos2Z.pos_xI.
        rewrite Z.pow_add_r by lia.
        rewrite <- Z.pow_mul_r by lia.
        rewrite Z.mul_comm with (n := 2).
        lia.
      - rewrite IHn.
        rewrite mod_exp by assumption.
        apply mod_equal.
        symmetry. rewrite Pos2Z.pos_xO.
        rewrite <- Z.pow_mul_r by lia.
        rewrite Z.mul_comm with (n := 2).
        lia.
      - rewrite Z.pow_1_r.
        reflexivity.
    Qed.

  End Gallina.

  Section Bedrock.
    Definition exp_6 : bedrock_func :=
      ("exp_by_squaring_6",
       (["x"; "sq"], [],
        bedrock_func_body:
          (
            cmd.call [] bignum_copy [expr.var "sq"; expr.var "x"];;
            cmd.call [] square [expr.var "sq"; expr.var "sq"];;
            cmd.call [] mul [expr.var "x"; expr.var "sq"; expr.var "sq"];;
            cmd.call [] square [expr.var "sq"; expr.var "sq"]
          )
       )
      ).



  End Bedrock.

End S.
