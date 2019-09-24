Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import riscv.Utility.Utility.
Require Import compiler.mod4_0.

Local Open Scope Z_scope.

Definition divisibleBy4{W: Words}(x: word): Prop := (word.unsigned x) mod 4 = 0.

Ltac divisibleBy4_pre :=
  lazymatch goal with
  | |- ?G => assert_fails (has_evar G)
  end;
  unfold divisibleBy4 in *;
  lazymatch goal with
  | |- _ mod 4 = 0 => idtac
  | |- _ => fail "not a divisibleBy4 goal"
  end;
  repeat match goal with
         | H: _ mod 4 = 0 |- _ => revert H
         end;
  clear;
  repeat match goal with
         | |- _ mod 4 = 0 -> _ => intro
         end;
  repeat (rewrite ?word.unsigned_add,
                  ?word.unsigned_sub,
                  ?word.unsigned_mul,
                  ?word.unsigned_of_Z
          || unfold word.wrap).

Ltac solve_divisibleBy4 := divisibleBy4_pre; solve_mod4_0.

(* tests from FlatToRiscv *)
Goal forall {W: Words} (pc: word) (l n m: Z), divisibleBy4 pc -> False.
  intros.
  assert (divisibleBy4 (word.add pc (word.of_Z (l * 4)))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4 (word.add pc (word.of_Z 4))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4
            (word.add
               (word.add (word.add pc (word.of_Z 4))
                         (word.mul (word.of_Z 4) (word.of_Z l)))
               (word.of_Z (n * 4)))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4
            (word.add
               (word.add pc
                         (word.mul (word.of_Z 4) (word.of_Z l)))
               (word.of_Z (n * 4)))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4
            (word.add
               (word.add pc
                         (word.mul (word.of_Z 4)
                                   (word.of_Z l)))
               (word.of_Z 4))) as A by solve_divisibleBy4. clear A.
  assert (divisibleBy4
            (word.add
               (word.add
                  (word.add
                     (word.add pc
                               (word.mul (word.of_Z 4)
                                         (word.of_Z l)))
                     (word.of_Z 4))
                  (word.mul (word.of_Z 4) (word.of_Z n)))
               (word.of_Z
                  (- m * 4)))) as A by solve_divisibleBy4. clear A.
Abort.


Section Modu.
  Context {W: Words}.

  Definition divisibleBy4'(x: word): Prop := word.modu x (word.of_Z 4) = word.of_Z 0.

  Lemma four_fits: 4 < 2 ^ width.
  Proof.
    destruct width_cases as [C | C]; rewrite C; reflexivity.
  Qed.

  Ltac div4_sidecondition :=
    pose proof four_fits;
    rewrite ?word.unsigned_of_Z; unfold word.wrap; rewrite ?Z.mod_small;
    blia.

  Lemma divisibleBy4_alt(x: word): divisibleBy4 x -> divisibleBy4' x.
  Proof.
    intro H. unfold divisibleBy4, divisibleBy4' in *.
    apply word.unsigned_inj.
    rewrite word.unsigned_modu_nowrap by div4_sidecondition.
    replace (word.unsigned (word.of_Z 4)) with 4 by div4_sidecondition.
    rewrite H.
    div4_sidecondition.
  Qed.

End Modu.

Ltac simpl_modu4_0 :=
  simpl;
  match goal with
  | |- context [word.eqb ?a ?b] =>
    rewrite (word.eqb_eq a b) by (apply divisibleBy4_alt; solve_divisibleBy4)
  end;
  simpl.
