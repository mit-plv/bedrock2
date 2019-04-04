Require Import Coq.ZArith.ZArith.
Require Import coqutil.Z.Lia.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import riscv.Utility.Utility.
Require Import compiler.mod4_0.

Local Open Scope Z_scope.

Definition divisibleBy4{W: Words}(x: word): Prop := (word.unsigned x) mod 4 = 0.

Ltac divisibleBy4_pre :=
  lazymatch goal with
  | |- divisibleBy4 _ => idtac
  | |- _ => fail "not a divisibleBy4 goal"
  end;
  repeat match goal with
         | H: divisibleBy4 _ |- _ => revert H
         end;
  clear;
  repeat match goal with
         | |- divisibleBy4 _ -> _ => intro
         end;
  unfold divisibleBy4 in *;
  repeat rewrite ?word.unsigned_add, ?word.unsigned_mul, ?word.unsigned_of_Z.

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
