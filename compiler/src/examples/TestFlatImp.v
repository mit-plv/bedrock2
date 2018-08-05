Require Import bbv.WordScope.
Require Import riscv.util.BitWidths.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import compiler.Op.
Require Import compiler.Memory.
Require Import compiler.NameWithEq.
Require Import riscv.util.BitWidth32.
Require Import compiler.util.List_Map.
Require Import compiler.util.List_Set.
Require Import compiler.FlatImp.
Require Import compiler.ZName.
Require Import riscv.MachineWidth32.


Definition var: Set := (@name ZName). (* only inside this test module *)

Definition _n := 0%Z.
Definition _a := 1%Z.
Definition _b := 2%Z.
Definition _s := 3%Z.
Definition _one := 4%Z.
(*
one = 1
n = input()
a = 0
b = 1
loop:
  stay in loop only if n nonzero
  s = a+b
  a = b
  b = s
  n = n - one
 *)


Example fib(n: word 32) :=
  SSeq (SLit _one $1) (
  SSeq (SLit _n n) (
  SSeq (SLit _a $0) (
  SSeq (SLit _b $1) (
  SLoop SSkip
        _n
        (SSeq (SOp _s OPlus _a _b) (
         SSeq (SSet _a _b) (
         SSeq (SSet _b _s) (
              (SOp _n OMinus _n _one)))))
  )))).

Definition annoying_eq: DecidableEq
  (list (@name ZName) * list (@name ZName) * @stmt (word 32) ZName ZName). Admitted.
Existing Instance annoying_eq.

Definition eval_stmt_test fuel initialSt := @eval_stmt (word 32) _ ZName ZName _ (List_Map _ _) empty_map fuel initialSt no_mem.

Example finalFibState(n: nat) := (eval_stmt_test 100 empty_map (fib $n)).
Example finalFibVal(n: nat): option (word 32) := match finalFibState n with
| Some (s, _) => get s _b
| _ => None
end.

Goal finalFibVal 0 = Some $1. reflexivity. Qed.
Goal finalFibVal 1 = Some $1. reflexivity. Qed.
Goal finalFibVal 2 = Some $2. reflexivity. Qed.
Goal finalFibVal 3 = Some $3. reflexivity. Qed.
Goal finalFibVal 4 = Some $5. reflexivity. Qed.
Goal finalFibVal 5 = Some $8. reflexivity. Qed.
Goal finalFibVal 6 = Some $13. reflexivity. Qed.
