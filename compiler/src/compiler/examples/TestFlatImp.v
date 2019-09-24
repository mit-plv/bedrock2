Require Import coqutil.Z.Lia.
Require Import compiler.util.Common.
Require Import coqutil.Decidable.
Require Import coqutil.Map.SortedList.
Require Import compiler.FlatImp.
Require Import coqutil.Word.Naive riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Empty_set_keyed_map.
Require Import coqutil.Map.Z_keyed_SortedListMap.


Definition var: Set := Z. (* only inside this test module *)
Definition func: Set := string.
Instance myparams: Syntax.parameters := {|
  Syntax.varname := var;
  Syntax.funname := func;
  Syntax.actname := string;
|}.

Notation stmt := (@stmt myparams).

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


Example fib(n: Z): stmt  :=
  SSeq (SLit _one 1) (
  SSeq (SLit _n n) (
  SSeq (SLit _a 0) (
  SSeq (SLit _b 1) (
  SLoop SSkip
        (CondNez _n)
        (SSeq (SOp _s Syntax.bopname.add _a _b) (
         SSeq (SSet _a _b) (
         SSeq (SSet _b _s) (
              (SOp _n Syntax.bopname.sub _n _one)))))
  )))).

Require Import compiler.Basic32Semantics.

Definition eval_stmt_test fuel initialSt := eval_stmt map.empty fuel initialSt map.empty.

Example finalFibState(n: Z) := (eval_stmt_test 100 map.empty (fib n)).
Example finalFibVal(n: Z): option word32 := match finalFibState n with
| Some (s, _) => map.get s _b
| _ => None
end.

Goal finalFibVal 0 = Some (word.of_Z 1). reflexivity. Qed.
Goal finalFibVal 1 = Some (word.of_Z  1). reflexivity. Qed.
Goal finalFibVal 2 = Some (word.of_Z  2). reflexivity. Qed.
Goal finalFibVal 3 = Some (word.of_Z  3). reflexivity. Qed.
Goal finalFibVal 4 = Some (word.of_Z  5). reflexivity. Qed.
Goal finalFibVal 5 = Some (word.of_Z  8). reflexivity. Qed.
Goal finalFibVal 6 = Some (word.of_Z 13). reflexivity. Qed.
