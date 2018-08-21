Require Import lib.LibTacticsMin.
Require Import riscv.util.Word.
Require Import riscv.util.BitWidths.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import compiler.Op.
Require Import compiler.StateCalculus.
Require Import compiler.NameWithEq.
Require Import Coq.Program.Tactics.
Require Import riscv.MachineWidth32.
Require Import compiler.util.List_Map.
Require Import compiler.Memory.
Require Import compiler.ExprImp.
Require Import compiler.ZName.


Definition var: Set := (@name ZName). (* only inside this test module *)

(*
given x, y, z

if y < x and z < x then
  c = x
  a = y
  b = z
else if x < y and z < y then
  c = y
  a = x
  b = z
else
  c = z
  a = x
  b = y
isRight = a*a + b*b == c*c
*)
Definition _a := 0%Z.
Definition _b := 1%Z.
Definition _c := 2%Z.
Definition _isRight := 3%Z.

Definition isRight(x y z: Z) :=
  SSeq (SIf (EOp OAnd (EOp OLt (ELit y) (ELit x)) (EOp OLt (ELit z) (ELit x)))
            (SSeq (SSet _c (ELit x)) (SSeq (SSet _a (ELit y)) (SSet _b (ELit z))))
            ((SIf (EOp OAnd (EOp OLt (ELit x) (ELit y)) (EOp OLt (ELit z) (ELit y)))
                  (SSeq (SSet _c (ELit y)) (SSeq (SSet _a (ELit x)) (SSet _b (ELit z))))
                  (SSeq (SSet _c (ELit z)) (SSeq (SSet _a (ELit x)) (SSet _b (ELit y)))))))
       (SSet _isRight (EOp OEq (EOp OPlus (EOp OTimes (EVar _a) (EVar _a))
                                          (EOp OTimes (EVar _b) (EVar _b)))
                               (EOp OTimes (EVar _c) (EVar _c)))).

Definition annoying_eq: DecidableEq
  (list (@name ZName) * list (@name ZName) * @stmt ZName ZName). Admitted.
Existing Instance annoying_eq.

Definition run_isRight(x y z: Z): option (word 32) :=
  final <- (eval_stmt empty_map 10 empty_map no_mem (isRight x y z));
  let '(finalSt, finalM) := final in
  get finalSt _isRight.

Goal run_isRight  3  4  5 = Some (ZToWord 32 1). reflexivity. Qed.
Goal run_isRight  3  7  5 = Some (ZToWord 32 0). reflexivity. Qed.
Goal run_isRight  4  3  5 = Some (ZToWord 32 1). reflexivity. Qed.
Goal run_isRight  5  3  5 = Some (ZToWord 32 0). reflexivity. Qed.
Goal run_isRight  5  3  4 = Some (ZToWord 32 1). reflexivity. Qed.
Goal run_isRight 12 13  5 = Some (ZToWord 32 1). reflexivity. Qed.
