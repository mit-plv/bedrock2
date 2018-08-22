Require Import lib.LibTacticsMin.
Require Import riscv.util.Word.
Require Import riscv.util.BitWidths.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import compiler.Op.
Require Import compiler.StateCalculus.
Require Import compiler.Decidable.
Require Import Coq.Program.Tactics.
Require Import riscv.MachineWidth32.
Require Import compiler.util.List_Map.
Require Import compiler.Memory.
Require Import compiler.ExprImp.
Require Import compiler.NamesInstance.
Require Import compiler.Basic32Semantics.

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
  cmd.seq (cmd.cond (expr.op OAnd (expr.op OLt (expr.literal y) (expr.literal x)) (expr.op OLt (expr.literal z) (expr.literal x)))
            (cmd.seq (cmd.set _c (expr.literal x)) (cmd.seq (cmd.set _a (expr.literal y)) (cmd.set _b (expr.literal z))))
            ((cmd.cond (expr.op OAnd (expr.op OLt (expr.literal x) (expr.literal y)) (expr.op OLt (expr.literal z) (expr.literal y)))
                  (cmd.seq (cmd.set _c (expr.literal y)) (cmd.seq (cmd.set _a (expr.literal x)) (cmd.set _b (expr.literal z))))
                  (cmd.seq (cmd.set _c (expr.literal z)) (cmd.seq (cmd.set _a (expr.literal x)) (cmd.set _b (expr.literal y)))))))
       (cmd.set _isRight (expr.op OEq (expr.op OPlus (expr.op OTimes (expr.var _a) (expr.var _a))
                                          (expr.op OTimes (expr.var _b) (expr.var _b)))
                               (expr.op OTimes (expr.var _c) (expr.var _c)))).

Definition annoying_eq: DecidableEq
  (list varname * list varname * cmd). Admitted.
Existing Instance annoying_eq.

Definition run_isRight(x y z: Z): option (bbv.Word.word 32) :=
  let final := eval_cmd empty_map 10 empty_map no_mem (isRight x y z) in
  match final with
  | Some (finalSt, finalM) => get finalSt _isRight
  | None => None
  end.

Goal run_isRight  3  4  5 = Some (ZToWord 32 1). reflexivity. Qed.
Goal run_isRight  3  7  5 = Some (ZToWord 32 0). reflexivity. Qed.
Goal run_isRight  4  3  5 = Some (ZToWord 32 1). reflexivity. Qed.
Goal run_isRight  5  3  5 = Some (ZToWord 32 0). reflexivity. Qed.
Goal run_isRight  5  3  4 = Some (ZToWord 32 1). reflexivity. Qed.
Goal run_isRight 12 13  5 = Some (ZToWord 32 1). reflexivity. Qed.
