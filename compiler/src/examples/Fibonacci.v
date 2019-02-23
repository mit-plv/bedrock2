Require bedrock2.Examples.Demos.
Require Import bedrock2.BasicC32Semantics.
Require Import compiler.ExprImp.
Require Import coqutil.Map.SortedList.
Require compiler.examples.TestFlatImp.
Require Import coqutil.Map.Interface.
Require Import riscv.Utility.
Import String List.ListNotations.

Definition fib_ExprImp(n: Z) := Eval cbv in snd (snd (Demos.fibonacci n)).
(* This is what the bare AST looks like. For a more readable version with notations, see
   bedrock2/Demos.v *)
(* Print fib_ExprImp. *)

Local Existing Instance BasicC32Semantics.parameters.
Definition fib_H_res(fuel: nat)(n: Z): option word :=
  match (eval_cmd map.empty fuel map.empty map.empty (fib_ExprImp n)) with
  | Some (st, m) => map.get st "b"%string
  | None => None
  end.

Goal fib_H_res 20 0 = Some (word.of_Z  1). reflexivity. Qed.
Goal fib_H_res 20 1 = Some (word.of_Z  1). reflexivity. Qed.
Goal fib_H_res 20 2 = Some (word.of_Z  2). reflexivity. Qed.
Goal fib_H_res 20 3 = Some (word.of_Z  3). reflexivity. Qed.
Goal fib_H_res 20 4 = Some (word.of_Z  5). reflexivity. Qed.
Goal fib_H_res 20 5 = Some (word.of_Z  8). reflexivity. Qed.
Goal fib_H_res 20 6 = Some (word.of_Z 13). reflexivity. Qed.