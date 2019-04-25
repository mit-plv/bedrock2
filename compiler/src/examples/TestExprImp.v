Require Import compiler.util.Common.
Require Import coqutil.Decidable.
Require Import Coq.Program.Tactics.
Require Import coqutil.Map.SortedList.
Require Import compiler.ExprImp.
Require Import bedrock2.ZNamesSyntax.
Require Import coqutil.Word.Naive riscv.Utility.Words32Naive.
Require Import riscv.Utility.DefaultMemImpl32.
Require Import coqutil.Map.Empty_set_keyed_map.
Require Import coqutil.Map.Z_keyed_SortedListMap.


Instance myparams: Syntax.parameters := {|
  Syntax.varname := Z;
  Syntax.funname := Z;
  Syntax.actname := Empty_set;
|}.

Axiom TODO: False.

Instance params: Semantics.parameters := {|
    Semantics.syntax := myparams;
    Semantics.word := word32;
    Semantics.locals := _;
    Semantics.funname_env := _;
    Semantics.funname_eqb a b := false;
    Semantics.ext_spec _ _ _ _ _ := False;
|}.

Definition annoying_eq: DecidableEq
  (list varname * list varname * cmd). Admitted.
Existing Instance annoying_eq.

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
  cmd.seq (cmd.cond (expr.op bopname.and (expr.op bopname.ltu (expr.literal y) (expr.literal x)) (expr.op bopname.ltu (expr.literal z) (expr.literal x)))
            (cmd.seq (cmd.set _c (expr.literal x)) (cmd.seq (cmd.set _a (expr.literal y)) (cmd.set _b (expr.literal z))))
            ((cmd.cond (expr.op bopname.and (expr.op bopname.ltu (expr.literal x) (expr.literal y)) (expr.op bopname.ltu (expr.literal z) (expr.literal y)))
                  (cmd.seq (cmd.set _c (expr.literal y)) (cmd.seq (cmd.set _a (expr.literal x)) (cmd.set _b (expr.literal z))))
                  (cmd.seq (cmd.set _c (expr.literal z)) (cmd.seq (cmd.set _a (expr.literal x)) (cmd.set _b (expr.literal y)))))))
       (cmd.set _isRight (expr.op bopname.eq (expr.op bopname.add (expr.op bopname.mul (expr.var _a) (expr.var _a))
                                          (expr.op bopname.mul (expr.var _b) (expr.var _b)))
                               (expr.op bopname.mul (expr.var _c) (expr.var _c)))).

Definition run_isRight(x y z: Z) :=
  let final := eval_cmd (p := params) map.empty 10 map.empty map.empty (isRight x y z) in
  match final with
  | Some (finalSt, finalM) => map.get finalSt _isRight
  | None => None
  end.

Goal run_isRight  3  4  5 = Some (word.of_Z 1). reflexivity. Qed.
Goal run_isRight  3  7  5 = Some (word.of_Z 0). reflexivity. Qed.
Goal run_isRight  4  3  5 = Some (word.of_Z 1). reflexivity. Qed.
Goal run_isRight  5  3  5 = Some (word.of_Z 0). reflexivity. Qed.
Goal run_isRight  5  3  4 = Some (word.of_Z 1). reflexivity. Qed.
Goal run_isRight 12 13  5 = Some (word.of_Z 1). reflexivity. Qed.
