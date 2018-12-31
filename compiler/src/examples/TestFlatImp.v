Require Import Coq.micromega.Lia.
Require Import riscv.util.Word.
Require Import riscv.util.BitWidths.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import compiler.Op.
Require Import coqutil.Decidable.
Require Import riscv.util.BitWidth32.
Require Import coqutil.Map.SortedList.
Require Import compiler.util.List_Set.
Require Import compiler.FlatImp.
Require Import riscv.Words32Naive.
Require Import riscv.DefaultMemImpl32.


Definition var: Set := Z. (* only inside this test module *)
Definition func: Set := Empty_set.
Instance myparams: Basic_bopnames.parameters := {|
  varname := var;
  funcname := func;
  actname := Empty_set;
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
        (SSeq (SOp _s bopname.add _a _b) (
         SSeq (SSet _a _b) (
         SSeq (SSet _b _s) (
              (SOp _n bopname.sub _n _one)))))
  )))).

Instance Zltb_strictorder: SortedList.parameters.strict_order Z.ltb.
Proof.
  constructor; intros; rewrite ?Z.ltb_lt, ?Z.ltb_ge, ?Z.ltb_irrefl in *;
    reflexivity || lia.
Qed.

Instance Zkeyed_map_params(V: Type): SortedList.parameters := {|
  parameters.key := Z;
  parameters.value := V;
  parameters.ltb := Z.ltb;
|}.

Instance Zkeyed_map(V: Type): map.map Z V :=
  SortedList.map (Zkeyed_map_params V) Zltb_strictorder.

Instance Empty_set_strictorder: SortedList.parameters.strict_order
                                  (fun (e1 e2: Empty_set) => false).
Proof.
  constructor; intros; match goal with x: Empty_set |- _ => destruct x end.
Qed.

Instance Empty_set_keyed_map_params(V: Type): SortedList.parameters := {|
  parameters.key := Empty_set;
  parameters.value := V;
  parameters.ltb e1 e2 := false;
|}.
Instance Empty_set_keyed_map(V: Type): map.map Empty_set V :=
  SortedList.map (Empty_set_keyed_map_params V) Empty_set_strictorder.

Instance Registers: map.map varname word32 := Zkeyed_map word32.

Instance myFlatImpParams: FlatImp.parameters := {|
  FlatImp.bopname_params := myparams;
  FlatImp.W := Words32Naive;
  FlatImp.locals := Registers;
  FlatImp.env := Empty_set_keyed_map _;
  FlatImp.mem := Mem;
  FlatImp.locals_ok := @SortedList.map_ok (Zkeyed_map_params _) _;
  FlatImp.env_ok := @SortedList.map_ok (Empty_set_keyed_map_params _) _;
  FlatImp.mem_ok := @SortedList.map_ok DefaultMemImpl32.params _;
  FlatImp.ext_spec t m action args outcome := False;
  FlatImp.max_ext_call_code_size name := 0%Z;
|}.

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
