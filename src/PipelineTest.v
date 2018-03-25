Require Import Coq.Lists.List.
Import ListNotations.
Require Import lib.LibTacticsMin.
Require Import bbv.Word.
Require Import riscv.util.Decidable.
Require Import compiler.Op.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Common.
Require Import compiler.Pipeline.
Require Import riscv.Riscv.
Require Import compiler.MyOmega.
Require Import riscv.util.Monads.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.

Require Import riscv.RiscvBitWidths32.


Instance NatName: NameWithEq := {| name := nat |}.

Definition var: Set := (@name NatName).
Definition Reg: Set := (@name NatName).

Definition var_a: var := 0.
Definition var_b: var := 1.
Definition var_c: var := 2.
Definition var_i: var := 3.

(*
a = 0
b = 1
i = 0
while i < n:
  c = a + b
  a = b
  b = c
  i = i + 1
*)

Definition fib_ExprImp(n: word wXLEN): stmt :=
  SSeq (SSet var_a (ELit $0)) (
  SSeq (SSet var_b (ELit $1)) (
  SSeq (SSet var_i (ELit $0)) (
  SWhile (EOp OLt (EVar var_i) (ELit n)) (
    SSeq (SSet var_c (EOp OPlus (EVar var_a) (EVar var_b))) (
    SSeq (SSet var_a (EVar var_b)) (
    SSeq (SSet var_b (EVar var_c)) (
    SSeq (SSet var_i (EOp OPlus (EVar var_i) (ELit $1)))
    SSkip))))))).

Definition state := (var -> option (word wXLEN)).

Definition fib_H_res(fuel: nat)(n: word wXLEN): option (word wXLEN) :=
  match (eval_stmt fuel empty (fib_ExprImp n)) with
  | Some st => st var_b
  | None => None
  end.


Goal fib_H_res 20 $0 = Some $1. reflexivity. Qed.
Goal fib_H_res 20 $1 = Some $1. reflexivity. Qed.
Goal fib_H_res 20 $2 = Some $2. reflexivity. Qed.
Goal fib_H_res 20 $3 = Some $3. reflexivity. Qed.
Goal fib_H_res 20 $4 = Some $5. reflexivity. Qed.
Goal fib_H_res 20 $5 = Some $8. reflexivity. Qed.
Goal fib_H_res 20 $6 = Some $13. reflexivity. Qed.


(* exprImp2Riscv is the main compilation function *)
Definition fib_riscv0(n: word wXLEN): list Instruction :=
  exprImp2Riscv (fib_ExprImp n).

Definition fib6_riscv: list Instruction :=
  ltac:(
    let t := constr:(fib_riscv0 $6) in
    let t := eval unfold fib_riscv0, exprImp2Riscv in t in
    let t := eval simpl in t in
    let t := eval unfold FlatToRiscv.var2Register, FlatToRiscv.compile_lit in t in
    let t := eval simpl in t in
    exact t
  ).

Notation "'RISCV' {{ x ; y ; .. ; z }}" := (@cons Instruction x
  (@cons Instruction y .. (@cons Instruction z nil) ..))
  (format "'RISCV' {{ '[v' '//' x ; '//' y ; '//' .. ; '//' z ']' '//' }}").

Print fib6_riscv.


Definition initialRiscvMachine(imem: list Instruction): RiscvMachine := {|
  instructionMem := fun (i: word wXLEN) => nth (Nat.div (wordToNat i) 4) imem InfiniteJal;
  registers := fun (r: Reg) => $0;
  pc := $0;
  exceptionHandlerAddr := wneg $4;
|}.


Definition fib6_L_final(fuel: nat): RiscvMachine :=
  execState (run fuel) (initialRiscvMachine fib6_riscv).

Definition fib6_L_res(fuel: nat): word wXLEN :=
  (fib6_L_final fuel).(registers) var_b.

Transparent wlt_dec.

(* 1st method: Run it *)
Lemma fib6_L_res_is_13_by_running_it: exists fuel, fib6_L_res fuel = $13.
  exists 200. cbv. reflexivity.
Qed.

(* 2nd method: Prove it without running it, but using the compiler correctness theorem *)
Lemma fib6_L_res_is_13_by_proving_it: exists fuel, fib6_L_res fuel = $13.
  unfold fib6_L_res. unfold fib6_L_final.
  pose proof @exprImp2Riscv_correct as P.
  assert (exists finalH, evalH 20 empty (fib_ExprImp $ (6)) = Some finalH) as F. {
    eexists. reflexivity.
  }
  destruct F as [finalH F].
  specialize P with (3 := F).
  specialize P with (varset := Function_Set var) (NG := NatNameGen).
  specialize (P (initialRiscvMachine fib6_riscv)).
  edestruct P as [fuelL G].
  - cbv. omega.
  - reflexivity.
  - exists fuelL. apply G.
    assert (forall T (a b: T), Some a = Some b -> a = b) as E. {
      introv R. inversion R. reflexivity.
    }
    apply E in F.
    rewrite <- F. clear F.
    cbv. reflexivity.
Qed.
