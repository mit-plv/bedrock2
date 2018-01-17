Require Import Coq.Lists.List.
Import ListNotations.
Require Import lib.LibTacticsMin.
Require Import bbv.Word.
Require Import compiler.Decidable.
Require Import compiler.Op.
Require Import compiler.ExprImp.
Require Import compiler.NameGen.
Require Import compiler.Common.
Require Import compiler.Pipeline.
Require Import compiler.Riscv.
Require Import compiler.MyOmega.
Require Import compiler.StateMonad.

Definition wlit: nat := 12. (* max bit width of literals *)
Definition wdiff: nat := 20. (* difference between literal width and word width *)
Definition wjimm: nat := 20.
Definition w := wlit + wdiff.

(* smaller sizes for debugging:
Definition wlit: nat := 12. (* max bit width of literals *)
Definition wdiff: nat := 4. (* difference between literal width and word width *)
Definition wjimm: nat := 12.
Definition w := wlit + wdiff.
*)

Lemma w_lbound: w >= wjimm. Omega. Qed.

Definition var := nat.

Instance dec_eq_var : DecidableEq var := Nat.eq_dec.

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

Definition fib_ExprImp(n: word wlit): @stmt wlit var :=
  SSeq (SSet var_a (ELit $0)) (
  SSeq (SSet var_b (ELit $1)) (
  SSeq (SSet var_i (ELit $0)) (
  SWhile (EOp OLt (EVar var_i) (ELit n)) (
    SSeq (SSet var_c (EOp OPlus (EVar var_a) (EVar var_b))) (
    SSeq (SSet var_a (EVar var_b)) (
    SSeq (SSet var_b (EVar var_c)) (
    SSeq (SSet var_i (EOp OPlus (EVar var_i) (ELit $1)))
    SSkip))))))).

Definition state := (var -> option (word w)).

Definition evalH(fuel: nat)(s: @stmt wlit var): option state := 
  @eval_stmt w wlit wdiff eq_refl var state _ fuel empty s.

Definition fib_H_res(fuel: nat)(n: word wlit): option (word w) :=
  match (evalH fuel (fib_ExprImp n)) with
  | Some st => st var_b
  | None => None
  end.

(* Eval vm_compute in (fib_H_res 100 $5). *)

Goal fib_H_res 20 $0 = Some $1. reflexivity. Qed.
Goal fib_H_res 20 $1 = Some $1. reflexivity. Qed.
Goal fib_H_res 20 $2 = Some $2. reflexivity. Qed.
Goal fib_H_res 20 $3 = Some $3. reflexivity. Qed.
Goal fib_H_res 20 $4 = Some $5. reflexivity. Qed.
Goal fib_H_res 20 $5 = Some $8. reflexivity. Qed.
Goal fib_H_res 20 $6 = Some $13. reflexivity. Qed.


Definition fib_riscv0(n: word wlit): list Instruction :=
  exprImp2Riscv (wjimm := wjimm) (fib_ExprImp n).

Definition fib_riscv(n: word wlit): list (@Instruction wlit wjimm var) :=
  ltac:(
    let t := constr:(fib_riscv0 n) in
    let t := eval unfold fib_riscv0, exprImp2Riscv in t in
    let t := eval simpl in t in
    let t := eval unfold FlatToRiscv.var2Register in t in
    exact t
  ).

Notation "'RISCV' {{ x ; y ; .. ; z }}" := (@cons (@Instruction _ _ _) x
  (@cons (@Instruction _ _ _) y .. (@cons (@Instruction _ _ _) z nil) ..))
  (format "'RISCV' {{ '[v' '//' x ; '//' y ; '//' .. ; '//' z ']' '//' }}").

Print fib_riscv.

Definition fib_L_final(fuel: nat)(n: word wlit): RiscvMachine :=
  execState (run (w_lbound := w_lbound) fuel) (initialRiscvMachine (fib_riscv n)).

Definition fib_L_res(fuel: nat)(n: word wlit): word w :=
  (fib_L_final fuel n).(registers) var_b.

Transparent wlt_dec.

(* 1st method: Run it *)
Goal exists fuel, fib_L_res fuel $6 = $13.
  exists 200. reflexivity.
Qed.

(* 2nd method: Prove it *)
Goal exists fuel, fib_L_res fuel $6 = $13.
  unfold fib_L_res. unfold fib_L_final.
  pose proof @exprImp2Riscv_correct as P.
  assert (exists finalH, @FlattenExpr.eval_stmt_H wlit wdiff var state _
     20 empty (fib_ExprImp $ (6)) = Some finalH) as F. {
    eexists. reflexivity.
  }
  destruct F as [finalH F].
  specialize P with (5 := F) (wjimm := wjimm) (w_lbound := w_lbound).
  specialize P with (eq_var_dec := dec_eq_var).
  specialize P with (varset := Function_Set var) (NG := NatNameGen).
  edestruct P as [fuelL G].
  - Omega.
  - Omega.
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
