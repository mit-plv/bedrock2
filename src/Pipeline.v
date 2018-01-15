Require Import Coq.Lists.List.
Import ListNotations.
Require Import lib.LibTacticsMin.
Require Import bbv.Word.
Require Import compiler.Decidable.
Require Import compiler.Op.
Require Import compiler.ResMonad.
Require        compiler.ExprImp.
Require Import compiler.FlattenExpr.
Require        compiler.FlatImp.
Require        compiler.FlatToRiscv.
Require Import compiler.Riscv.
Require Import compiler.Machine.
Require Import compiler.StateMonad.
Require Import compiler.runsToSatisfying.
Require Import compiler.MyOmega.
Require Import compiler.zcast.
Require Import compiler.NameGen.
Require Import compiler.Common.

Section Pipeline.

  Context {wlit: nat}. (* max bit width of literals *)
  Context {wdiff: nat}. (* difference between literal width and word width *)
  Context {wjimm: nat}.
  Notation w := (wlit + wdiff).
  Variable w_lbound: w >= wjimm.
  Variable wlit_bound: 2 <= wlit <= wjimm.
  Variable wjimm_bound: 2 <= wjimm <= w.
  Context {var: Set}.
  Context {eq_var_dec: DecidableEq var}.
  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.
  Context {vars: Type}.
  Context {varset: set vars var}.
  Context {NGstate: Type}.
  Context {NG: NameGen var vars NGstate}.

  Definition exprImp2Riscv(s: @ExprImp.stmt wlit var): list (@Instruction wlit wjimm var) :=
    let ngs := freshNameGenState (ExprImp.allVars_stmt s) in
    let (sFlat, ngs') := flattenStmt ngs s in
    FlatToRiscv.compile_stmt sFlat.

  Definition evalH := @ExprImp.eval_stmt w wlit wdiff eq_refl var state stateMap.

  Definition evalL(fuel: nat)(insts: list Instruction): RiscvMachine :=
    execState (run (w_lbound := w_lbound) fuel) (initialRiscvMachine insts).

  Lemma exprImp2Riscv_correct: forall sH instsL fuelH finalH,
    ExprImp.stmt_size sH * 64 < pow2 wlit ->
    exprImp2Riscv sH = instsL ->
    eval_stmt_H fuelH empty sH = Some finalH ->
    exists fuelL,
      forall resVar res,
      get finalH resVar = Some res ->
      (evalL fuelL instsL).(registers) resVar = res.
  Proof.
    introv B C EvH.
    unfold exprImp2Riscv in C.
    destruct_one_match_hyp.
    unfold eval_stmt_H in EvH.
    pose proof flattenStmt_correct as P.
    specialize (P fuelH sH s finalH).
    destruct P as [fuelM [finalM [EvM GM]]].
    - unfold ExprImp2FlatImp. rewrite E. reflexivity.
    - unfold eval_stmt_H. apply EvH.
    - pose proof  (@FlatToRiscv.compile_stmt_correct
        wlit wdiff wjimm w_lbound wlit_bound wjimm_bound var eq_var_dec) as P.
      specialize P with (2 := C).
      specialize P with (2 := EvM).
      destruct P as [fuelL P].
      + pose proof @flattenStmt_size as D1.
        specialize D1 with (1 := E).
        clear -B D1.
        omega.
      + exists fuelL.
        introv G.
        apply P.
        apply GM.
        apply G.
  Qed.

End Pipeline.
