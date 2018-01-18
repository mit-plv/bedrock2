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
Require Import compiler.StateMonad.
Require Import compiler.runsToSatisfying.
Require Import compiler.MyOmega.
Require Import compiler.zcast.
Require Import compiler.NameGen.
Require Import compiler.Common.
Require Import compiler.RiscvBitWidths.
Require Import compiler.NameWithEq.

Section Pipeline.

  Context {Bw: RiscvBitWidths}.

  Context {Name: NameWithEq}.
  Notation var := (@name Name).
  Existing Instance eq_name_dec.

  Context {state: Type}.
  Context {stateMap: Map state var (word wXLEN)}.

  Context {vars: Type}.
  Context {varset: set vars var}.
  Context {NGstate: Type}.
  Context {NG: NameGen var vars NGstate}.

  Definition exprImp2Riscv(s: ExprImp.stmt (w := wXLEN)): list Instruction :=
    let ngs := freshNameGenState (ExprImp.allVars_stmt s) in
    let (sFlat, ngs') := flattenStmt ngs s in
    FlatToRiscv.compile_stmt sFlat.

  Definition evalH := ExprImp.eval_stmt (w := wXLEN).

  Definition evalL(fuel: nat)(insts: list Instruction): RiscvMachine :=
    execState (run fuel) (initialRiscvMachine insts).

  Lemma exprImp2Riscv_correct: forall sH instsL fuelH finalH,
    ExprImp.stmt_size sH * 64 < pow2 wimm ->
    exprImp2Riscv sH = instsL ->
    evalH fuelH empty sH = Some finalH ->
    exists fuelL,
      forall resVar res,
      get finalH resVar = Some res ->
      (evalL fuelL instsL).(registers) resVar = res.
  Proof.
    introv B C EvH.
    unfold exprImp2Riscv in C.
    destruct_one_match_hyp.
    unfold evalH in EvH.
    pose proof flattenStmt_correct as P.
    specialize (P fuelH sH s finalH).
    destruct P as [fuelM [finalM [EvM GM]]].
    - unfold ExprImp2FlatImp. rewrite E. reflexivity.
    - unfold evalH. apply EvH.
    - pose proof  FlatToRiscv.compile_stmt_correct as P.
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
