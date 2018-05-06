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
Require Import riscv.Riscv.
Require Import riscv.util.Monads.
Require Import compiler.runsToSatisfying.
Require Import compiler.MyOmega.
Require Import bbv.DepEqNat.
Require Import compiler.NameGen.
Require Import compiler.Common.
Require Import riscv.RiscvBitWidths.
Require Import compiler.NameWithEq.
Require Import riscv.encode.Encode.
Require Import riscv.AxiomaticRiscv.


Section Pipeline.

  Context {Bw: RiscvBitWidths}.

  Context {state: Type}.
  Context {stateMap: Map state Register (word wXLEN)}.

  Context {mem: nat -> Set}.
  Context {IsMem: Memory.Memory (mem wXLEN) wXLEN}.
  
  Local Notation RiscvMachine := (@RiscvMachine Bw (mem wXLEN) state).
  Context {RVM: RiscvProgram (OState RiscvMachine) (word wXLEN)}.

  (* assumes generic translate and raiseException functions *)
  Context {RVS: @RiscvState (OState RiscvMachine) (word wXLEN) _ _ RVM}.  

  Context {RVAX: @AxiomaticRiscv Bw state FlatToRiscv.State_is_RegisterFile (mem wXLEN) _ RVM}.

  Definition var := Register.

  Context {vars: Type}.
  Context {varset: set vars var}.
  Context {NGstate: Type}.
  Context {NG: NameGen var vars NGstate}.

  
  Definition exprImp2Riscv(s: ExprImp.stmt): list Instruction :=
    let ngs := freshNameGenState (ExprImp.allVars_stmt s) in
    let (sFlat, ngs') := flattenStmt ngs s in
    FlatToRiscv.compile_stmt sFlat.

  Definition evalH := ExprImp.eval_stmt.

  Definition evalL(fuel: nat)(insts: list Instruction)(initial: RiscvMachine): RiscvMachine :=
    execState (run fuel) (putProgram (map (fun i => ZToWord 32 (encode i)) insts) initial).

  Lemma exprImp2Riscv_correct: forall sH initialL instsL fuelH finalH initialMemH finalMemH,
    ExprImp.stmt_size sH * 64 < pow2 wXLEN ->
    exprImp2Riscv sH = instsL ->
    evalH fuelH empty initialMemH sH = Some (finalH, finalMemH) ->
    exists fuelL,
      forall resVar res,
      get finalH resVar = Some res ->
      getReg (evalL fuelL instsL initialL).(core).(registers) resVar = res.
  Proof.
    introv B C EvH.
    unfold exprImp2Riscv in C.
    destruct_one_match_hyp.
    unfold evalH in EvH.
  Admitted.
  (* TODO first finish FlatToRiscv.compile_stmt_correct
    pose proof flattenStmt_correct as P.
    specialize (P fuelH sH s finalH).
    destruct P as [fuelM [finalM [EvM GM]]].
    - unfold ExprImp2FlatImp. rewrite E. reflexivity.
    - unfold evalH. apply EvH.
    - pose proof  FlatToRiscv.compile_stmt_correct as P.
      specialize P with (2 := C).
      specialize P with (2 := EvM).
      specialize (P initialL).
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
  *)

End Pipeline.
