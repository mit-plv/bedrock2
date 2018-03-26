Require Import Coq.ZArith.BinInt.
Require Import bbv.WordScope.
Require Import bbv.DepEqNat.
Require Import riscv.util.NameWithEq.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.Monads.
Require Import riscv.Decode.
Require Import riscv.Memory. (* should go before Program because both define loadByte etc *)
Require Import riscv.Program.
Require Import riscv.Execute.
Require Import riscv.util.PowerFunc.
Require Import riscv.Utility.
Require Import Coq.Lists.List. Import ListNotations.
Require Import riscv.Minimal.
Require Import riscv.PseudoInstructions.
Require Import riscv.InstructionCoercions.
Require Import riscv.FunctionMemory.

Section Riscv.

  Context {B: RiscvBitWidths}.

  Context {MW: MachineWidth (word wXLEN)}.

  Definition InstructionMem := word wXLEN -> Instruction.
  
  (* assumes generic translate and raiseException functions *)
  Context {RVS: RiscvState (OState RiscvMachine) (word wXLEN)}.
  
  Definition run1(imem: InstructionMem): OState RiscvMachine unit :=
    pc <- getPC;
    execute (imem pc);;
    step.

  Definition run(imem: InstructionMem): nat -> OState RiscvMachine unit :=
    fun n => power_func (fun m => run1 imem ;; m) n (Return tt).
  
End Riscv.
