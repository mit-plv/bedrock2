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
  
  Record HarvardMachine := mkHarvardMachine {
    machine: @RiscvMachine _ (mem wXLEN);
    instructionMem: InstructionMem;
  }.

  Definition with_machine m ml := mkHarvardMachine m ml.(instructionMem).
  Definition with_instructionMem l ml := mkHarvardMachine ml.(machine) l.  

  Definition liftL0{B: Type}(f: OState RiscvMachine B):  OState HarvardMachine B :=
    fun s => let (ob, ma) := f s.(machine) in (ob, with_machine ma s).

  Definition liftL1{A B: Type}(f: A -> OState RiscvMachine B): A -> OState HarvardMachine B :=
    fun a s => let (ob, ma) := f a s.(machine) in (ob, with_machine ma s).

  Definition liftL2{A1 A2 B: Type}(f: A1 -> A2 -> OState RiscvMachine B):
    A1 -> A2 -> OState HarvardMachine B :=
    fun a1 a2 s => let (ob, ma) := f a1 a2 s.(machine) in (ob, with_machine ma s).
                                           
  Instance IsHarvardMachine: RiscvProgram (OState HarvardMachine) (word wXLEN) :=  {|
      getRegister := liftL1 getRegister;
      setRegister := liftL2 setRegister;
      getPC := liftL0 getPC;
      setPC := liftL1 setPC;
      loadByte   := liftL1 loadByte;
      loadHalf   := liftL1 loadHalf;
      loadWord   := liftL1 loadWord;
      loadDouble := liftL1 loadDouble;
      storeByte   := liftL2 storeByte;
      storeHalf   := liftL2 storeHalf;
      storeWord   := liftL2 storeWord;
      storeDouble := liftL2 storeDouble;
      step := liftL0 step;
      getCSRField_MTVecBase := liftL0 getCSRField_MTVecBase;
      endCycle A := Return None;
  |}.

  Definition putProgram(prog: list (word 32))(ma: HarvardMachine): HarvardMachine :=
    with_machine (putProgram prog ma.(machine)) ma.

  Definition loadInst(addr: word wXLEN): OState HarvardMachine Instruction :=
    im <- gets instructionMem;
    Return (im addr).

  (* assumes generic translate and raiseException functions *)
  Context {RVS: RiscvState (OState HarvardMachine) (word wXLEN)}.
  
  Definition run1: OState HarvardMachine unit :=
    pc <- getPC;
    inst <- loadInst pc;
    execute inst;;
    step.

  Definition run: nat -> OState HarvardMachine unit :=
    fun n => power_func (fun m => run1 ;; m) n (Return tt).
  
End Riscv.

Existing Instance IsHarvardMachine. (* needed because it was defined inside a Section *)
