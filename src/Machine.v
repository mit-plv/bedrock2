Require Import Coq.Lists.List.
Require Import bbv.Word.
Require Import compiler.StateMonad.
Require Import compiler.Decidable.
Require Import compiler.Riscv.


Section Machine.

  Context {w: nat}.
  Context {Register: Set}.
  Context {Reg0: Register}.
  Context {dec_Register: DecidableEq Register}.

  Record RiscvMachine := mkRiscvMachine {
    instructionMem: word w -> @Instruction Register;
    registers: Register -> word w;
    pc: word w;
  }.

  Instance IsRiscvMachine: @RiscvState w Register (State RiscvMachine) :=
  {|
      R0 := Reg0;
      getRegister := fun (reg: Register) =>
        machine <- get;
        Return (machine.(registers) reg);
      setRegister := fun (reg: Register) (v: word w) =>
        machine <- get;
        match machine with
        | mkRiscvMachine imem regs pc =>
            put (mkRiscvMachine imem (fun reg2 => if dec (reg = reg2) then v else regs reg2) pc)
        end;
      loadInst := fun (addr: word w) =>
        im <- gets instructionMem;
        Return (im addr);
      getPC := gets pc;
      setPC := fun (newPC: word w) =>
        machine <- get;
        match machine with
        | mkRiscvMachine imem regs pc =>
            put (mkRiscvMachine imem regs newPC)
        end;
  |}.

End Machine.

(* needed because it's not exported outside the section by default *)
Existing Instance IsRiscvMachine.


Module MachineTest.

  Definition m1: @RiscvMachine 4 nat := {|
    instructionMem := fun (w: word 4) => Add 3 3 3;
    registers := fun (reg: nat) => $22;
    pc := $33
  |}.

  Definition myInst := (@IsRiscvMachine 4 nat 0 _).
  Existing Instance myInst.

  Definition prog1: State (@RiscvMachine 4 nat) (word 4) :=
    x <- getRegister 2;
    setRegister 2 (x ^+ $3);;
    getRegister 4.

  Goal evalState prog1 m1 = $6. reflexivity. Qed.

End MachineTest.
