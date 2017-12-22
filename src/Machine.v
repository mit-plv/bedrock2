Require Import Coq.Lists.List.
Require Import bbv.Word.
Require Import compiler.StateMonad.
Require Import compiler.Decidable.
Require Import compiler.Riscv.


Section Machine.

  Context {wlit: nat}.
  Context {wdiff: nat}.
  Notation w := (wlit + wdiff).
  Context {Reg: Set}.
  Context {dec_Register: DecidableEq Reg}.

  Record RiscvMachine := mkRiscvMachine {
    instructionMem: word w -> @Instruction wlit Reg;
    registers: Reg -> word w;
    pc: word w;
  }.

  Instance IsRiscvMachine: @RiscvState wlit wdiff Reg (State RiscvMachine) :=
  {|
      getRegister := fun (reg: (@Register Reg)) =>
        match reg with
        | RegO => Return $0
        | RegS r => machine <- get; Return (machine.(registers) r)
        end;
      setRegister := fun (reg: (@Register Reg)) (v: word w) =>
        match reg with
        | RegO => Return tt
        | RegS r => machine <- get;
                    match machine with
                    | mkRiscvMachine imem regs pc =>
                        put (mkRiscvMachine imem 
                                            (fun reg2 => if dec (r = reg2) then v else regs reg2)
                                            pc)
                    end
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

  Definition initialRiscvMachine(imem: list (@Instruction wlit Reg)): RiscvMachine := {|
    instructionMem := fun (i: word w) => nth (Nat.div (wordToNat i) 4) imem InfiniteJal;
    registers := fun (r: Reg) => $0;
    pc := $0
  |}.

End Machine.

(* needed because it's not exported outside the section by default *)
Existing Instance IsRiscvMachine.


Module MachineTest.

  Definition m1: @RiscvMachine 4 0 nat := {|
    instructionMem := fun (w: word (4+0)) => Nop;
    registers := fun (reg: nat) => $22;
    pc := $33
  |}.

  Definition myInst := (@IsRiscvMachine 4 0 nat _).
  Existing Instance myInst.

  (* TODO (_ 4 0) is cumbersome *)
  Definition prog1: State (@RiscvMachine 4 0 nat) (word (_ 4 0)) :=
    x <- getRegister (RegS 2);
    setRegister (RegS 2) (x ^+ $3);;
    getRegister (RegS 4).

  Goal evalState prog1 m1 = $6. reflexivity. Qed.

End MachineTest.
