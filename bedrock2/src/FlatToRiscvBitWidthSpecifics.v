Require Import lib.LibTacticsMin.
Require Import riscv.util.Monads.
Require Import compiler.FlatImp.
Require Import compiler.StateCalculus.
Require Import bbv.DepEqNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import compiler.Op.
Require Import riscv.Program.
Require Import riscv.Decode.
Require Import riscv.PseudoInstructions.
Require Import riscv.RiscvMachine.
Require Import riscv.Execute.
Require Import riscv.Run.
Require Import riscv.Memory.
Require Import riscv.util.PowerFunc.
Require Import riscv.util.BitWidths.
Require Import compiler.NameWithEq.
Require Import Coq.Program.Tactics.
Require Import riscv.InstructionCoercions.
Require Import compiler.StateCalculus.
Require Import riscv.AxiomaticRiscv.
Require Import Coq.micromega.Lia.
Require Import riscv.util.nat_div_mod_to_quot_rem.
Require Import compiler.util.word_ring.
Require Import compiler.util.Misc.
Require Import riscv.Utility.
Require Import riscv.util.ZBitOps.
Require Import compiler.util.Common.
Require Import riscv.Utility.
Require Import compiler.ZName.
Require Import riscv.MachineWidth_wXLEN.
Require Import riscv.MachineWidth32.
Require Import riscv.MachineWidth64.


Class FlatToRiscvBitWidthSpecifics(mword: Set)(mem: Set){MW: MachineWidth mword} := {
  BitWidth: BitWidths;

  loadWordwXLEN: mem -> mword ->  mword;
  
  storeWordwXLEN: mem -> mword -> mword -> mem;

}.
                                                                        
(*
  Definition loadWordwXLEN(memL: mem)(addr: mword): mword.
    clear -addr memL IsMem B mword_word_wXLEN.
    rewrite mword_word_wXLEN.
    unfold wXLEN in *.
    destruct bitwidth.
    - exact (Memory.loadWord memL addr).
    - exact (Memory.loadDouble memL addr).
  Defined.

  Definition TODO{T: Type}: T. Proof using. Admitted.
  
  Definition storeWordwXLEN(m: mem)(a v: mword): mem.
    unfold wXLEN, bitwidth in *.
    clear - m a v IsMem mword_word_wXLEN.
    rewrite mword_word_wXLEN in *.
    destruct B.
    - refine (Memory.storeWord m a v).
      Fail rewrite mword_word_wXLEN in IsMem.
      apply TODO.
    - refine (Memory.storeDouble m a v). apply TODO.
      Grab Existential Variables.
      apply TODO. apply TODO.
  Defined.


  BitWidths.BitWidths
*)