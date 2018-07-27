Require Import riscv.util.BitWidths.
Require Import riscv.Utility.


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