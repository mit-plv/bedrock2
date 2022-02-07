Require Import List Coq.ZArith.ZArith.

Require Import end2end.End2EndLightbulb.
Import riscv.Utility.InstructionNotations.
Import bedrock2.NotationsCustomEntry.
Import bedrock2.Hexdump.

Local Open Scope Z_scope.
Local Open Scope hexdump_scope.

Set Printing Width 108.

Goal True.
  pose lightbulb_insts as p.
  unfold lightbulb_insts in p.
  let x := eval cbv in (Pipeline.instrencode lightbulb_insts) in idtac x.

  (* pose ((IInstruction (Jal 0 8)) *)
  (*         :: (IInstruction (Jal 0 0)) (* When a test gets failed.. *) *)
  (*         :: (IInstruction (Lui 1 (0x00004000))) *)
  (*         :: (IInstruction (Lui 2 (0x12345000))) *)
  (*         :: (IInstruction (Addi 2 2 (0x00000678))) *)
  (*         :: (IInstruction (Lui 3 (0x00005000))) *)
  (*         :: (IInstruction (Addi 3 3 (0x00000678))) *)
  (*         :: (IInstruction (Addi 4 4 (0x00000078))) *)
  (*         (* Test 1: LW after SW *) *)
  (*         :: (IInstruction (Sw 1 2 (-4))) *)
  (*         :: (IInstruction (Lw 5 1 (-4))) *)
  (*         :: (IInstruction (Bne 2 5 (-20))) *)
  (*         (* Test 2: LH after SH (word-aligned) *) *)
  (*         :: (IInstruction (Sh 1 3 (-8))) *)
  (*         :: (IInstruction (Lh 6 1 (-8))) *)
  (*         :: (IInstruction (Bne 3 6 (-32))) *)
  (*         (* Test 3: LB after SB (word-aligned) *) *)
  (*         :: (IInstruction (Sb 1 4 (-12))) *)
  (*         :: (IInstruction (Lb 7 1 (-12))) *)
  (*         :: (IInstruction (Bne 4 7 (-44))) *)
  (*         (* All the tests passed! Loop here. *) *)
  (*         :: (IInstruction (Jal 0 0)) *)
  (*         :: nil) *)
  (*   as p. *)
  (* let x := eval cbv in (Pipeline.instrencode p) in idtac x. *)

Abort.
Unset Printing Width.
