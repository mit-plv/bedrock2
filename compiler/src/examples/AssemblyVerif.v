Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Import ListNotations.
Require Import coqutil.Word.Properties.
Require Import riscv.Utility.Monads.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Decode.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Utility.Utility.
Require Import riscv.Platform.Memory.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.MkMachineWidth.
Require Import coqutil.Map.Interface.
Require Import coqutil.Z.HexNotation.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.SeparationLogic.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.SimplWordExpr.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Utility.ListLib.


Open Scope Z_scope.
Open Scope ilist_scope.

Definition x1: Z := 1.
Definition x2: Z := 2.

Definition base: Z := Ox"400".

(* average of register x1 and x2 put into x2 *)
Definition asm_prog_1: list Instruction := [[
  Add x2 x1 x2;
  Srai x2 x2 1
]].

(* a program with memory operations *)
Definition asm_prog_2: list Instruction := [[
  Addi x1 Register0 base;
  Lw x2 x1 0;
  Add x2 x2 x2;
  Sw x1 x2 0
]].

Local Unset Universe Polymorphism. (* for Add Ring *)

Section Verif.

  Definition actname := Empty_set. (* no external actions *)

  Context {W: Words}.
  Context {Registers: map.map Register word}.
  Context {Registers_ok: map.ok Registers}.
  Context {mem: map.map word byte}.
  Context {mem_ok: map.ok mem}.
  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M (RiscvMachine Register actname)}.
  Context {PR: Primitives PRParams}.

  Definition iset := if Utility.width =? 32 then RV32IM else RV64IM.

  Ltac word_cst w :=
    match w with
    | word.of_Z ?x => let b := isZcst x in
                      match b with
                      | true => x
                      | _ => constr:(NotConstant)
                      end
    | _ => constr:(NotConstant)
    end.

  Definition word_ring_morph := word.ring_morph (word := word).
  Definition word_ring_theory := word.ring_theory (word := word).

  Hint Rewrite
    word_ring_morph.(morph_add)
    word_ring_morph.(morph_sub)
    word_ring_morph.(morph_mul)
    word_ring_morph.(morph_opp)
  : rew_word_morphism.

  Add Ring wring : word_ring_theory
      (preprocess [autorewrite with rew_word_morphism],
       morphism word_ring_morph,
       constants [word_cst]).

  Ltac run1det :=
    eapply runsTo_det_step;
    [ simulate;
      match goal with
      | |- ?mid = ?RHS =>
        (* simpl RHS because mid will be instantiated to it and turn up again in the next step *)
        is_evar mid; simpl; reflexivity
      | |- _ => fail 10000 "simulate' did not go through completely"
      end
    | ].

  Let asm_prog_1_encodable: valid_instructions iset asm_prog_1.
  Proof.
    unfold valid_instructions. intros. simpl in *.
    repeat destruct H as [? | H]; subst instr || contradiction.
    all: destruct iset; cbv; clear; firstorder discriminate.
  Qed.

  Definition gallina_prog_1(v1 v2: word): word :=
    word.srs (word.add v1 v2) (word.of_Z 1).

  Lemma asm_prog_1_correct: forall (initial: RiscvMachine Register actname) newPc
                                  (argvars resvars: list Register) R (v1 v2: word),
      map.get initial.(getRegs) x1 = Some v1 ->
      map.get initial.(getRegs) x2 = Some v2 ->
      newPc = word.add initial.(getPc)
                       (word.mul (word.of_Z 4) (word.of_Z (Zlength asm_prog_1))) ->
      (program initial.(getPc) asm_prog_1 * R)%sep initial.(getMem) ->
      initial.(getNextPc) = word.add initial.(getPc) (word.of_Z 4) ->
      runsTo (mcomp_sat (run1 iset)) initial
             (fun final =>
                final.(getPc) = newPc /\
                final.(getNextPc) = add newPc (word.of_Z 4) /\
                (program initial.(getPc) asm_prog_1 * R)%sep final.(getMem) /\
                map.get final.(getRegs) x2 = Some (gallina_prog_1 v1 v2)).
  Proof.
    intros.
    assert (valid_register x1). { unfold valid_register, x1. lia. }
    assert (valid_register x2). { unfold valid_register, x2. lia. }
    destruct initial as [initial_regs initial_pc initial_nextPc initial_mem initial_trace].
    unfold asm_prog_1 in *.
    simpl in *.
    subst.
    rewrite! Zlength_cons, Zlength_nil.
    simpl.
    run1det.
    run1det.
    eapply runsToDone.
    simpl.
    repeat split; first [ solve_word_eq word_ok | assumption | idtac ].
    apply map.get_put_same.
  Qed.

End Verif.
