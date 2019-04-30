Require Import Coq.Lists.List.
Require Import coqutil.Z.Lia.
Import ListNotations.
Require Import coqutil.Word.Properties.
Require Import riscv.Utility.Monads.
Require Import riscv.Spec.Primitives.
Require Import riscv.Spec.MetricPrimitives.
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
Require Import riscv.Platform.MetricRiscvMachine.
Require Import bedrock2.ptsto_bytes.


Open Scope Z_scope.
Open Scope ilist_scope.

Definition x1: Z := 1.
Definition x2: Z := 2.

(* average of register x1 and x2 put into x2 *)
Definition asm_prog_1: list Instruction := [[
  Add x2 x1 x2;
  Srai x2 x2 1
]].

Definition input_ptr: Z := Ox"400".
Definition output_ptr: Z := Ox"500".

(* a program with memory operations *)
Definition asm_prog_2: list Instruction := [[
  Lw x1 Register0 input_ptr;
  Lw x2 Register0 (input_ptr+4)
]] ++
asm_prog_1 ++ [[
  Sw Register0 x2 output_ptr
]].

Section Verif.

  Context {W: Words}.
  Context {Registers: map.map Register word}.
  Context {Registers_ok: map.ok Registers}.
  Context {mem: map.map word byte}.
  Context {mem_ok: map.ok mem}.
  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {PR: MetricPrimitives PRParams}.

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

  Ltac simulate'_step :=
    first [ eapply go_loadWord_sep ; simpl in *; simpl_word_exprs (@word_ok W); [sidecondition..|]
          | eapply go_storeWord_sep; simpl in *; simpl_word_exprs (@word_ok W); [sidecondition..|intros]
          | simulate_step ].

  Ltac simulate' := repeat simulate'_step.

  Ltac run1det :=
    eapply runsTo_det_step;
    [ simulate';
      match goal with
      | |- ?mid = ?RHS =>
        (* simpl RHS because mid will be instantiated to it and turn up again in the next step *)
        is_evar mid; simpl; reflexivity
      | |- _ => fail 10000 "simulate' did not go through completely"
      end
    | ].

  Lemma asm_prog_1_encodable: valid_instructions iset asm_prog_1.
  Proof.
    unfold valid_instructions. intros. simpl in *.
    repeat destruct H as [? | H]; subst instr || contradiction.
    all: destruct iset; cbv; clear; firstorder discriminate.
  Qed.

  Definition gallina_prog_1(v1 v2: word): word :=
    word.srs (word.add v1 v2) (word.of_Z 1).

  Lemma asm_prog_1_correct: forall (initial: MetricRiscvMachine) newPc R (v1 v2: word),
      map.get initial.(getRegs) x1 = Some v1 ->
      map.get initial.(getRegs) x2 = Some v2 ->
      newPc = word.add initial.(getPc)
                       (word.mul (word.of_Z 4) (word.of_Z (Z.of_nat (List.length asm_prog_1)))) ->
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
    assert (valid_register x1). { unfold valid_register, x1. blia. }
    assert (valid_register x2). { unfold valid_register, x2. blia. }
    pose proof asm_prog_1_encodable.
    destruct initial as [ [initial_regs initial_pc initial_nextPc initial_mem initial_trace] initial_metrics].
    unfold asm_prog_1 in *.
    simpl in *.
    subst.
    simpl.
    run1det.
    run1det.
    eapply runsToDone.
    simpl.
    repeat split; first [ solve_word_eq word_ok | assumption | idtac ].
    apply map.get_put_same.
  Qed.

  Opaque asm_prog_1.

  Lemma asm_prog_2_encodable: valid_instructions iset asm_prog_2.
  Proof.
    unfold valid_instructions. intros. simpl in *.
    repeat destruct H as [? | H]; subst instr || contradiction.
    all: destruct iset; cbv; clear; firstorder discriminate.
  Qed.

  Definition gallina_prog_2(v1 v2: w32): word :=
    gallina_prog_1 (word.of_Z (BitOps.signExtend 32 (LittleEndian.combine 4 v1)))
                   (word.of_Z (BitOps.signExtend 32 (LittleEndian.combine 4 v2))).

  Arguments LittleEndian.combine: simpl never.

  Lemma word_goal_1_TODO: forall initial_pc : word,
      word.add
        (word.add (word.add (word.add initial_pc (word.of_Z 4)) (word.of_Z 4))
                  (word.mul (word.of_Z 4) (word.of_Z (Z.of_nat (Datatypes.length asm_prog_1)))))
        (word.of_Z 4) =
      word.add initial_pc
               (word.mul (word.of_Z 4)
                         (word.of_Z
                            (Z.pos (Pos.succ
                                      (Pos.of_succ_nat (Datatypes.length asm_prog_1 + 1)))))).
  Proof using .
  Admitted.

  Axiom fix_updated_mem_TODO: False.

  Lemma asm_prog_2_correct: forall (initial: MetricRiscvMachine) newPc
                                  (argvars resvars: list Register) R (v1 v2 dummy: w32),
      newPc = word.add initial.(getPc)
                       (word.mul (word.of_Z 4) (word.of_Z (Z.of_nat (List.length asm_prog_2)))) ->
      (program initial.(getPc) asm_prog_2 *
       ptsto_bytes 4 (word.of_Z input_ptr) v1 *
       ptsto_bytes 4 (word.of_Z (input_ptr+4)) v2 *
       ptsto_bytes 4 (word.of_Z output_ptr) dummy * R)%sep initial.(getMem) ->
      initial.(getNextPc) = word.add initial.(getPc) (word.of_Z 4) ->
      runsTo (mcomp_sat (run1 iset)) initial
             (fun final =>
                final.(getPc) = newPc /\
                final.(getNextPc) = add newPc (word.of_Z 4) /\
                (program initial.(getPc) asm_prog_2 * R)%sep final.(getMem) /\
                map.get final.(getRegs) x2 = Some (gallina_prog_2 v1 v2)).
  Proof.
    intros.
    assert (valid_register x1). { unfold valid_register, x1. blia. }
    assert (valid_register x2). { unfold valid_register, x2. blia. }
    pose proof asm_prog_2_encodable.
    destruct initial as [ [initial_regs initial_pc initial_nextPc initial_mem initial_trace] initial_metrics].
    unfold asm_prog_2 in *.
    simpl in *.
    unfold program in *.
    seprewrite_in @array_append H0. simpl in *.
    subst.
    simpl.

    run1det.
    run1det.
    eapply runsTo_trans. {
      eapply asm_prog_1_correct; simpl.
      - rewrite map.get_put_diff by (unfold x1, x2; blia).
        apply map.get_put_same.
      - apply map.get_put_same.
      - reflexivity.
      - sidecondition.
      - reflexivity.
    }
    simpl.
    intros middle (? & ? & ? & ?).
    destruct middle as [ [middle_regs middle_pc middle_nextPc middle_mem middle_trace] middle_metrics].    simpl in *.
    subst.

    clear H6.

    (* TODO matching up addresses should work automatically *)
    replace (@word.add _ (@word W)
              (@word.add _ (@word W)
                 (@word.add _ (@word W) initial_pc (@word.of_Z _ (@word W) 4))
                 (@word.of_Z _ (@word W) 4))
              (@word.of_Z _ (@word W)
                 (@word.unsigned _ (@word W) (@word.of_Z _ (@word W) 4) *
                  BinInt.Z.of_nat (@Datatypes.length Instruction asm_prog_1))))
      with (@word.add _ (@word W)
        (@word.add _ (@word W) (@word.add _ (@word W) initial_pc (@word.of_Z _ (@word W) 4))
           (@word.of_Z _ (@word W) 4))
        (@word.mul _ (@word W) (@word.of_Z _ (@word W) 4)
           (@word.of_Z _ (@word W) (Z.of_nat (@Datatypes.length Instruction asm_prog_1)))))
      in H1; cycle 1. {
      clear.
      change BinInt.Z.of_nat with Z.of_nat in *.
      f_equal.
      apply word.unsigned_inj.
      rewrite word.unsigned_mul.
      rewrite word.unsigned_of_Z at 2. unfold word.wrap.
      rewrite (word.unsigned_of_Z (4 mod 2 ^ width * Z.of_nat (Datatypes.length asm_prog_1))).
      rewrite! word.unsigned_of_Z. unfold word.wrap.
      apply Zmult_mod_idemp_r.
    }

    run1det.
    simpl in *.
    eapply runsToDone.
    simpl.
    repeat split.
    - clear. rewrite List.app_length. simpl. rewrite word_goal_1_TODO. reflexivity.
    - clear. rewrite List.app_length. simpl. rewrite word_goal_1_TODO. reflexivity.
    - (* TODO *) case fix_updated_mem_TODO.
    - assumption.
  Qed.

End Verif.

(* Print Assumptions asm_prog_2_correct. just word_goal_1_TODO and fix_updated_mem *)
