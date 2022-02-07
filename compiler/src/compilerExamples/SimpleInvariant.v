Require Import coqutil.Datatypes.PropSet.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.util.Common.
Require Import coqutil.Tactics.Simp.
Require Import compiler.SeparationLogic.
Require Export coqutil.Word.SimplWordExpr.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.DivisibleBy4.
Require Import compiler.EmitsValid.
Require Import compiler.MetricsToRiscv.
Require Import compiler.FlatImp.
Require Import compiler.RunInstruction.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvLiterals.
Require Import riscv.Utility.InstructionCoercions.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Monads.
Require Import riscv.Spec.Machine.

Arguments Jal (_)%Z (_)%Z. (* needed when inside a (_)%sep *)

Section Proofs.
  Context {iset: Decode.InstructionSet}.
  Context {fun_pos_env: map.map String.string Z}.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Context {locals: map.map Z word}.
  Context {mem: map.map word byte}.
  Context {env: map.map String.string (list Z * list Z * FlatImp.stmt Z)}.
  Context {M: Type -> Type}.
  Context {MM: Monads.Monad M}.
  Context {RVM: Machine.RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {ext_spec: Semantics.ExtSpec}.
  Context {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}.
  Context {locals_ok: map.ok locals}.
  Context {mem_ok: map.ok mem}.
  Context {fun_pos_env_ok: map.ok fun_pos_env}.
  Context {env_ok: map.ok env}.
  Context {PR: MetricPrimitives.MetricPrimitives PRParams}.
  Context {BWM: bitwidth_iset width iset}.
  Context (compile_ext_call: fun_pos_env -> Z -> Z -> stmt Z -> list Instruction).

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Notation RiscvMachine := MetricRiscvMachine.

  Notation "'len' l" := (Z.of_nat (List.length l)) (at level 10).
  Notation "[/ a ]" := (word.of_Z a). (* squeeze/ a Z into a word *)
  Notation "[\ a ]" := (word.unsigned a). (* open up\ a word so that it becomes a Z *)

  Definition pc_in_range(m: RiscvMachine)(base: word)(l: Z): Prop :=
    [\getPc m] mod 4 = 0 /\
    [\word.sub (getPc m) base] <= l /\
    getNextPc m = word.add (getPc m) [/4].

  Definition Inv(m: RiscvMachine): Prop :=
    exists (insts: list Instruction) (data: list byte)
           (p_insts: word) (p_data: word),
      pc_in_range m p_insts (4 * len insts) /\
      (* begin ignore *)
      subset (footpr (program iset p_insts insts *
                      ptsto_instr iset (word.add p_insts [/4 * len insts])
                                  (Jal RegisterNames.zero (-4 * len insts)))%sep)
             (of_list m.(getXAddrs)) /\
      (* end ignore *)
      (program iset p_insts insts *
       ptsto_instr iset (word.add p_insts [/4 * len insts]) (Jal RegisterNames.zero (-4 * len insts)) *
       array ptsto [/1] p_data data)%sep m.(getMem) /\
      (* TODO we would also have to say that Sb and Lb only touch memory within data *)
      (forall inst, In inst insts -> (exists r1 r2 ofs, inst = Sb r1 r2 ofs) \/
                                     (exists r1 r2 ofs, inst = Lb r1 r2 ofs) \/
                                     (exists r1 r2 r3,  inst = Add r1 r2 r3)).

  Lemma pc_stays_in_range_and_instructions_remain_the_same_for_one_step:
    forall m, Inv m -> mcomp_sat (Run.run1 iset) m Inv.
  Proof.
    intros m HI.
    unfold Inv, pc_in_range in *.
    destruct_RiscvMachine m.
    simp.
    assert (exists insts0 inst insts1, insts = insts0 ++ [inst] ++ insts1 /\
                                       m_pc = word.add p_insts [/4 * len insts0])
      as P by admit.
    simp.
    match goal with
    | H: forall (_: Instruction), In _ _ -> _ |- _ =>
      specialize (H inst);
        rename H into A; move A at bottom
    end.
    specialize_hyp A. {
      eauto 10 using in_cons, in_or_app, in_eq.
    }
    destruct A as [ A | [A | A] ]; simp.
    - simulate'.

  Abort.

End Proofs.

Require compilerExamples.MMIO.
Require Import riscv.Platform.FE310ExtSpec.

Section PrintExamples.
  Context {iset: Decode.InstructionSet}.
  Context {fun_pos_env: map.map String.string Z}.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Context {locals: map.map Z word}.
  Context {mem: map.map word byte}.
  Context {env: map.map String.string (list Z * list Z * FlatImp.stmt Z)}.
  Context {M: Type -> Type}.
  Context {MM: Monads.Monad M}.
  Context {RVM: Machine.RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {ext_spec: Semantics.ExtSpec}.
  Context {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}.
  Context {locals_ok: map.ok locals}.
  Context {mem_ok: map.ok mem}.
  Context {fun_pos_env_ok: map.ok fun_pos_env}.
  Context {env_ok: map.ok env}.
  Context {PR: MetricPrimitives.MetricPrimitives PRParams}.
  Context {BWM: bitwidth_iset width iset}.
  Context (compile_ext_call: fun_pos_env -> Z -> Z -> stmt Z -> list Instruction).

  Import MonadNotations.
  Open Scope bool_scope.
  Open Scope string_scope.

  Goal False.
    set (executeM := riscv.Spec.ExecuteM.execute).
    unfold ExecuteM.execute in *.

    unfold highBits in *; simpl in *.

  Abort.

  Goal False.
    set (isMMIOAddr := MinimalMMIO.isMMIOAddr).
    simpl in *.

    unfold isOTP, isPRCI, isGPIO0, isUART0 in *.

    set (test := (isMMIOAddr (word.of_Z (0x00020004)))).
  Abort.

  Goal False.
    set (executeI := riscv.Spec.ExecuteI.execute).
    unfold ExecuteI.execute in *.

  Abort.

End PrintExamples.
