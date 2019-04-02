Require Import Coq.ZArith.BinInt.
Require Import Coq.micromega.Lia.
Require Import Coq.omega.Omega.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import riscv.Utility.Monads.
Require Import riscv.Utility.Utility.
Require Import riscv.Spec.Decode.
Require Import riscv.Platform.Memory.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.Run.
Require Import riscv.Spec.Execute.
Require Import riscv.Proofs.DecodeEncode.
Require Import coqutil.Tactics.Tactics.
Require Import compiler.util.Tactics.
Require Import compiler.SeparationLogic.
Require Import compiler.EmitsValid.
Require Import bedrock2.ptsto_bytes.
Require Import bedrock2.Scalars.
Require Import riscv.Utility.Encode.
Require Import riscv.Proofs.EncodeBound.
Require Import coqutil.Decidable.
Require Import compiler.GoFlatToRiscv.
Require Import riscv.Utility.InstructionCoercions. Local Open Scope ilist_scope.

Section Run.

  Context {W: Words}.
  Context {Registers: map.map Register word}.
  Context {Action: Type}.
  Context {mem: map.map word byte}.
  Context {mem_ok: map.ok mem}.

  Local Notation RiscvMachineL := (RiscvMachine Register Action).

  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M (RiscvMachine Register Action)}.
  Context {PR: Primitives PRParams}.
  Variable iset: InstructionSet.

  Lemma run_Lw: forall (base addr: word) (v: w32) (rd rs: Register) (ofs: MachineInt)
                       (initialL: RiscvMachineL) (R: mem -> Prop),
      verify (Lw rd rs ofs) iset ->
      (* valid_register almost follows from verify except for then the register is Register0 *)
      valid_register rd ->
      valid_register rs ->
      (word.unsigned initialL.(getPc)) mod 4 = 0 ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      map.get initialL.(getRegs) rs = Some base ->
      addr = word.add base (word.of_Z ofs) ->
      (program initialL.(getPc) [[Lw rd rs ofs]] * ptsto_bytes 4 addr v * R)%sep
        initialL.(getMem) ->
      mcomp_sat (run1 iset) initialL (fun finalL =>
        finalL.(getRegs) = map.put initialL.(getRegs) rd (int32ToReg v) /\
        finalL.(getLog) = initialL.(getLog) /\
        (program initialL.(getPc) [[Lw rd rs ofs]] * ptsto_bytes 4 addr v * R)%sep
          finalL.(getMem) /\
        finalL.(getPc) = initialL.(getNextPc) /\
        finalL.(getNextPc) = word.add finalL.(getPc) (word.of_Z 4)).
  Proof.
    intros.
    destruct initialL as [initial_regs initial_pc initial_npc initial_mem initial_log].
    simpl in *. subst.
    simulate.
    eapply go_loadWord_sep. {
      simpl. ecancel_assumption.
    }
    simulate.
    simpl.
    repeat match goal with
           | |- _ /\ _ => split
           | |- _ => reflexivity
           | |- _ => ecancel_assumption
           end.
  Qed.

  Definition run_Load_spec(n: nat)(L: Register -> Register -> MachineInt -> Instruction): Prop :=
    forall (base addr: word) (v: HList.tuple byte n) (rd rs: Register) (ofs: MachineInt)
           (initialL: RiscvMachineL) (R: mem -> Prop),
      verify (L rd rs ofs) iset ->
      (* valid_register almost follows from verify except for then the register is Register0 *)
      valid_register rd ->
      valid_register rs ->
      (word.unsigned initialL.(getPc)) mod 4 = 0 ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      map.get initialL.(getRegs) rs = Some base ->
      addr = word.add base (word.of_Z ofs) ->
      (program initialL.(getPc) [[L rd rs ofs]] * ptsto_bytes n addr v * R)%sep
        initialL.(getMem) ->
      mcomp_sat (run1 iset) initialL (fun finalL =>
        finalL.(getRegs) = map.put initialL.(getRegs) rd
                  (word.of_Z (signExtend (8 * Z.of_nat n) (LittleEndian.combine n v))) /\
        finalL.(getLog) = initialL.(getLog) /\
        (program initialL.(getPc) [[L rd rs ofs]] * ptsto_bytes n addr v * R)%sep
          finalL.(getMem) /\
        finalL.(getPc) = initialL.(getNextPc) /\
        finalL.(getNextPc) = word.add finalL.(getPc) (word.of_Z 4)).

  Lemma run_Lw': run_Load_spec 4 Lw.
  Proof.
    unfold run_Load_spec.
    intros.
    destruct initialL as [initial_regs initial_pc initial_npc initial_mem initial_log].
    simpl in *. subst.
    simulate.
    eapply go_loadWord_sep. {
      simpl. ecancel_assumption.
    }
    simulate.
    simpl.
    repeat match goal with
           | |- _ /\ _ => split
           | |- _ => reflexivity
           | |- _ => ecancel_assumption
           end.
  Qed.

  Lemma run_Lh: run_Load_spec 2 Lh.
  Proof.
    unfold run_Load_spec.
    intros.
    destruct initialL as [initial_regs initial_pc initial_npc initial_mem initial_log].
    simpl in *. subst.
    simulate.
    eapply go_loadHalf_sep. {
      simpl. ecancel_assumption.
    }
    simulate.
    simpl.
    repeat match goal with
           | |- _ /\ _ => split
           | |- _ => reflexivity
           | |- _ => ecancel_assumption
           end.
  Qed.

End Run.
