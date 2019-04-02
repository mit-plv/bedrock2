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
Require Import compiler.SimplWordExpr.


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

  Definition iset := if width =? 32 then RV32IM else RV64IM.

  Ltac simulate'_step :=
    first [ eapply go_loadByte_sep ; simpl; [sidecondition..|]
          | eapply go_storeByte_sep; simpl; [sidecondition..|intros]
          | eapply go_loadHalf_sep ; simpl; [sidecondition..|]
          | eapply go_storeHalf_sep; simpl; [sidecondition..|intros]
          | eapply go_loadWord_sep ; simpl; [sidecondition..|]
          | eapply go_storeWord_sep; simpl; [sidecondition..|intros]
          | eapply go_loadDouble_sep ; simpl; [sidecondition..|]
          | eapply go_storeDouble_sep; simpl; [sidecondition..|intros]
          | simulate_step ].

  Ltac simulate' := repeat simulate'_step.

  Definition run_Load_spec(n: nat)(L: Register -> Register -> MachineInt -> Instruction)
             (opt_sign_extender: Z -> Z): Prop :=
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
                  (word.of_Z (opt_sign_extender (LittleEndian.combine n v))) /\
        finalL.(getLog) = initialL.(getLog) /\
        (program initialL.(getPc) [[L rd rs ofs]] * ptsto_bytes n addr v * R)%sep
          finalL.(getMem) /\
        finalL.(getPc) = initialL.(getNextPc) /\
        finalL.(getNextPc) = word.add finalL.(getPc) (word.of_Z 4)).

  Definition run_Store_spec(n: nat)(S: Register -> Register -> MachineInt -> Instruction): Prop :=
    forall (base addr v_new: word) (v_old: HList.tuple byte n) (rs1 rs2: Register)
           (ofs: MachineInt) (initialL: RiscvMachineL) (R: mem -> Prop),
      verify (S rs1 rs2 ofs) iset ->
      (* valid_register almost follows from verify except for then the register is Register0 *)
      valid_register rs1 ->
      valid_register rs2 ->
      (word.unsigned initialL.(getPc)) mod 4 = 0 ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      map.get initialL.(getRegs) rs1 = Some base ->
      map.get initialL.(getRegs) rs2 = Some v_new ->
      addr = word.add base (word.of_Z ofs) ->
      (program initialL.(getPc) [[S rs1 rs2 ofs]] * ptsto_bytes n addr v_old * R)%sep
        initialL.(getMem) ->
      mcomp_sat (run1 iset) initialL (fun finalL =>
        finalL.(getRegs) = initialL.(getRegs) /\
        finalL.(getLog) = initialL.(getLog) /\
        (program initialL.(getPc) [[S rs1 rs2 ofs]] *
         ptsto_bytes n addr (LittleEndian.split n (word.unsigned v_new)) * R)%sep
            finalL.(getMem) /\
        finalL.(getPc) = initialL.(getNextPc) /\
        finalL.(getNextPc) = word.add finalL.(getPc) (word.of_Z 4)).

  Ltac t :=
    unfold run_Load_spec, run_Store_spec;
    intros;
    match goal with
    | initialL: RiscvMachineL |- _ => destruct initialL
    end;
    simpl in *; subst;
    simulate';
    simpl;
    repeat match goal with
           | |- _ /\ _ => split
           | |- _ => reflexivity
           | |- _ => ecancel_assumption
           end.

  Lemma run_Lb: run_Load_spec 1 Lb (signExtend 8).
  Proof. t. Qed.

  Lemma run_Lbu: run_Load_spec 1 Lbu id.
  Proof. t. Qed.

  Lemma run_Lh: run_Load_spec 2 Lh (signExtend 16).
  Proof. t. Qed.

  Lemma run_Lhu: run_Load_spec 2 Lhu id.
  Proof. t. Qed.

  Lemma run_Lw: run_Load_spec 4 Lw (signExtend 32).
  Proof. t. Qed.

  Lemma run_Lw_unsigned: width = 32 -> run_Load_spec 4 Lw id.
  Proof.
    t. rewrite sextend_width_nop; [reflexivity|symmetry;assumption].
  Qed.

  Lemma run_Lwu: run_Load_spec 4 Lwu id.
  Proof. t. Qed.

  Lemma run_Ld: run_Load_spec 8 Ld (signExtend 64).
  Proof. t. Qed.

  (* Note: there's no Ldu instruction, because Ld does the same *)
  Lemma run_Ld_unsigned: run_Load_spec 8 Ld id.
  Proof.
    t. rewrite sextend_width_nop; [reflexivity|]. unfold iset in *.
    clear -H. destruct H as [_ H]. unfold verify_iset in *.
    destruct width_cases as [E | E]; rewrite E in *; simpl in *; intuition congruence.
  Qed.

  Lemma run_Sb: run_Store_spec 1 Sb.
  Proof. t. Qed.

  Lemma run_Sh: run_Store_spec 2 Sh.
  Proof. t. Qed.

  Lemma run_Sw: run_Store_spec 4 Sw.
  Proof. t. Qed.

  Lemma run_Sd: run_Store_spec 8 Sd.
  Proof. t. Qed.

End Run.
