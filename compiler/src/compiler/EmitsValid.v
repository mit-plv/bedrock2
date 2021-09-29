(* Not needed at the moment because we validate the concrete expressions output by the compiler *)
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Z.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Decidable.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.
Require Import coqutil.Z.BitOps.
Require Import riscv.Platform.Run.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Primitives.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Utility.Tactics.
Require Import riscv.Utility.Utility.
Require Import compiler.FlatImp.
Require Import compiler.FlatToRiscvDef. Import FlatToRiscvDef.
Require Import riscv.Platform.Memory.
Require Import coqutil.Z.prove_Zeq_bitwise.

Local Open Scope Z_scope.

Set Implicit Arguments.

#[export] Hint Unfold
  funct12_EBREAK
  funct12_ECALL
  funct12_MRET
  funct12_SRET
  funct12_URET
  funct12_WFI
  funct3_ADD
  funct3_ADDI
  funct3_ADDIW
  funct3_ADDW
  funct3_AMOD
  funct3_AMOW
  funct3_AND
  funct3_ANDI
  funct3_BEQ
  funct3_BGE
  funct3_BGEU
  funct3_BLT
  funct3_BLTU
  funct3_BNE
  funct3_CSRRC
  funct3_CSRRCI
  funct3_CSRRS
  funct3_CSRRSI
  funct3_CSRRW
  funct3_CSRRWI
  funct3_DIV
  funct3_DIVU
  funct3_DIVUW
  funct3_DIVW
  funct3_FENCE
  funct3_FENCE_I
  funct3_LB
  funct3_LBU
  funct3_LD
  funct3_LH
  funct3_LHU
  funct3_LW
  funct3_LWU
  funct3_MUL
  funct3_MULH
  funct3_MULHSU
  funct3_MULHU
  funct3_MULW
  funct3_OR
  funct3_ORI
  funct3_PRIV
  funct3_REM
  funct3_REMU
  funct3_REMUW
  funct3_REMW
  funct3_SB
  funct3_SD
  funct3_SH
  funct3_SLL
  funct3_SLLI
  funct3_SLLIW
  funct3_SLLW
  funct3_SLT
  funct3_SLTI
  funct3_SLTIU
  funct3_SLTU
  funct3_SRA
  funct3_SRAI
  funct3_SRAIW
  funct3_SRAW
  funct3_SRL
  funct3_SRLI
  funct3_SRLIW
  funct3_SRLW
  funct3_SUB
  funct3_SUBW
  funct3_SW
  funct3_XOR
  funct3_XORI
  funct5_AMOADD
  funct5_AMOAND
  funct5_AMOMAX
  funct5_AMOMAXU
  funct5_AMOMIN
  funct5_AMOMINU
  funct5_AMOOR
  funct5_AMOSWAP
  funct5_AMOXOR
  funct5_LR
  funct5_SC
  funct6_SLLI
  funct6_SRAI
  funct6_SRLI
  funct7_ADD
  funct7_ADDW
  funct7_AND
  funct7_DIV
  funct7_DIVU
  funct7_DIVUW
  funct7_DIVW
  funct7_MUL
  funct7_MULH
  funct7_MULHSU
  funct7_MULHU
  funct7_MULW
  funct7_OR
  funct7_REM
  funct7_REMU
  funct7_REMUW
  funct7_REMW
  funct7_SFENCE_VMA
  funct7_SLL
  funct7_SLLIW
  funct7_SLLW
  funct7_SLT
  funct7_SLTU
  funct7_SRA
  funct7_SRAIW
  funct7_SRAW
  funct7_SRL
  funct7_SRLIW
  funct7_SRLW
  funct7_SUB
  funct7_SUBW
  funct7_XOR
  opcode_AMO
  opcode_AUIPC
  opcode_BRANCH
  opcode_JAL
  opcode_JALR
  opcode_LOAD
  opcode_LOAD_FP
  opcode_LUI
  opcode_MADD
  opcode_MISC_MEM
  opcode_MSUB
  opcode_NMADD
  opcode_NMSUB
  opcode_OP
  opcode_OP_32
  opcode_OP_FP
  opcode_OP_IMM
  opcode_OP_IMM_32
  opcode_STORE
  opcode_STORE_FP
  opcode_SYSTEM
 : unf_encode_consts.

#[export] Hint Unfold
  verify
  verify_Invalid
  verify_R
  verify_R_atomic
  verify_I
  verify_I_shift_57
  verify_I_shift_66 bitwidth
  verify_I_system
  verify_S
  verify_SB
  verify_U
  verify_UJ
  verify_Fence
: unf_verify.


Ltac simpl_pow2 :=
      repeat (so fun hyporgoal => match hyporgoal with
              | context [(2 ^ ?a)%Z] =>
                  let r := eval cbv in (2 ^ a)%Z in change (2 ^ a)%Z with r in *
              end).

Lemma bitSlice_bounds: forall w start eend,
    0 <= start <= eend ->
    0 <= bitSlice w start eend < 2 ^ (eend - start).
Proof.
  intros. rewrite bitSlice_alt by assumption.
  unfold bitSlice'.
  apply Z.mod_pos_bound.
  apply Z.pow_pos_nonneg; blia.
Qed.

Lemma times4mod2: forall (a: Z),
    (a * 4) mod 2 = 0.
Proof.
  intros. change 4 with (2 * 2). rewrite Z.mul_assoc.
  apply Z.mod_mul. congruence.
Qed.


Tactic Notation "so" tactic(f) :=
  match goal with
  | _: ?A |- _  => f A
  |       |- ?A => f A
  end.

Ltac unify_universes_for_blia :=
  repeat (so fun hyporgoal => match hyporgoal with
                              | context [?x] =>
                                let T := type of x in
                                unify Z T;
                                assert_fails (is_var x);
                                lazymatch goal with
                                | nn := x |- _ => fail
                                | |- _ => idtac
                                end;
                                let n := fresh "n" in set (n := x) in *
                              end);
  repeat match goal with
         | nn := _ |- _ => subst nn
         end.

(* workaround for https://github.com/coq/coq/issues/9268 *)
Ltac blia' := unify_universes_for_blia; blia.

Inductive supported_iset: InstructionSet -> Prop :=
| supported_RV32I: supported_iset RV32I
| supported_RV64I: supported_iset RV64I
| supported_RV32IM: supported_iset RV32IM
| supported_RV64IM: supported_iset RV64IM.

Section EmitsValid.

  Context {iset: InstructionSet}.

  Local Arguments Z.of_nat: simpl never.
  Local Arguments Z.mul: simpl never.
  Local Arguments Z.pow: simpl never.
  Local Arguments Z.add: simpl never.

  Lemma compile_lit_12bit_emits_valid: forall r iset w,
      valid_register r ->
      valid_instructions iset (compile_lit_12bit r w).
  Proof.
    intros. unfold compile_lit_12bit, valid_instructions.
    intros. simpl in *. destruct H0; [subst|contradiction].
    split; [|exact I]. simpl.
    autounfold with unf_verify unf_encode_consts.
    unfold valid_register in *.
    pose proof (signExtend_range 12 w eq_refl).
    simpl_pow2.
    blia.
  Qed.

  Lemma remove_lobits: forall v i,
      0 <= i ->
      (v - bitSlice v 0 i) mod 2 ^ i = 0.
  Proof.
    intros.
    rewrite bitSlice_alt by blia. unfold bitSlice'.
    rewrite Z.sub_0_r.
    change (2 ^ 0) with 1.
    rewrite Z.div_1_r.
    rewrite Zminus_mod_idemp_r.
    rewrite Z.sub_diag.
    apply Zmod_0_l.
  Qed.

  Lemma compile_lit_32bit_emits_valid: forall r v iset,
      valid_register r ->
      valid_instructions iset (compile_lit_32bit r v).
  Proof.
    intros. unfold compile_lit_32bit, valid_instructions.
    intros instr HIn. simpl in HIn.
    assert (- 2 ^ 31 <= Z.lxor (signExtend 32 v) (signExtend 12 v) < 2 ^ 31) as P1. {
      match goal with
      | |- _ <= ?x < _ => replace x with (signExtend 32 x)
      end.
      - change 31 with (32 - 1). apply signExtend_range. reflexivity.
      - clear -H.
        prove_Zeq_bitwise.
    }
    assert (Z.lxor (signExtend 32 v) (signExtend 12 v) mod 2 ^ 12 = 0) as P2. {
      rewrite <- Z.land_ones by blia.
      rewrite signExtend_alt_bitwise by blia. unfold signExtend_bitwise.
      prove_Zeq_bitwise.
    }
    assert (- 2 ^ 11 <= signExtend 12 v < 2 ^ 11) as P3. {
      change 11 with (12 - 1). apply signExtend_range. reflexivity.
    }
    destruct HIn as [ ? | [? | ?] ]; [subst..|contradiction];
      (split; [|exact I]); simpl;
        autounfold with unf_verify unf_encode_consts;
        unfold valid_register in *;
        simpl_pow2;
        blia.
  Qed.

  Lemma valid_Slli: forall rd rs shamt,
      0 <= shamt < 32 ->
      valid_register rd ->
      valid_register rs ->
      verify (IInstruction (Slli rd rs shamt)) iset.
  Proof.
    intros.
    unfold verify, valid_register in *;
    simpl;
    autounfold with unf_encode_consts unf_verify;
    destruct iset;
    blia.
  Qed.

  Lemma valid_Addi_bitSlice: forall rd rs w i j iset,
      0 <= i <= j ->
      j - i <= 11 ->
      valid_register rd ->
      valid_register rs ->
      verify (IInstruction (Addi rd rs (bitSlice w i j))) iset.
  Proof.
    intros.
    assert (- 2 ^ 11 <= bitSlice w i j < 2 ^ 11). {
      rewrite bitSlice_alt by assumption.
      unfold bitSlice'.
      assert (2 ^ (j - i) <> 0) as A. {
        apply Z.pow_nonzero; blia.
      }
      pose proof (Z.mod_bound_or (w / 2 ^ i) (2 ^ (j - i)) A) as P.
      assert (0 < 2 ^ 11) by reflexivity.
      assert (0 < 2 ^ (j - i)). {
        apply Z.pow_pos_nonneg; blia.
      }
      assert (2 ^ (j - i) <= 2 ^ 11) as B. {
        apply Z.pow_le_mono_r; blia.
      }
      blia.
    }
    unfold verify, valid_register in *;
    simpl;
    autounfold with unf_encode_consts unf_verify;
    destruct iset;
    blia.
  Qed.

  Lemma valid_Xori_bitSlice: forall rd rs w i j iset,
      0 <= i <= j ->
      j - i <= 11 ->
      valid_register rd ->
      valid_register rs ->
      verify (IInstruction (Xori rd rs (bitSlice w i j))) iset.
  Proof.
    intros.
    assert (- 2 ^ 11 <= bitSlice w i j < 2 ^ 11). {
      rewrite bitSlice_alt by assumption.
      unfold bitSlice'.
      assert (2 ^ (j - i) <> 0) as A. {
        apply Z.pow_nonzero; blia.
      }
      pose proof (Z.mod_bound_or (w / 2 ^ i) (2 ^ (j - i)) A) as P.
      assert (0 < 2 ^ 11) by reflexivity.
      assert (0 < 2 ^ (j - i)). {
        apply Z.pow_pos_nonneg; blia.
      }
      assert (2 ^ (j - i) <= 2 ^ 11) as B. {
        apply Z.pow_le_mono_r; blia.
      }
      blia.
    }
    unfold verify, valid_register in *;
    simpl;
    autounfold with unf_encode_consts unf_verify;
    destruct iset;
    blia.
  Qed.

  Lemma compile_lit_64bit_emits_valid: forall r w,
      valid_register r ->
      valid_instructions iset (compile_lit_64bit r w).
  Proof.
    intros. unfold compile_lit_64bit, valid_instructions.
    intros. apply in_app_or in H0. destruct H0. {
      eapply compile_lit_32bit_emits_valid; try eassumption.
    }
    simpl in *.
    repeat destruct H0 as [H0 | H0]; [subst instr..|contradiction];
      (eapply valid_Xori_bitSlice || eapply valid_Slli); try eassumption; try blia.
  Qed.

  Lemma compile_lit_emits_valid: forall r w,
      valid_register r ->
      valid_instructions iset (compile_lit iset r w).
  Proof.
    intros.
    unfold compile_lit.
    repeat (destruct_one_match ||
            eauto using compile_lit_12bit_emits_valid,
                        compile_lit_32bit_emits_valid,
                        compile_lit_64bit_emits_valid).
  Qed.

  Import Syntax.bopname.
  Lemma compile_op_emits_valid: forall x op y z,
      supported_iset iset ->
      valid_register x ->
      valid_register y ->
      valid_register z ->
      ((op = mul \/ op = mulhuu \/ op = divu \/ op = remu) -> (iset = RV32IM \/ iset = RV64IM)) ->
      valid_instructions iset (compile_op x op y z).
  Proof.
    unfold valid_instructions.
    intros * H ? ? ? ? ? H3.
    destruct op; simpl in *; (repeat destruct H3; try contradiction);
          inversion H; unfold verify; simpl;
          autounfold with unf_verify unf_encode_consts;
          repeat match goal with
                 | |- context [ bitSlice ?w ?start ?eend ] =>
                   unique pose proof (@bitSlice_bounds w start eend)
                 end;
          simpl_pow2;
          unfold valid_register in *;
          try solve [constructor];
          try blia;
          try (split; [blia|auto]);
          destruct iset; auto; intuition try congruence.
  Qed.

  Lemma compile_bcond_by_inverting_emits_valid: forall cond amt,
      valid_registers_bcond cond ->
      - 2 ^ 12 <= amt < 2 ^ 12 ->
      amt mod 2 = 0 ->
      verify (compile_bcond_by_inverting cond amt) iset.
  Proof.
    unfold valid_registers_bcond, ForallVars_bcond, valid_register.
    intros.
    simpl in *.
    destruct cond; [destruct op|]; simpl;
    unfold verify;
    destruct bitwidth;
    simpl;
    autounfold with unf_encode_consts unf_verify;
    intuition blia.
  Qed.

  Lemma compile_load_emits_valid: forall x y sz offset,
      valid_register x ->
      valid_register y ->
      - 2 ^ 11 <= offset < 2 ^ 11 ->
      valid_instructions iset [compile_load iset sz x y offset].
  Proof.
    intros. unfold valid_instructions, valid_register, compile_load in *.
    unfold verify, respects_bounds, verify_iset. simpl.
    destr (bitwidth iset =? 32); [rewrite E|];
    unfold bitwidth in *;
    destruct sz eqn: Eqsz; unfold valid_instructions, valid_register in *; simpl;
      intros;
      (destruct H2; [|contradiction]);
      subst instr;
      unfold verify;
      simpl;
      rewrite? E; simpl;
      autounfold with unf_encode_consts unf_verify;
      rewrite? E; simpl;
      intuition (try blia);
      destruct iset; try intuition congruence.
    (* TODO verify_iset add F instructions to verify_iset and adapt decode_encode proof *)
  Abort.

  Lemma compile_store_emits_valid: forall x y sz offset,
      valid_register x ->
      valid_register y ->
      - 2 ^ 11 <= offset < 2 ^ 11 ->
      valid_instructions iset [compile_store iset sz x y offset].
  Proof.
    intros.
    intros. unfold valid_instructions, valid_register, compile_store in *.
    unfold verify, respects_bounds, verify_iset. simpl.
    destr (bitwidth iset =? 32); [rewrite E|];
    unfold bitwidth in *;
    destruct sz; inversion H; clear H; unfold valid_instructions, valid_register in *; simpl;
      intros;
      (destruct H; [|contradiction]);
      subst instr;
      unfold verify;
      simpl;
      rewrite? E;
      simpl;
      autounfold with unf_encode_consts unf_verify;
      intuition (try blia);
      destruct iset; try intuition congruence.
    (* TODO verify_iset add F instructions to verify_iset and adapt decode_encode proof *)
  Abort.

  Lemma compile_lit_size: forall x v,
      0 <= Z.of_nat (length (compile_lit iset x v)) <= 8.
  Proof.
    intros. unfold compile_lit, compile_lit_64bit, compile_lit_32bit, compile_lit_12bit.
    repeat destruct_one_match; cbv; split; discriminate.
  Qed.

  (*
  Lemma compile_stmt_size: forall s,
    0 <= Z.of_nat (length (compile_stmt s)) <= stmt_size s.
  Proof.
    induction s; simpl; try apply compile_lit_size;
      try destruct op; try solve [destruct f]; simpl;
      repeat (rewrite List.app_length || simpl in * ); try blia.
    pose proof (compile_ext_call_length binds a args). blia.
  Qed.

  Context {fun_pos_env: coqutil.Map.Interface.map.map String.string Z}.

  Axiom compile_function_emits_valid: forall e pos argnames resnames body,
      supported_iset iset ->
      Forall valid_register argnames ->
      Forall valid_register resnames ->
      valid_FlatImp_vars body ->
      stmt_not_too_big body ->
      valid_instructions iset (compile_function e pos (argnames, resnames, body)).

  Lemma compile_stmt_emits_valid: forall s,
      supported_iset iset ->
      valid_FlatImp_vars s ->
      stmt_not_too_big s ->
      valid_instructions iset (compile_stmt s).
  Proof.
    assert (- 2 ^ 11 <= 0 < 2 ^ 11) by blia.
    induction s; intros; simpl in *; intuition (
      eauto 10 using valid_FlatImp_var_implies_valid_register, Forall_impl,
                 compile_load_emits_valid,
                 compile_store_emits_valid,
                 compile_lit_emits_valid,
                 compile_op_emits_valid,
                 compile_ext_call_emits_valid
    );
    unfold valid_instructions, valid_FlatImp_var, Register0, stmt_not_too_big in *;
    intros; simpl in *;
    repeat match goal with
           | H: _ \/ _ |- _ => destruct H
           | H: In _ (_ ++ _) |- _ => apply in_app_iff in H
           | H: In _ (_ :: _) |- _ => apply in_inv in H
           | s: stmt |- _ => unique pose proof (compile_stmt_size s)
           end;
    subst;
    repeat (so fun hyporgoal => match hyporgoal with
            | context [(2 ^ ?a)%Z] =>
              let r := eval cbv in (2 ^ a)%Z in change (2 ^ a)%Z with r in *
            end);
    try solve
        [ apply compile_bcond_by_inverting_emits_valid;
          [ auto using valid_FlatImp_var_implies_valid_register,
                       valid_FlatImp_vars_bcond_implies_valid_registers_bcond
          | blia'
          | apply times4mod2 ]
        | match goal with
          | H: _ |- _ => solve [apply H;
                                (blia || auto using valid_FlatImp_var_implies_valid_register,
                                     valid_FlatImp_vars_bcond_implies_valid_registers_bcond)]
          end
        | unfold verify in *;
          destruct iset;
          simpl in *; intros;
          intuition subst; simpl in *;
          autounfold with unf_encode_consts unf_verify;
          repeat match goal with
                 | |- context [(?x * 4) mod 2] => rewrite (times4mod2 x)
                 end;
          blia' ].
  Qed.
  *)

End EmitsValid.
