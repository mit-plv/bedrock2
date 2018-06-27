Require Import Coq.Lists.List.
Require Import Coq.micromega.Lia.
Require Import Coq.omega.Omega.
Require Import riscv.Decode.
Require Import riscv.encode.Encode.
Require Import riscv.util.ZBitOps.
Require Import riscv.util.BitWidths.
Require Import riscv.Run.
Require Import riscv.Program.
Require Import riscv.AxiomaticRiscv.
Require Import compiler.Tactics.
Require Import riscv.util.Tactics.
Require Import compiler.FlatImp.
Require Import compiler.FlatToRiscv.


Local Open Scope Z_scope.

Set Implicit Arguments.

Lemma nth_error_single_Some: forall A (a1 a2: A) i,
    nth_error (a1 :: nil) i = Some a2 ->
    i = O /\ a1 = a2.
Proof.
  intros. destruct i; inversion H; auto. simpl in *.
  exfalso. eapply nth_error_nil_Some. eassumption.
Qed.

Lemma nth_error_cons_Some: forall A (a1 a2: A) (l: list A) i,
    nth_error (a1 :: l) i = Some a2 ->
    i = O /\ a1 = a2 \/ exists j, i = S j /\ nth_error l j = Some a2.
Proof.
  intros. destruct i; simpl in *.
  - inversions H. auto.
  - eauto.
Qed.

Lemma nth_error_app_Some: forall A (a: A) (l1 l2: list A) i,
    nth_error (l1 ++ l2) i = Some a ->
    nth_error l1 i = Some a \/ nth_error l2 (i - length l1) = Some a.
Proof.
  intros.
  assert (i < length l1 \/ length l1 <= i)%nat as C by omega.
  destruct C as [C | C].
  - left. rewrite nth_error_app1 in H; assumption.
  - right. rewrite nth_error_app2 in H; assumption.
Qed.

Hint Unfold
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

Hint Unfold
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
  apply Z.pow_pos_nonneg; omega.
Qed.

Lemma times4mod2: forall (a: Z),
    (a * 4) mod 2 = 0.
Proof.
  intros. change 4 with (2 * 2). rewrite Z.mul_assoc.
  apply Z.mod_mul. congruence.
Qed.

Section EmitsValid.

  Context {Bw: BitWidths}.

  Lemma compile_lit_emits_valid: forall r w i inst,
      nth_error (compile_lit r w) i = Some inst ->
      valid_register r ->
      verify inst RV_wXLEN_IM.
  Proof.
    intros.
    unfold compile_lit, compile_lit_rec, RV_wXLEN_IM in *.
    simpl in *.
    repeat match goal with
    | H: nth_error (_ :: _) ?i = Some _ |- _ => destruct i; simpl in *
    | H: nth_error nil _ = Some _ |- _ => exfalso; eapply nth_error_nil_Some; exact H
    end;
    destruct bitwidth; inversions H; unfold verify; simpl;
      autounfold with unf_verify unf_encode_consts;
      unfold Register0;
      repeat match goal with
      | |- context [ bitSlice ?w ?start ?eend ] =>
        unique pose proof (@bitSlice_bounds w start eend)
      end;
      simpl_pow2;
      unfold valid_register in *;
      intuition (try omega).
  Qed.

  Lemma compile_op_emits_valid: forall x op y z i inst,
      nth_error (compile_op x op y z) i = Some inst ->
      valid_register x ->
      valid_register y ->
      valid_register z ->
      verify inst RV_wXLEN_IM.
  Proof.
    intros.
    unfold RV_wXLEN_IM in *.
    destruct op; simpl in *;
      repeat match goal with
             | H: nth_error (_ :: _) ?i = Some _ |- _ => destruct i; simpl in *
             | H: nth_error nil _ = Some _ |- _ => exfalso; eapply nth_error_nil_Some; exact H
             end;
      destruct bitwidth; inversions H; unfold verify; simpl;
      autounfold with unf_verify unf_encode_consts;
      unfold Register0;
      repeat match goal with
      | |- context [ bitSlice ?w ?start ?eend ] =>
        unique pose proof (@bitSlice_bounds w start eend)
      end;
      simpl_pow2;
      unfold valid_register in *;
      intuition (try omega).
  Qed.

  Arguments Z.of_nat: simpl never.
  Arguments Z.mul: simpl never.
  Arguments Z.pow: simpl never.
  
  Lemma compile_stmt_emits_valid: forall s i inst,
      nth_error (compile_stmt s) i = Some inst ->
      valid_registers s ->
      stmt_not_too_big s ->
      verify inst RV_wXLEN_IM.
  Proof.
    induction s; intros; simpl in *;
    repeat  match goal with
      | H: nth_error nil _ = Some _ |- _ =>
             exfalso; eapply nth_error_nil_Some; exact H
      | H: nth_error (_ :: nil) _ = Some _ |- _ =>
             apply nth_error_single_Some in H
      | H: nth_error (_ :: _) _ = Some _ |- _ =>
             apply nth_error_cons_Some in H; destruct H as [ [? ?] | [? [? ?] ] ]
      | H: nth_error (_ ++ _) _ = Some _ |- _ =>
             apply nth_error_app_Some in H; destruct H as [? | ?]
      | H: nth_error (compile_lit _ _) _ = Some _ |- _ => 
             apply compile_lit_emits_valid in H; [ | intuition fail ]
      | H: nth_error (compile_op _ _ _ _) _ = Some _ |- _ =>
             apply compile_op_emits_valid in H; [ | intuition fail .. ]
      end;
      unfold verify, valid_register in *;
      (intuition subst);
      unfold Register0, stmt_not_too_big, RV_wXLEN_IM, LwXLEN, SwXLEN, bitwidth in *;
      destruct Bw; simpl in *;
      autounfold with unf_encode_consts unf_verify;
      repeat (so fun hyporgoal => match hyporgoal with
              | context [(2 ^ ?a)%Z] => 
                  let r := eval cbv in (2 ^ a)%Z in change (2 ^ a)%Z with r in *
              end);
      repeat match goal with
             | s: stmt |- _ => unique pose proof (compile_stmt_size s)
             end;
      repeat match goal with
      | IH: forall (i: nat) (inst: Instruction), _ |- _ =>
            edestruct IH as [? ?]; [ eassumption | assumption | lia | clear IH ]
      end;
      (intuition (first [apply times4mod2 | omega | nia | idtac])).
  Qed.

End EmitsValid.

