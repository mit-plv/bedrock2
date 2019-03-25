Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import coqutil.Decidable.
Require Import riscv.Spec.Decode.
Require Import riscv.Utility.Encode.
Require Import riscv.Utility.ZBitOps.
Require Import riscv.Platform.Run.
Require Import riscv.Spec.Machine.
Require Import riscv.Spec.Primitives.
Require Import compiler.util.Tactics.
Require Import riscv.Utility.Tactics.
Require Import compiler.FlatImp.
Require Import compiler.FlatToRiscvDef. Import FlatToRiscvDef.
Require Import riscv.Utility.ListLib.
Require Import riscv.Platform.Memory.

Local Open Scope Z_scope.

Set Implicit Arguments.

Lemma nth_error_nil_Some: forall {A} i (a: A), nth_error nil i = Some a -> False.
Proof.
  intros. destruct i; simpl in *; discriminate.
Qed.

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


Tactic Notation "so" tactic(f) :=
  match goal with
  | _: ?A |- _  => f A
  |       |- ?A => f A
  end.

Ltac unify_universes_for_lia :=
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
Ltac lia' := unify_universes_for_lia; lia.

Inductive supported_iset: InstructionSet -> Prop :=
| supported_RV32IM: supported_iset RV32IM
| supported_RV64IM: supported_iset RV64IM.

Section EmitsValid.

  Context {compilation_params: FlatToRiscvDef.parameters}.

  Arguments Z.of_nat: simpl never.
  Arguments Z.mul: simpl never.
  Arguments Z.pow: simpl never.
  Arguments Z.add: simpl never.

  Lemma compile_lit_small_emits_valid: forall r iset w,
      -2^11 <= w < 2^11 ->
      valid_register r ->
      valid_instructions iset (compile_lit_12bit r w).
  Proof.
    intros. unfold compile_lit_12bit, valid_instructions.
    intros. simpl in *. destruct H1; [subst|contradiction].
    split; [|exact I]. simpl.
    autounfold with unf_verify unf_encode_consts.
    unfold Register0, valid_register in *.
    simpl_pow2.
    lia.
  Qed.

  Lemma swrap_range: forall z w,
      0 < w ->
      -2^(w-1) <= swrap w z < 2^(w-1).
  Proof.
    intros. unfold swrap.
    pose proof (Z.mod_pos_bound (z + 2 ^ (w - 1)) (2 ^ w)).
    pose proof (Z.pow_pos_nonneg 2 w).
    assert (2 ^ (w - 1) * 2 = 2 ^ w). {
      replace w with (w - 1 + 1) at 2 by lia.
      rewrite Z.pow_add_r; try reflexivity; lia.
    }
    lia.
  Qed.

  Lemma signExtend_range: forall i z,
      0 < i ->
      0 <= z < 2^i ->
      -2^(i-1) <= signExtend i z < 2^(i-1).
  Proof.
    intros. unfold signExtend.
    assert (0 < 2 ^ (i - 1)). {
      apply Z.pow_pos_nonneg; lia.
    }
    destruct (Z.testbit z (i - 1)) eqn: E.
    - apply Z.testbit_true in E; [|lia].
      rewrite Z.mod_eq in E by lia.
      rewrite Z.div_div in E by lia.
      replace (2 ^ (i - 1) * 2) with (2 ^ i) in E; cycle 1. {
        replace i with (i - 1 + 1) at 1 by lia.
        rewrite Z.pow_add_r; try reflexivity; lia.
      }
      replace (z / 2 ^ i) with 0 in E; cycle 1. {
        symmetry. apply Z.div_small. lia.
      }
      assert (z / 2 ^ (i - 1) = 1) as E' by lia. clear E. rename E' into E.
      assert (~ z < 2 ^ (i - 1)). {
        intro C.
        pose proof (Z.div_small z (2 ^ (i - 1))) as D.
        lia.
      }
      replace (Z.setbit 0 i) with (2 ^ i); cycle 1. {
        rewrite Z.setbit_spec'.
        rewrite Z.lor_0_l.
        reflexivity.
      }
      replace (2 ^ i) with (2 ^ (i - 1) * 2) in *; cycle 1. {
        replace i with (i - 1 + 1) at 2 by lia.
        rewrite Z.pow_add_r; try reflexivity; lia.
      }
      lia.
    - apply Z.testbit_false in E; [|lia].
      rewrite Z.mod_eq in E by lia.
      rewrite Z.div_div in E by lia.
      replace (2 ^ (i - 1) * 2) with (2 ^ i) in E; cycle 1. {
        replace i with (i - 1 + 1) at 1 by lia.
        rewrite Z.pow_add_r; try reflexivity; lia.
      }
      replace (z / 2 ^ i) with 0 in E; cycle 1. {
        symmetry. apply Z.div_small. lia.
      }
      assert (z / 2 ^ (i - 1) = 0) as E' by lia. clear E. rename E' into E.
      assert (z < 2 ^ (i - 1)). {
        epose proof (Z.div_small_iff _ _ _) as P. destruct P as [P _].
        specialize (P E).
        lia.
      }
      lia.
      Unshelve.
      lia.
  Qed.

  Lemma remove_lobits: forall v i,
      0 <= i ->
      (v - bitSlice v 0 i) mod 2 ^ i = 0.
  Proof.
    intros.
    rewrite bitSlice_alt by lia. unfold bitSlice'.
    rewrite Z.sub_0_r.
    change (2 ^ 0) with 1.
    rewrite Z.div_1_r.
    rewrite Zminus_mod_idemp_r.
    rewrite Z.sub_diag.
    apply Zmod_0_l.
  Qed.

  Lemma compile_lit_32bit_emits_valid: forall r v iset,
      -2^31 <= v < 2^31 ->
      valid_register r ->
      valid_instructions iset (compile_lit_32bit r v).
  Proof. Admitted. (*
    intros. unfold compile_lit_32bit, valid_instructions.
    intros. simpl in *.
    pose proof (@swrap_range (v - signExtend 12 (bitSlice v 0 12)) 32 eq_refl) as P1.
    pose proof (bitSlice_range 12 v) as P2.
    pose proof (@signExtend_range 12 (bitSlice v 0 12) eq_refl) as P3.
    assert (swrap 32 (v - signExtend 12 (bitSlice v 0 12)) mod (2 ^ 12) = 0) as P4. {
      unfold swrap.
      simpl.
      rewrite Zminus_mod.
      rewrite <- Znumtheory.Zmod_div_mod; try reflexivity; cycle 1. {
        unfold Z.divide. exists (2 ^ 20). reflexivity.
      }
      rewrite (Znumtheory.Zdivide_mod (2 ^ 31) (2 ^ 12)); cycle 1. {
        unfold Z.divide. exists (2 ^ 19). reflexivity.
      }
      rewrite Z.sub_0_r.
      rewrite Z.mod_mod by lia.
      rewrite Zplus_mod.
      rewrite (Znumtheory.Zdivide_mod (2 ^ 31) (2 ^ 12)); cycle 1. {
        unfold Z.divide. exists (2 ^ 19). reflexivity.
      }
      rewrite Z.add_0_r.
      rewrite Z.mod_mod by lia.
      rewrite signExtend_alt by reflexivity.
      unfold signExtend'.
      rewrite Zminus_mod.
      rewrite (Zminus_mod (bitSlice v 0 12) ((bitSlice v 0 12 / 2 ^ (12 - 1)) mod 2 * 2 ^ 12)).
      rewrite Z_mod_mult.
      rewrite Z.sub_0_r.
      rewrite Z.mod_mod by lia.
      rewrite <- Zminus_mod.
      rewrite bitSlice_alt by lia.
      unfold bitSlice'. simpl.
      change (2 ^ 0) with 1.
      rewrite Z.div_1_r.
      rewrite Zminus_mod_idemp_r.
      rewrite Z.sub_diag.
      reflexivity.
    }
    destruct H1 as [ ? | [? | ?] ]; [subst..|contradiction];
      (split; [|exact I]); simpl;
        autounfold with unf_verify unf_encode_consts;
        unfold Register0, valid_register in *;
        simpl_pow2;
        omega. (* TODO PARAMRECORDS? lia doesn't work *)
  Qed. *)

  Lemma valid_Slli: forall rd rs shamt iset,
      0 <= shamt < 32 ->
      valid_register rd ->
      valid_register rs ->
      verify (IInstruction (Slli rd rs shamt)) iset.
  Proof.
    intros.
    unfold verify, valid_register in *;
    simpl;
    autounfold with unf_encode_consts unf_verify;
    unfold Register0 in *;
    destruct iset;
    lia.
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
        apply Z.pow_nonzero; lia.
      }
      pose proof (Z.mod_bound_or (w / 2 ^ i) (2 ^ (j - i)) A) as P.
      assert (0 < 2 ^ 11) by reflexivity.
      assert (0 < 2 ^ (j - i)). {
        apply Z.pow_pos_nonneg; lia.
      }
      assert (2 ^ (j - i) <= 2 ^ 11) as B. {
        apply Z.pow_le_mono_r; lia.
      }
      lia.
    }
    unfold verify, valid_register in *;
    simpl;
    autounfold with unf_encode_consts unf_verify;
    unfold Register0 in *;
    destruct iset;
    lia.
  Qed.

  Lemma compile_lit_64bit_emits_valid: forall r w iset,
      0 <= w < 2^64 ->
      valid_register r ->
      valid_instructions iset (compile_lit_64bit r w).
  Proof.
    intros. unfold compile_lit_64bit, valid_instructions.
    intros. apply in_app_or in H1. destruct H1. {
      eapply compile_lit_32bit_emits_valid; try eassumption.
      change 31 with (32 - 1).
      eapply signExtend_range; [reflexivity|].
      change 32 with (64 - 32) at 3.
      apply bitSlice_bounds.
      lia.
    }
    simpl in *.
    repeat destruct H1 as [H1 | H1]; [subst instr..|contradiction];
      (eapply valid_Addi_bitSlice || eapply valid_Slli); try eassumption; try lia.
  Qed.

  Lemma compile_lit_large_emits_valid: forall r w iset,
      valid_register r ->
      valid_instructions iset (compile_lit_large r w).
  Proof.
    unfold compile_lit_large; intros.
    destruct_one_match.
    - eapply compile_lit_32bit_emits_valid; try eassumption.
      change 31 with (32 - 1). (*
      apply swrap_range.
      reflexivity.
    - eapply compile_lit_64bit_emits_valid; try eassumption.
      apply Z.mod_pos_bound. reflexivity.
  Qed.*) Admitted.

  Global Arguments compile_lit_large_emits_valid : clear implicits.

  Lemma compile_lit_new_emits_valid: forall r w iset,
      valid_register r ->
      valid_instructions iset (compile_lit_new r w).
  Proof.
    intros.
    unfold compile_lit_new in *.
    destruct_one_match;
    eauto using compile_lit_small_emits_valid, compile_lit_large_emits_valid.
  Qed.

  Lemma compile_op_emits_valid: forall iset x op y z,
      supported_iset iset ->
      valid_register x ->
      valid_register y ->
      valid_register z ->
      valid_instructions iset (compile_op x op y z).
  Proof.
    unfold valid_instructions.
    intros.
    destruct op; simpl in *; (repeat destruct H3; try contradiction);
          inversions H; unfold verify; simpl;
          autounfold with unf_verify unf_encode_consts;
          unfold Register0;
          repeat match goal with
                 | |- context [ bitSlice ?w ?start ?eend ] =>
                   unique pose proof (@bitSlice_bounds w start eend)
                 end;
          simpl_pow2;
          unfold valid_register in *;
          try solve [constructor];
          try lia;
          try (split; [lia|auto]);
          destruct iset; auto; try discriminate.
  Qed.

  Lemma compile_bcond_by_inverting_emits_valid: forall iset cond amt,
      valid_registers_bcond cond ->
      - 2 ^ 12 <= amt < 2 ^ 12 ->
      amt mod 2 = 0 ->
      verify (compile_bcond_by_inverting cond amt) iset.
  Proof.
    unfold valid_registers_bcond, valid_register.
    intros.
    simpl in *.
    destruct cond; [destruct op|]; simpl;
    unfold verify;
    destruct bitwidth;
    simpl;
    autounfold with unf_encode_consts unf_verify;
    unfold Register0 in *;
    intuition lia.
  Qed.

  Definition iset := if Utility.width =? 32 then RV32IM else RV64IM.

  Lemma compile_load_emits_valid: forall x y sz,
      valid_register x ->
      valid_register y ->
      valid_instructions iset [compile_load sz x y 0].
  Proof.
    intros. unfold iset.
    destruct Utility.width_cases as [E | E]; rewrite E; simpl;
    destruct sz eqn: Eqsz; unfold valid_instructions, valid_register in *; simpl;
      intros;
      (destruct H1; [|contradiction]);
      subst instr;
      unfold verify;
      simpl;
      rewrite? E; simpl;
      autounfold with unf_encode_consts unf_verify;
      unfold Register0 in *;
      rewrite? E; simpl;
      intuition (try lia).
  Qed.

  Lemma compile_store_emits_valid: forall x y sz,
      valid_register x ->
      valid_register y ->
      valid_instructions iset [compile_store sz x y 0].
  Proof.
    intros. unfold iset.
    destruct Utility.width_cases as [E | E]; rewrite E; simpl;
    destruct sz; inversions H; unfold valid_instructions, valid_register in *; simpl;
      intros;
      (destruct H; [|contradiction]);
      subst instr;
      unfold verify;
      simpl;
      rewrite? E;
      simpl;
      autounfold with unf_encode_consts unf_verify;
      unfold Register0 in *;
      intuition (try lia).
  Qed.

  Hint Rewrite @Zlength_nil @Zlength_cons @Zlength_app: rew_Zlength.

  Lemma compile_lit_new_size: forall x v,
      0 <= Zlength (compile_lit_new x v) <= 15.
  Admitted.

  Lemma compile_stmt_size: forall s,
    0 <= Zlength (compile_stmt s) <= stmt_size s.
  Proof.
    induction s; simpl; try apply compile_lit_new_size;
      try destruct op; try solve [destruct f]; simpl;
      repeat (autorewrite with rew_Zlength || simpl in *); try lia.
    pose proof (Zlength_nonneg (compile_ext_call binds a args)).
    pose proof (compile_ext_call_length binds a args).
    lia.
  Qed.

  Lemma compile_stmt_emits_valid: forall s,
      supported_iset iset ->
      valid_registers s ->
      stmt_not_too_big s ->
      valid_instructions iset (compile_stmt s).
  Proof.
    induction s; intros; simpl in *; intuition (
      auto using compile_load_emits_valid,
                 compile_store_emits_valid,
                 compile_lit_new_emits_valid,
                 compile_op_emits_valid,
                 compile_ext_call_emits_valid
    );
    unfold valid_instructions, valid_register, Register0, stmt_not_too_big in *;
    intros; simpl in *;
    repeat match goal with
           | H: _ \/ _ |- _ => destruct H
           | H: In _ (_ ++ _) |- _ => apply in_app_iff in H
           | H: In _ (_ :: _) |- _ => apply in_inv in H
           | s: stmt |- _ => unique pose proof (compile_stmt_size s)
           | H: context [Zlength ?l] |- _ => unique pose proof (Zlength_nonneg l)
           end;
    subst;
    repeat (so fun hyporgoal => match hyporgoal with
            | context [(2 ^ ?a)%Z] =>
              let r := eval cbv in (2 ^ a)%Z in change (2 ^ a)%Z with r in *
            end);
    try solve
        [ apply compile_bcond_by_inverting_emits_valid; [assumption | lia' | apply times4mod2 ]
        | match goal with
          | H: _ |- _ => solve [apply H; (lia || auto)]
          end
        | unfold verify in *;
          destruct iset;
          simpl in *; intros;
          intuition subst; simpl in *;
          autounfold with unf_encode_consts unf_verify;
          repeat match goal with
                 | |- context [(?x * 4) mod 2] => rewrite (times4mod2 x)
                 end;
          lia' ].
  Qed.

End EmitsValid.
