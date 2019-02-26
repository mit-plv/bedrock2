Require Import Coq.Lists.List. Import ListNotations.
Require Import Coq.micromega.Lia.
Require Import Coq.ZArith.ZArith.
Require Import riscv.Decode.
Require Import riscv.Encode.
Require Import riscv.util.ZBitOps.
Require Import riscv.Run.
Require Import riscv.Program.
Require Import riscv.Primitives.
Require Import compiler.util.Tactics.
Require Import riscv.util.Tactics.
Require Import compiler.FlatImp.
Require Import compiler.FlatToRiscvDef. Import FlatToRiscvDef.
Require Import riscv.util.ListLib.
Require Import riscv.Memory.

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


Section EmitsValid.

  Context (iset: InstructionSet).

  Context {compilation_params: FlatToRiscvDef.parameters}.

  Lemma compile_lit_emits_valid: forall r w,
      valid_register r ->
      valid_instructions iset (compile_lit r w).
  Proof.
    unfold valid_instructions.
    intros.
    unfold compile_lit, compile_lit_rec in *.
    simpl in *.
    repeat destruct H0 as [? | H0];
        try contradiction;
        subst instr;
        destruct bitwidth; inversions H; unfold verify; simpl;
        autounfold with unf_verify unf_encode_consts;
        unfold Register0;
        repeat match goal with
               | |- context [ bitSlice ?w ?start ?eend ] =>
                 unique pose proof (@bitSlice_bounds w start eend)
               end;
        simpl_pow2;
        intuition try lia;
        destruct iset;
        try lia.
  Qed.

  Lemma compile_op_emits_valid: forall x op y z,
      supportsM iset = true ->
      valid_register x ->
      valid_register y ->
      valid_register z ->
      valid_instructions iset (compile_op x op y z).
  Proof.
    unfold valid_instructions.
    intros.
    destruct op; simpl in *; (repeat destruct H3; try contradiction);
          inversions H; unfold verify; simpl;
          unfold supportsM in *;
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

  Lemma compile_bcond_by_inverting_emits_valid: forall cond amt,
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

  Lemma compile_load_emits_valid: forall x y sz,
      valid_register x ->
      valid_register y ->
      valid_instructions iset [compile_load iset sz x y 0].
  Proof.
    intros.
    destruct sz; destruct iset eqn: E; unfold valid_instructions, valid_register in *; simpl;
      intros;
      (destruct H1; [|contradiction]);
      subst instr;
      unfold verify;
      simpl;
      autounfold with unf_encode_consts unf_verify;
      unfold Register0 in *;
      intuition (try lia).
  Qed.

  Lemma compile_store_emits_valid: forall x y sz,
      valid_register x ->
      valid_register y ->
      valid_instructions iset [compile_store iset sz x y 0].
  Proof.
    intros.
    destruct sz; destruct iset eqn: E; unfold valid_instructions, valid_register in *; simpl;
      intros;
      (destruct H1; [|contradiction]);
      subst instr;
      unfold verify;
      simpl;
      autounfold with unf_encode_consts unf_verify;
      unfold Register0 in *;
      intuition (try lia).
  Qed.

  Arguments Z.of_nat: simpl never.
  Arguments Z.mul: simpl never.
  Arguments Z.pow: simpl never.
  Arguments Z.add: simpl never.

  Hint Rewrite @Zlength_nil @Zlength_cons @Zlength_app: rew_Zlength.

  Lemma compile_stmt_size: forall s,
    0 <= Zlength (compile_stmt iset s) <= stmt_size s.
  Proof.
    induction s; simpl; try destruct op; try solve [destruct f]; simpl;
    repeat (autorewrite with rew_Zlength || simpl in * || unfold compile_lit); try lia.
    pose proof (Zlength_nonneg (compile_ext_call binds a args)).
    pose proof (compile_ext_call_length binds a args).
    lia.
  Qed.

  Lemma compile_stmt_emits_valid: forall s,
      supportsM iset = true ->
      valid_registers s ->
      stmt_not_too_big s ->
      valid_instructions iset (compile_stmt iset s).
  Proof.
    induction s; intros; simpl in *; intuition (
      auto using compile_load_emits_valid,
                 compile_store_emits_valid,
                 compile_lit_emits_valid,
                 compile_op_emits_valid,
                 compile_ext_call_emits_valid
    );
    unfold valid_instructions, valid_register, Register0, stmt_not_too_big in *;
    intros; simpl in *;
    repeat match goal with
           | H: _ \/ _ |- _ => destruct H
           | H: In _ (_ ++ _) |- _ => apply in_app_iff in H
           | H: In _ (_ :: _) |- _ => apply in_inv in H
           | s: stmt |- _ => unique pose proof (stmt_size_pos s)
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
