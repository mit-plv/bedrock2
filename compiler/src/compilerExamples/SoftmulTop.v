Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Bitwidth32.
Require Import coqutil.Map.Interface coqutil.Map.OfFunc.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Utility.runsToNonDet.
Require riscv.Utility.InstructionNotations.
Require bedrock2.Hexdump.
Require riscv.Spec.PseudoInstructions.
Require Import compiler.SeparationLogic.
Require Import bedrock2.ZnWords.
Require Import riscv.Utility.Encode.
Require Import riscv.Platform.MaterializeRiscvProgram.
Require Import compiler.regs_initialized.
Require Import bedrock2.BasicC32Semantics.
Require Import riscv.Platform.MinimalCSRs.
Require Import coqutil.Map.Z_keyed_SortedListMap.
Require Import compilerExamples.SoftmulBedrock2.
Require Import compilerExamples.SoftmulCompile.
Require Import compilerExamples.Softmul.
Require Import compiler.LowerPipeline.
Require Import bedrock2.SepAutoArray bedrock2.SepAutoExports.
Require Import bedrock2.SepBulletPoints.
Local Open Scope sep_bullets_scope. Undelimit Scope sep_scope.

Definition softmul_binary: list byte := Pipeline.instrencode handler_insts.

Module PrintAssembly.
  Import riscv.Utility.InstructionNotations.
  Goal True. let r := eval cbv in handler_insts in idtac (* r *). Abort.
End PrintAssembly.

Module PrintBytes.
  Import bedrock2.Hexdump.
  Local Open Scope hexdump_scope.
  Set Printing Width 100.
  Goal True. let r := eval cbv in softmul_binary in idtac (* r *). Abort.
End PrintBytes.

Notation Registers := (Zkeyed_map BasicC32Semantics.word).
Notation Mem := BasicC32Semantics.mem.
Notation MachineState := (@State 32 BasicC32Semantics.word Mem Registers).
Notation word := BasicC32Semantics.word.

Definition R(r1 r2: MachineState): Prop :=
  r1.(regs) = r2.(regs) /\
  r1.(pc) = r2.(pc) /\
  r1.(nextPc) = r2.(nextPc) /\
  r1.(csrs) = map.empty /\
  basic_CSRFields_supported r2 /\
  regs_initialized r2.(regs) /\
  exists mtvec_base scratch_end,
    map.get r2.(csrs) CSRField.MTVecBase = Some mtvec_base /\
    map.get r2.(csrs) CSRField.MScratch = Some scratch_end /\
    <{ * eq r1.(mem)
       * mem_available (word.of_Z (scratch_end - 256)) (word.of_Z scratch_end)
       * ptsto_bytes (word.of_Z (mtvec_base * 4)) softmul_binary }> r2.(mem).

Lemma bytearray_to_instr_array: forall insts addr,
    Forall (fun i => verify i Decode.RV32I) insts ->
    iff1 (array ptsto (word.of_Z 1) addr (Pipeline.instrencode insts))
         (array (instr idecode) (word.of_Z 4) addr insts).
Proof.
  intros. revert addr. induction H; intros.
  - cbn. reflexivity.
  - rewrite array_cons.
    unfold Pipeline.instrencode in *. cbn [flat_map]. rewrite array_app.
    rewrite IHForall. clear IHForall.
    rewrite LittleEndian.to_list_split.
    rewrite LittleEndianList.length_le_split.
    repeat word_simpl_step_in_goal.
    cancel.
    cbn [seps].
    unfold instr, idecode, truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes.
    setoid_rewrite HList.tuple.to_list_of_list.
    unfold iff1, ex1. intro m. split; intro A.
    + exists (encode x).
      extract_ex1_and_emp_in_goal. split; [|split].
      * exact A.
      * eapply DecodeEncode.decode_encode. assumption.
      * apply EncodeBound.encode_range.
    + fwd. extract_ex1_and_emp_in A. fwd.
      rewrite EncodeDecode.encode_decode; auto.
Qed.

Lemma verify_handler_insts : Forall (fun i => verify i Decode.RV32I) handler_insts.
Proof.
  repeat (eapply Forall_cons || eapply Forall_nil).
  all : cbv; ssplit; trivial; try congruence.
Qed.

Definition bytes_to_word(bs: list byte): word :=
  word.of_Z (LittleEndianList.le_combine bs).

(* TODO generalize over bitwidth and add to library *)
Definition byte_list_to_word_list(bs: list byte): list word :=
  List.map bytes_to_word (List.chunk 4 bs).

Lemma length_byte_list_to_word_list_divisible: forall bs n,
    List.length bs = (n * 4)%nat ->
    List.length (byte_list_to_word_list bs) = n.
Admitted.

Definition word_to_bytes(w: word): list byte :=
  LittleEndianList.le_split 4 (word.unsigned w).

(* TODO generalize over bitwidth and add to library *)
Definition word_list_to_byte_list(ws: list word): list byte :=
  List.flat_map word_to_bytes ws.

Lemma word_list_to_byte_list_length: forall ws,
    List.length (word_list_to_byte_list ws) = (List.length ws * 4)%nat.
Admitted.

Lemma split_le_combine_grow: forall bs n,
    (Datatypes.length bs <= n)%nat ->
    LittleEndianList.le_split n (LittleEndianList.le_combine bs) =
      bs ++ List.repeat Byte.x00 (n - List.length bs)%nat.
Proof.
  intros.
  assert (bs = [Byte.x12; Byte.x23; Byte.x24]) by admit.
  assert (n = 5%nat) by admit.
  subst.
  cbv.
  reflexivity.
Admitted.

Lemma bytes_to_word_roundtrip: forall bs,
    (List.length bs <= 4)%nat ->
    word_to_bytes (bytes_to_word bs) = bs ++ List.repeat Byte.x00 (4 - List.length bs)%nat.
Proof.
  unfold word_to_bytes, bytes_to_word. intros.
  rewrite word.unsigned_of_Z_nowrap.
  1: eapply split_le_combine_grow. 1: assumption.
  pose proof (LittleEndianList.le_combine_bound bs) as P.
Admitted.

Lemma byte_list_to_word_list_roundtrip_aux: forall n bs,
    (List.length bs <= n)%nat ->
    word_list_to_byte_list (byte_list_to_word_list bs) =
      bs ++ List.repeat Byte.x00 ((List.length bs + 3)/4*4 - List.length bs)%nat.
Proof.
  induction n; intros.
  - destruct bs. 1: reflexivity. inversion H.
  - destruct bs. 1: reflexivity. cbn in H.
    rename b into b0.
    destruct bs as [|b1 bs]. {
      cbn. rewrite List.app_nil_r. unfold bytes_to_word, LittleEndianList.le_combine.
      rewrite Z.shiftl_0_l. rewrite Z.lor_0_r.
Admitted.

Lemma byte_list_to_word_list_roundtrip: forall bs,
    Z.of_nat (List.length bs) mod 4 = 0 ->
    word_list_to_byte_list (byte_list_to_word_list bs) = bs.
Proof.
  intros.
  rewrite byte_list_to_word_list_roundtrip_aux with (n := List.length bs) by reflexivity.
Admitted.

Lemma word_array_to_byte_array: forall addr (bs: list byte) (ws: list word),
    word_list_to_byte_list ws = bs ->
    iff1 (array scalar (word.of_Z 4) addr ws) (array ptsto (word.of_Z 1) addr bs).
Proof.
  intros. subst. revert addr. induction ws; intros.
  - cbn. reflexivity.
  - rewrite array_cons.
    unfold word_list_to_byte_list in *. cbn [flat_map]. rewrite array_app.
    rewrite IHws. clear IHws.
    unfold word_to_bytes at 3.
    rewrite LittleEndianList.length_le_split.
    repeat word_simpl_step_in_goal.
    cancel.
    cbn [seps].
    unfold scalar, truncated_word, truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes.
    rewrite HList.tuple.to_list_of_list.
    unfold word_to_bytes. reflexivity.
Qed.

Lemma split_sepclause_convert: forall (all part part': Mem -> Prop) frame (C: Prop),
    iff1 part' part ->
    split_sepclause all part' frame C ->
    split_sepclause all part frame C.
Proof.
  unfold split_sepclause. intros. rewrite <- H. assumption.
Qed.

Axiom TODO_bytelist_length: forall bs n,
    Datatypes.length bs = (n * 4)%nat ->
    (Datatypes.length bs = (n * 4)%nat) =
    (Datatypes.length (byte_list_to_word_list bs) = n).

Lemma R_equiv_related: forall r1 r2,
    R r1 r2 <-> related r1 r2.
Proof.
  unfold R, related, mem_available. split; intros; fwd; intuition try congruence.
  - extract_ex1_and_emp_in_hyps.
    unfold ptsto_bytes, softmul_binary in *.
    do 3 eexists.
    split; [eassumption|].
    split; [eassumption|].
    apply and_comm.
    flatten_seps_in_goal.
    extract_ex1_and_emp_in_goal.
    rename Hp6p2 into M.
    rewrite (iff1ToEq (bytearray_to_instr_array _ (word.of_Z (mtvec_base * 4))
                         verify_handler_insts)) in M.
    scancel_asm.
    split_ith_left_and_cancel_with_fst_right 0%nat.
    1: eapply split_sepclause_convert.
    1: symmetry.
    1: eapply word_array_to_byte_array.
    1: eapply byte_list_to_word_list_roundtrip.
    all: cycle 1.
    1: lazymatch goal with
       | |- context [List.length (byte_list_to_word_list ?B) = 32%nat] =>
           replace (List.length (byte_list_to_word_list B) = 32%nat) with
           (List.length B = 128%nat)
       end.
    2: eapply TODO_bytelist_length with (n := 32%nat).
    1: unshelve (eauto with split_sepclause_goal).
    1: rename H into Sp.
    1: split.
    1: eapply Sp.
    1: solve [solve_split_sepclause_sidecond_or_pose_err].
    1: clear Sp. (* because there's no "after the call" where we want to merge *)
    1: repeat word_simpl_step_in_goal.
    1: rewrite (@List.skipn_all2 _ 256%nat) by listZnWords.
    1: impl_ecancel_step_without_splitting.
    1: impl_ecancel_step_without_splitting.
    1: unfold array.
    1: ssplit.
    1: reflexivity.
    1: listZnWords.
    1: listZnWords.
    1: listZnWords.
    1: listZnWords.
  - extract_ex1_and_emp_in_hyps.
    unfold ptsto_bytes, softmul_binary in *.
    do 2 eexists.
    split; [eassumption|].
    split; [eassumption|].
    flatten_seps_in_goal.
    extract_ex1_and_emp_in_goal.
    rewrite (iff1ToEq (bytearray_to_instr_array _ (word.of_Z (mtvec_base * 4))
                         verify_handler_insts)).
    (* somewhat unusual: hyp is split, goal is more merged *)
    rename Hp6p3 into M.
    seprewrite_in (word_array_to_byte_array (word.of_Z (stack_hi - 128))) M.
    1: reflexivity.
    rewrite (array_app
               anybytes
               (word_list_to_byte_list stacktrash)
               (word.of_Z (stack_hi - 256))).
    flatten_seps_in_goal. cbn [seps].
    rewrite Hp6p3_emp0.
    repeat word_simpl_step_in_goal.
    repeat word_simpl_step_in_hyps.
    (* TODO why doesn't word_simpl canonicalize this? *)
    replace (word.sub (word.of_Z stack_hi) (word.of_Z 256))
      with (word.of_Z (word := word) (stack_hi - 256)) by ring.
    replace (word.sub (word.of_Z stack_hi) (word.of_Z 128))
      with (word.of_Z (word := word) (stack_hi - 128)) by ring.
    replace (word.mul (word.of_Z 4) (word.of_Z mtvec_base))
      with (word.of_Z (word := word) (mtvec_base * 4)) by ring.
    scancel_asm.
    pose proof (word_list_to_byte_list_length stacktrash).
    listZnWords.
Qed.

Lemma softmul_correct: forall initialH initialL post,
    runsTo (mcomp_sat (run1 mdecode)) initialH post ->
    R initialH initialL ->
    runsTo (mcomp_sat (run1 idecode)) initialL (fun finalL =>
               exists finalH, R finalH finalL /\ post finalH).
Proof.
  intros.
  eapply R_equiv_related in H0.
  eapply runsTo_weaken.
  1: eapply Softmul.softmul_correct. 1,2: eassumption.
  cbv beta. intros.
  fwd. eapply R_equiv_related in H1p0. eauto.
Qed.

(*
Print Assumptions softmul_correct.
only word list to byte list stuff
*)
