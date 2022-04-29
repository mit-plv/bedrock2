Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Bitwidth32.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.Memory.
Require Import riscv.Spec.CSRFile.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.RecordSetters.
Require Import coqutil.Decidable.
Require Import Coq.micromega.Lia.
Require Import coqutil.Map.Interface coqutil.Map.OfFunc.
Require Import coqutil.Map.MapEauto.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import coqutil.Tactics.rdelta.
Require Import compiler.DivisibleBy4.
Require Import riscv.Utility.runsToNonDet.
Require riscv.Spec.PseudoInstructions.
Require Import compiler.SeparationLogic.
Require Import coqutil.Tactics.Simp.
Require Import bedrock2.Syntax.
Require Import bedrock2.ZnWords.
Require Import riscv.Utility.Encode.
Require Import riscv.Proofs.EncodeBound.
Require Import riscv.Platform.MinimalCSRs.
Require Import riscv.Proofs.InstructionSetOrder.
Require Import riscv.Proofs.DecodeEncodeProver.
Require Import riscv.Proofs.DecodeEncode.
Require Import riscv.Proofs.DecodeByExtension.
Require riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MaterializeRiscvProgram.
Require Import compiler.regs_initialized.
Require Import compilerExamples.SoftmulBedrock2.
Require Import compilerExamples.SoftmulCompile.
Require Import bedrock2.SepAutoArray bedrock2.SepAutoExports.
Require Import bedrock2.SepBulletPoints.
Local Open Scope sep_bullets_scope. Undelimit Scope sep_scope.

Ltac assertZcst x :=
  let x' := rdelta x in lazymatch isZcst x' with true => idtac end.

Ltac compareZconsts :=
  lazymatch goal with
  | |- not (@eq Z ?x ?y) => assertZcst x; assertZcst y; discriminate 1
  | |- ?A /\ ?B => split; compareZconsts
  | |- ?x < ?y => assertZcst x; assertZcst y; reflexivity
  | |- ?x <= ?y => assertZcst x; assertZcst y; discriminate 1
  | |- @eq Z ?x ?y => assertZcst x; assertZcst y; reflexivity
  end.

Ltac cbn_MachineWidth := cbn [
  MkMachineWidth.MachineWidth_XLEN
  riscv.Utility.Utility.add
  riscv.Utility.Utility.sub
  riscv.Utility.Utility.mul
  riscv.Utility.Utility.div
  riscv.Utility.Utility.rem
  riscv.Utility.Utility.negate
  riscv.Utility.Utility.reg_eqb
  riscv.Utility.Utility.signed_less_than
  riscv.Utility.Utility.ltu
  riscv.Utility.Utility.xor
  riscv.Utility.Utility.or
  riscv.Utility.Utility.and
  riscv.Utility.Utility.XLEN
  riscv.Utility.Utility.regToInt8
  riscv.Utility.Utility.regToInt16
  riscv.Utility.Utility.regToInt32
  riscv.Utility.Utility.regToInt64
  riscv.Utility.Utility.uInt8ToReg
  riscv.Utility.Utility.uInt16ToReg
  riscv.Utility.Utility.uInt32ToReg
  riscv.Utility.Utility.uInt64ToReg
  riscv.Utility.Utility.int8ToReg
  riscv.Utility.Utility.int16ToReg
  riscv.Utility.Utility.int32ToReg
  riscv.Utility.Utility.int64ToReg
  riscv.Utility.Utility.s32
  riscv.Utility.Utility.u32
  riscv.Utility.Utility.regToZ_signed
  riscv.Utility.Utility.regToZ_unsigned
  riscv.Utility.Utility.sll
  riscv.Utility.Utility.srl
  riscv.Utility.Utility.sra
  riscv.Utility.Utility.divu
  riscv.Utility.Utility.remu
  riscv.Utility.Utility.maxSigned
  riscv.Utility.Utility.maxUnsigned
  riscv.Utility.Utility.minSigned
  riscv.Utility.Utility.regToShamt5
  riscv.Utility.Utility.regToShamt
  riscv.Utility.Utility.highBits
  riscv.Utility.Utility.ZToReg
].

#[export] Instance Instruction_inhabited: inhabited Instruction :=
  mk_inhabited (InvalidInstruction 0).

(* typeclasses eauto is for the word.ok sidecondition *)
#[export] Hint Rewrite @word.of_Z_unsigned using typeclasses eauto : fwd_rewrites.

Definition regs3to31: list Z := List.unfoldn (Z.add 1) 29 3.

Section WithRegisterNames.
  Import RegisterNames PseudoInstructions.
  Import InstructionCoercions. Open Scope ilist_scope.

  Definition save_regs3to31 :=
    @List.map Register Instruction (fun r => Sw sp r (4 * r)) regs3to31.
  Definition restore_regs3to31 :=
    @List.map Register Instruction (fun r => Lw r sp (4 * r)) regs3to31.

  (* TODO write encoder (so far there's only a decoder called CSR.lookupCSR) *)
  Definition MTVal    := 835.
  Remark MTVal_correct   : CSR.lookupCSR MTVal    = CSR.MTVal.    reflexivity. Qed.
  Definition MEPC     := 833.
  Remark MEPC_correct    : CSR.lookupCSR MEPC     = CSR.MEPC.     reflexivity. Qed.
  Definition MScratch := 832.
  Remark MScratch_correct: CSR.lookupCSR MScratch = CSR.MScratch. reflexivity. Qed.

  Definition handler_init := [[
    Csrrw sp sp MScratch;  (* swap sp and MScratch CSR *)
    Sw sp zero (-128);     (* save the 0 register (for uniformity) *)
    Sw sp ra (-124);       (* save ra *)
    Csrr ra MScratch;      (* use ra as a temporary register... *)
    Sw sp ra (-120);       (* ... to save the original sp *)
    Csrw sp MScratch;      (* restore the original value of MScratch *)
    Addi sp sp (-128)      (* remainder of code will be relative to updated sp *)
  ]].

  Definition inc_mepc := [[
    Csrr t1 MEPC;
    Addi t1 t1 4;
    Csrw t1 MEPC
  ]].

  Definition handler_final := [[
    Lw ra sp 4;
    Lw sp sp 8; (* Bug: used to be `Csrr sp MScratch`, which is wrong if Mul sets sp *)
    Mret
  ]].

  Definition call_mul := [[
    Csrr a0 MTVal;  (* argument 0: value of invalid instruction *)
    Addi a1 sp 0;   (* argument 1: pointer to memory with register values before trap *)
    Jal ra (Z.of_nat (1 + List.length inc_mepc + 29 + List.length handler_final) * 4)
  ]].

  Definition asm_handler_insts :=
    handler_init ++ save_regs3to31 ++ call_mul ++ inc_mepc ++
       restore_regs3to31 ++ handler_final.

  Definition handler_insts := asm_handler_insts ++ mul_insts.
End WithRegisterNames.

Section Riscv.
  Import bedrock2.BasicC32Semantics.
  Import Coq.Logic.FunctionalExtensionality.
  Local Notation Mem := mem (only parsing).
  Local Notation mem := MinimalCSRs.mem (only parsing).

  Context {registers: map.map Z word}.
  Context {registers_ok: map.ok registers}.

  (* RISC-V Monad *)
  Local Notation M := (free riscv_primitive primitive_result).

  Local Hint Mode map.map - - : typeclass_instances.

  Lemma ptsto_unique: forall (addr: word) (b: byte) (m1 m2: Mem),
      ptsto addr b m1 ->
      ptsto addr b m2 ->
      m1 = m2.
  Proof.
    intros. unfold ptsto in *. subst. reflexivity.
  Qed.

  Lemma array_unique{V: Type}(pred: word -> V -> Mem -> Prop)
      (pred_unique: forall addr v m1 m2, pred addr v m1 -> pred addr v m2 -> m1 = m2):
    forall sz vs addr m1 m2,
      array pred sz addr vs m1 ->
      array pred sz addr vs m2 ->
      m1 = m2.
  Proof.
    induction vs; intros.
    - cbn in *. unfold emp in *. fwd. reflexivity.
    - cbn in *.
      unfold sep, map.split in H, H0. fwd.
      f_equal.
      + eapply pred_unique; eassumption.
      + eapply IHvs; eassumption.
  Qed.

  Lemma truncated_scalar_unique: forall addr z m1 m2,
      truncated_scalar access_size.four addr z m1 ->
      truncated_scalar access_size.four addr z m2 ->
      m1 = m2.
  Proof.
    unfold truncated_scalar, littleendian, ptsto_bytes.
    intros.
    eapply array_unique.
    1: eapply ptsto_unique.
    all: eassumption.
  Qed.

  Lemma truncated_scalar_unique': forall [addr z m],
      (addr :-> z : truncated_scalar access_size.four) m ->
      eq m = (addr :-> z : truncated_scalar access_size.four).
  Proof.
    intros.
    extensionality m'. apply PropExtensionality.propositional_extensionality.
    split; intros.
    - subst. assumption.
    - eapply truncated_scalar_unique; eassumption.
  Qed.

  Notation program iset := (array (instr iset) (word.of_Z 4)).

  Lemma weaken_mcomp_sat: forall m initial (post1 post2: State -> Prop),
      (forall s, post1 s -> post2 s) ->
      mcomp_sat m initial post1 ->
      mcomp_sat m initial post2.
  Proof.
    unfold mcomp_sat. intros.
    eapply free.interpret_weaken_post with (postA1 := post1); eauto; simpl;
      eauto using weaken_run_primitive.
  Qed.

  Lemma mcomp_sat_bind: forall initial A (a: M A) (rest: A -> M unit) (post: State -> Prop),
      free.interpret run_primitive a initial (fun r mid => mcomp_sat (rest r) mid post) post ->
      mcomp_sat (Monads.Bind a rest) initial post.
  Proof.
    intros. unfold mcomp_sat. eapply free.interpret_bind. 2: exact H. apply weaken_run_primitive.
  Qed.

  Lemma invert_fetch0: forall initial post k,
      mcomp_sat (pc <- Machine.getPC; i <- Machine.loadWord Fetch pc; k i)
        initial post ->
      exists w, load_bytes 4 initial.(mem) initial.(pc) = Some w /\
                mcomp_sat (k w) initial post.
  Proof.
    intros. unfold mcomp_sat in *. cbn -[HList.tuple load_bytes] in H.
    unfold load in H.
    simp. eauto.
  Qed.

  Lemma split_of_list_word_at_cons: forall n addr b (bs: tuple byte n),
      Z.of_nat n < 2 ^ 32 ->
      map.split (map.of_list_word_at addr (b :: tuple.to_list bs))
        (map.put map.empty addr b)
        (map.of_list_word_at (word.add addr (word.of_Z 1)) (tuple.to_list bs)).
  Proof.
    unfold map.split. split.
    + eapply map.map_ext. intros.
      rewrite map.get_putmany_dec.
      rewrite 2map.get_of_list_word_at.
      rewrite map.get_put_dec.
      destr (word.eqb addr k).
      * ring_simplify (word.sub k k). rewrite word.unsigned_of_Z_0. cbn.
        replace (Z.to_nat (word.unsigned (word.sub k (word.add k (word.of_Z 1)))))
          with (Z.to_nat (2 ^ 32 - 1)) by ZnWords.
        pose proof (tuple.length_to_list bs) as L.
        assert (List.length (tuple.to_list bs) <= Z.to_nat (2 ^ 32 - 1))%nat as N by lia.
        eapply (proj2 (nth_error_None _ _)) in N.
        rewrite N. reflexivity.
      * assert (word.unsigned addr <> word.unsigned k). {
          intro C. apply E. apply word.unsigned_inj in C. exact C.
        }
        replace (Z.to_nat (word.unsigned (word.sub k addr))) with
          (S (Z.to_nat (word.unsigned (word.sub k (word.add addr (word.of_Z 1))))))
          by ZnWords.
        cbn.
        rewrite map.get_empty.
        destruct_one_match; reflexivity.
    + unfold map.disjoint. intros. rewrite map.get_put_dec in H0. fwd.
      match goal with
      | H: map.get ?m ?k = Some _ |- _ => assert (map.get m k <> None) as P
            by congruence
      end.
      eapply map.get_of_list_word_at_domain in P.
      pose proof (tuple.length_to_list bs) as L.
      ZnWords.
  Qed.

  Lemma getmany_of_tuple_footprint_to_split: forall n a vs m,
      Z.of_nat n <= 2 ^ 32 ->
      map.getmany_of_tuple m (Memory.footprint a n) = Some vs ->
      exists m', map.split m (map.of_list_word_at a (tuple.to_list vs)) m'.
  Proof.
    induction n; intros.
    - exists m. unfold map.split. split.
      + symmetry. apply map.putmany_empty_l.
      + apply map.disjoint_empty_l.
    - destruct vs as (v & vs). cbn in H0|-*. unfold tuple in H0. fwd.
      unfold map.getmany_of_tuple, Memory.footprint in IHn.
      specialize IHn with (2 := E0).
      edestruct IHn as (m' & IH). 1: lia. clear IHn.
      exists (map.remove m' a).
      unfold map.split in IH |- *. fwd.
      unfold map.disjoint in *. split.
      + apply map.map_ext.
        intros. rewrite ?map.get_putmany_dec in *.
        rewrite ?map.get_of_list_word_at in *.
        rewrite map.get_remove_dec in *.
        destr (word.eqb a k).
        * replace (Z.to_nat (word.unsigned (word.sub k k))) with O by ZnWords.
          destr (map.get m' k).
          { fwd. reflexivity. }
          { assumption. }
        * assert (word.unsigned a <> word.unsigned k). {
            intro C. apply E1. apply word.unsigned_inj in C. exact C.
          }
          replace (Z.to_nat (word.unsigned (word.sub k a))) with
            (S (Z.to_nat (word.unsigned (word.sub k (word.add a (word.of_Z 1))))))
            by ZnWords.
          cbn.
          reflexivity.
      + intros.
        rewrite map.get_remove_dec in H1.
        fwd.
        rewrite map.get_of_list_word_at in H0.
        assert (word.unsigned a <> word.unsigned k). {
          intro C. apply E1. apply word.unsigned_inj in C. exact C.
        }
        replace (Z.to_nat (word.unsigned (word.sub k a))) with
          (S (Z.to_nat (word.unsigned (word.sub k (word.add a (word.of_Z 1)))))) in H0
          by ZnWords.
        cbn in H0.
        eapply IHp1. 2: eassumption.
        rewrite map.get_of_list_word_at. eassumption.
  Qed.

  Lemma ptsto_bytes_of_list_word_at: forall n addr bs,
      Z.of_nat n <= 2 ^ 32 ->
      ptsto_bytes n addr bs (map.of_list_word_at addr (tuple.to_list bs)).
  Proof.
    induction n; intros; cbn.
    - unfold emp. split; [reflexivity|auto].
    - unfold sep. destruct bs as (b & bs). do 2 eexists. ssplit.
      3: eapply IHn; lia.
      2: unfold ptsto; reflexivity.
      eapply split_of_list_word_at_cons. lia.
  Qed.

  Lemma invert_load_bytes: forall n m addr bs,
      Z.of_nat n <= 2 ^ 32 ->
      load_bytes n m addr = Some bs ->
      exists R, sep (ptsto_bytes n addr bs) R m.
  Proof.
    intros. unfold load_bytes in *.
    eapply getmany_of_tuple_footprint_to_split in H0. 2: assumption. fwd.
    exists (eq m'). unfold sep. do 2 eexists; ssplit; eauto.
    eapply ptsto_bytes_of_list_word_at. assumption.
  Qed.

  Lemma invert_fetch: forall initial post decoder,
      mcomp_sat (run1 decoder) initial post ->
      exists R i, sep (initial.(pc) :-> i : instr decoder) R initial.(mem) /\
                  mcomp_sat (Execute.execute i;; endCycleNormal)
                            { initial with nextPc := word.add (pc initial) (word.of_Z 4) }
                            post.
  Proof.
    intros. apply invert_fetch0 in H. fwd. record.simp.
    eapply invert_load_bytes in Hp0. 2: cbv; discriminate 1. fwd.
    eexists R, _. split. 2: eassumption.
    unfold instr.
    eapply sep_ex1_l. unfold ex1.
    unfold truncated_scalar, littleendian. cbn -[Z.pow].
    exists (LittleEndianList.le_combine (tuple.to_list w)).
    apply sep_comm. apply sep_assoc. apply sep_emp_r. split; [|split].
    - apply sep_comm. eqapply Hp0. f_equal.
      rewrite <- LittleEndian.combine_eq.
      rewrite <- LittleEndian.split_eq.
      symmetry.
      eapply LittleEndian.split_combine.
    - reflexivity.
    - eapply LittleEndianList.le_combine_bound.
  Qed.

  Lemma interpret_loadWord: forall (initial: State) (postF: w32 -> State -> Prop)
                                   (postA: State -> Prop) (a v: word) R,
      sep (a :-> v : scalar) R initial.(mem) /\
      postF (LittleEndian.split 4 (word.unsigned v)) initial ->
      free.interpret run_primitive (Machine.loadWord Execute a) initial postF postA.
  Proof.
    intros *. intros [M P].
    cbn -[HList.tuple load_bytes] in *.
    unfold load.
    change load_bytes with bedrock2.Memory.load_bytes.
    erewrite load_bytes_of_sep; cycle 1. {
      unfold scalar, truncated_word, Scalars.truncated_word,
        Scalars.truncated_scalar, Scalars.littleendian in M.
      unfold ptsto_bytes.ptsto_bytes in *.
      exact M.
    }
    change (Memory.bytes_per access_size.word) with 4%nat.
    cbn. exact P.
  Qed.

  Set Printing Depth 100000.

  Lemma mdecodeM_to_InvalidI: forall z minst,
      mdecode z = MInstruction minst ->
      idecode z = InvalidInstruction z.
  Proof.
    unfold mdecode, idecode. intros.
    destruct_one_match_hyp; fwd.
    - rewrite <- decode_seq_correct. unfold decode_seq.
      change (bitwidth RV32I) with 32.
      remember (decodeI 32 z) as d.
      remember (decodeCSR 32 z) as c.
      repeat match goal with
             | |- context C[if andb ?b1 ?b2 then ?a1 else ?a2] =>
                 let G := context C[a2] in change G
             end.
      unfold decodeI, decodeCSR in *.
      rewrite Ep0p0, Ep0p1, Ep1 in *.
      change (c = InvalidCSR) in Heqc.
      change (d = InvalidI) in Heqd.
      subst.
      reflexivity.
    - eapply decode_RV32I_not_MInstruction in H. contradiction H.
  Qed.

  Lemma invert_mdecode_M: forall z minst,
      mdecode z = MInstruction minst ->
      exists rd rs1 rs2, minst = Mul rd rs1 rs2.
  Proof.
    unfold mdecode. intros. destruct_one_match_hyp.
    - inversion H. eauto.
    - eapply decode_RV32I_not_MInstruction in H. contradiction H.
  Qed.

  Lemma opcode_M_is_OP: forall inst,
      isValidM inst = true ->
      bitSlice (encode (MInstruction inst)) 0 7 = opcode_OP.
  Proof.
    intros.
    assert (0 <= opcode_OP < 2 ^ 7). {
      cbv. intuition congruence.
    }
    destruct inst; try discriminate; cbn; unfold encode_R. all: try solve [prove_Zeq_bitwise].
  Qed.

  Lemma decode_M_on_RV32I_Invalid: forall inst,
      isValidM inst = true ->
      decode RV32I (encode (MInstruction inst)) = InvalidInstruction (encode (MInstruction inst)).
  Proof.
    intros.
    pose proof opcode_M_is_OP _ H as A.
    let Henc := fresh "Henc" in
    match goal with
    | |- ?D ?I (encode ?x) = _ =>
      remember (encode x) as encoded eqn:Henc; symmetry in Henc
    end;
    cbv [ encode Encoder Verifier apply_InstructionMapper map_Fence map_FenceI map_I map_I_shift_57
          map_I_shift_66 map_I_system map_Invalid map_R map_R_atomic map_S map_SB map_U map_UJ] in Henc;
    match goal with
    | |- ?D ?I _ = _ => cbv beta delta [D]
    end.
    lets_to_eqs.
    match goal with
    | H: opcode = _ |- _ => rename H into HO
    end.
    assert (opcode = opcode_OP) by congruence. clear HO. subst opcode.
    match goal with
    | H: results = _ |- _ => cbn in H
    end.
    subst results.
    clear dependent decodeM. clear dependent decodeA. clear dependent decodeF.
    clear dependent decodeI64. clear dependent decodeM64. clear dependent decodeA64. clear dependent decodeF64.
    match goal with
    | H: decodeCSR = _ |- _ => rename H into HCSR
    end.
    repeat match type of HCSR with
           | ?d = (if ?b then ?x else ?y) => change (d = y) in HCSR
           end.
    subst decodeCSR.
    match goal with
    | H: decodeI = _ |- _ => rename H into HI
    end.
    match goal with
    | H: funct3 = _ |- _ => rename H into HF3
    end.
    match goal with
    | H: funct7 = _ |- _ => rename H into HF7
    end.
    destruct inst;
      try match goal with
          | H : isValidM InvalidM = true |- _ => discriminate H
          end;
      rewrite <-Henc in HF3, HF7;
      match type of HF3 with
      | funct3 = bitSlice (encode_R _ _ _ _ ?f _) _ _ =>
        assert (funct3 = f) as EF3
            by (rewrite HF3; clear;
                assert (0 <= f < 2 ^ 3) by (cbv; intuition congruence);
                unfold encode_R; prove_Zeq_bitwise)
      end;
      match type of HF7 with
      | funct7 = bitSlice (encode_R _ _ _ _ _ ?f) _ _ =>
        assert (funct7 = f) as EF7
            by (rewrite HF7; clear;
                assert (0 <= f < 2 ^ 7) by (cbv; intuition congruence);
                unfold encode_R; prove_Zeq_bitwise)
        end;
      rewrite ?EF3, ?EF7 in HI;
      repeat match type of HI with
             | ?d = (if ?b then ?x else ?y) => change (d = y) in HI
             end;
      subst decodeI resultI resultCSR;
      cbn;
      reflexivity.
  Qed.

  Definition basic_CSRFields_supported(r: State): Prop :=
    map.get r.(csrs) CSRField.MTVal <> None /\
    map.get r.(csrs) CSRField.MPP <> None /\
    map.get r.(csrs) CSRField.MPIE <> None /\
    map.get r.(csrs) CSRField.MIE <> None /\
    map.get r.(csrs) CSRField.MEPC <> None /\
    map.get r.(csrs) CSRField.MCauseCode <> None.

  Definition related(r1 r2: State): Prop :=
    r1.(regs) = r2.(regs) /\
    r1.(pc) = r2.(pc) /\
    r1.(nextPc) = r2.(nextPc) /\
    r1.(csrs) = map.empty /\
    basic_CSRFields_supported r2 /\
    regs_initialized r2.(regs) /\
    exists mtvec_base stacktrash stack_hi,
      map.get r2.(csrs) CSRField.MTVecBase = Some mtvec_base /\
      map.get r2.(csrs) CSRField.MScratch = Some stack_hi /\
      List.length stacktrash = 32%nat /\
      <{ * eq r1.(mem)
         * word.of_Z (stack_hi - 128) :-> stacktrash : word_array
         * LowerPipeline.mem_available (word.of_Z (stack_hi - 256))
                                       (word.of_Z (stack_hi - 128))
         * word.of_Z (mtvec_base * 4) :-> handler_insts : program idecode }> r2.(mem).

  (* From FlatToRiscvCommon, but with arbitrary n instead of access_size,
     because we also need support for loading 8 bytes, even though there's
     no instruction for it in RV32 *)
  Lemma subst_load_bytes_for_eq {n} {mH mL: Mem} {addr: word} {bs P R}:
      bedrock2.Memory.load_bytes n mH addr = Some bs ->
      Z.of_nat n <= 2 ^ 32 ->
      sep P (sep (eq mH) R) mL ->
      exists Q, sep P (sep (ptsto_bytes n addr bs) (sep Q R)) mL.
  Proof.
    intros.
    apply sep_of_load_bytes in H. 2: assumption.
    destruct H as [Q A]. exists Q.
    assert (sep (sep (ptsto_bytes n addr bs) Q) (sep P R) mL); [|ecancel_assumption].
    eapply FlatToRiscvCommon.seplog_subst_eq; [exact H1|..|exact A]. ecancel.
  Qed.

  Ltac subst_load_bytes_for_eq :=
    lazymatch goal with
    | Load: ?LB ?n _ _ _ ?m _ = _ |- _ =>
        unify LB @Memory.load_bytes;
        let P := fresh "P" in
        epose proof (subst_load_bytes_for_eq Load) as P;
        let Q := fresh "Q" in
        edestruct P as [Q ?]; clear P; [assumption | ecancel_assumption|]
    end.

  Lemma related_preserves_load_bytes: forall n sH sL a w,
      Z.of_nat n <= 2 ^ 32 ->
      related sH sL ->
      load_bytes n sH.(mem) a = Some w ->
      load_bytes n sL.(mem) a = Some w.
  Proof.
    unfold related. intros. fwd.
    subst_load_bytes_for_eq.
    eapply load_bytes_of_sep. ecancel_assumption.
  Qed.

  Lemma load_preserves_related: forall n c a initialH initialL postH,
      Z.of_nat n <= 2 ^ 32 ->
      related initialH initialL ->
      load n c a initialH postH ->
      load n c a initialL
        (fun res finalL => exists finalH, related finalH finalL /\ postH res finalH).
  Proof.
    unfold load.
    cbn. intros.
    destruct_one_match_hyp. 2: contradiction.
    erewrite related_preserves_load_bytes; eauto.
  Qed.

  Lemma store_preserves_related: forall n c a v initialH initialL postH,
      Z.of_nat n <= 2 ^ 32 ->
      related initialH initialL ->
      store n c a v initialH postH ->
      store n c a v initialL
            (fun finalL => exists finalH, related finalH finalL /\ postH finalH).
  Proof.
    unfold store, related. intros. fwd.
    lazymatch goal with
    | H: store_bytes _ _ _ _ = _ |- _ =>
        unshelve epose proof (FlatToRiscvCommon.store_bytes_frame H _) as P; cycle 2
    end.
    1: ecancel_assumption.
    destruct P as (finalML & P1 & P2).
    move E at bottom.
    unfold store_bytes in E. fwd.
    subst_load_bytes_for_eq.
    repeat match goal with
           | |- exists _, _ => eexists
           | |- _ /\ _ => split
           end; cycle -1.
    1: eassumption.
    all: eauto.
  Qed.

  Lemma run_primitive_preserves_related: forall a initialH initialL postF postA,
      related initialH initialL ->
      run_primitive a initialH postF postA ->
      run_primitive a initialL
        (fun res finalL => exists finalH,
             related finalH finalL /\ postF res finalH)
        (fun finalL => exists finalH, related finalH finalL /\ postA finalH).
  Proof.
    intros. pose proof H as R.
    unfold related, basic_CSRFields_supported in H|-*.
    simp.
    destruct a; cbn [run_primitive] in *.
    - exists initialH. intuition (congruence || eauto 10).
    - exists { initialH with regs ::= setReg z r }. record.simp.
      unfold setReg in *. destr ((0 <? z) && (z <? 32))%bool;
        intuition (congruence || eauto 10 using preserve_regs_initialized_after_put).
    - eapply load_preserves_related; eauto. cbv. discriminate 1.
    - eapply load_preserves_related; eauto. cbv. discriminate 1.
    - eapply load_preserves_related; eauto. cbv. discriminate 1.
    - eapply load_preserves_related; eauto. cbv. discriminate 1.
    - eapply store_preserves_related; eauto. cbv. discriminate 1.
    - eapply store_preserves_related; eauto. cbv. discriminate 1.
    - eapply store_preserves_related; eauto. cbv. discriminate 1.
    - eapply store_preserves_related; eauto. cbv. discriminate 1.
    - contradiction.
    - contradiction.
    - contradiction.
    - simp. replace (csrs initialH) with (@map.empty _ _ CSRFile) in E.
      rewrite map.get_empty in E. discriminate E.
    - simp. replace (csrs initialH) with (@map.empty _ _ CSRFile) in E.
      rewrite map.get_empty in E. discriminate E.
    - eauto 10.
    - simp. eauto 10.
    - simp. eauto 10.
    - exists initialH.
      intuition (congruence || eauto 10).
    - eexists. ssplit; cycle -1. 1: eassumption. all: try record.simp; try congruence; auto.
      eauto 10.
    - eexists. unfold updatePc in *. ssplit; cycle -1. 1: eassumption.
      all: try record.simp; try congruence; auto. eauto 10.
    - eexists. unfold updatePc in *. ssplit; cycle -1. 1: eassumption.
      all: try record.simp; try congruence; auto. eauto 10.
    - eexists. unfold updatePc in *. ssplit; cycle -1. 1: eassumption.
      all: record.simp; try congruence; auto. eauto 10.
  Qed.

  (* If we're running the same primitives on two related states, they remain related.
     (Note: decoding using RV32I vs RV32IM does not result in the same primitives). *)
  Lemma mcomp_sat_preserves_related: forall m initialL initialH postH,
      related initialH initialL ->
      mcomp_sat m initialH postH ->
      mcomp_sat m initialL (fun finalL => exists finalH, related finalH finalL /\ postH finalH).
  Proof.
    induction m; intros. 2: {
      eapply weaken_mcomp_sat. 2: eassumption. eauto.
    }
    unfold mcomp_sat in *.
    cbn in *.
    eapply weaken_run_primitive. 3: {
      eapply run_primitive_preserves_related; eassumption.
    }
    2: auto.
    cbn.
    intros. simp.
    eapply H. 1: eassumption.
    eassumption.
  Qed.

  Lemma mcomp_sat_endCycleNormal: forall (mach: State) (post: State -> Prop),
      post { mach with pc := mach.(nextPc); nextPc ::= word.add (word.of_Z 4) } ->
      mcomp_sat endCycleNormal mach post.
  Proof. intros. assumption. Qed.

  Lemma interpret_bind{T U}(postF: U -> State -> Prop)(postA: State -> Prop) a b s:
    free.interpret run_primitive a s
                   (fun (x: T) s0 => free.interpret run_primitive (b x) s0 postF postA) postA ->
    free.interpret run_primitive (free.bind a b) s postF postA.
  Proof. eapply free.interpret_bind. apply weaken_run_primitive. Qed.

  Lemma interpret_getPC: forall (initial: State) (postF : word -> State -> Prop) (postA : State -> Prop),
      postF initial.(pc) initial ->
      free.interpret run_primitive getPC initial postF postA.
  Proof. intros *. exact id. Qed.

  Lemma interpret_startCycle: forall (initial: State) (postF : unit -> State -> Prop) (postA : State -> Prop),
      postF tt { initial with nextPc :=
                                word.add initial.(pc) (word.of_Z (word := word) 4) } ->
      free.interpret run_primitive startCycle initial postF postA.
  Proof. intros *. exact id. Qed.

  Lemma interpret_setPC: forall (m: State) (postF : unit -> State -> Prop) (postA : State -> Prop) (v: word),
      postF tt { m with nextPc := v } ->
      free.interpret run_primitive (setPC v) m postF postA.
  Proof. intros *. exact id. Qed.

  (* Otherwise `@map.rep CSRField.CSRField Z CSRFile` gets simplified into `@SortedList.rep CSRFile_map_params`
     and `rewrite` stops working because of implicit argument mismatches. *)
  Arguments map.rep : simpl never.

  Lemma interpret_getRegister0: forall (initial: State) (postF: word -> State -> Prop) (postA: State -> Prop),
      postF (word.of_Z 0) initial ->
      free.interpret run_primitive (getRegister RegisterNames.zero) initial postF postA.
  Proof.
    intros. simpl. unfold getReg, RegisterNames.zero. destr (Z.eq_dec 0 0).
    2: exfalso; congruence. assumption.
  Qed.

  Lemma interpret_getRegister: forall (initial: State) (postF: word -> State -> Prop) (postA: State -> Prop) r v,
      0 < r < 32 ->
      map.get initial.(regs) r = Some v ->
      postF v initial ->
      free.interpret run_primitive (getRegister r) initial postF postA.
  Proof.
    intros. simpl. unfold getReg. destruct_one_match; fwd. 1: assumption.
    exfalso; lia.
  Qed.

  (* better wrt evar creation order *)
  Lemma interpret_getRegister': forall (initial: State) (postF: word -> State -> Prop) (postA: State -> Prop) r,
      0 < r < 32 ->
      regs_initialized initial.(regs) ->
      (forall v, map.get initial.(regs) r = Some v -> postF v initial) ->
      free.interpret run_primitive (getRegister r) initial postF postA.
  Proof.
    intros. specialize (H0 _ H). destruct H0. eapply interpret_getRegister. 1: blia.
    all: eauto.
  Qed.

  Lemma interpret_setRegister: forall (initial: State) (postF: unit -> State -> Prop) (postA: State -> Prop) r v,
      0 < r < 32 ->
      postF tt { initial with regs ::= map.set r v } ->
      free.interpret run_primitive (setRegister r v) initial postF postA.
  Proof.
    intros. simpl. unfold setReg. destruct_one_match; fwd. 1: assumption.
    exfalso; lia.
  Qed.

  Lemma interpret_endCycleEarly: forall (m: State) (postF : unit -> State -> Prop) (postA : State -> Prop),
      postA (updatePc m) ->
      free.interpret run_primitive (endCycleEarly _) m postF postA.
  Proof. intros *. exact id. Qed.

  Lemma interpret_getCSRField: forall (m: State) (postF : Z -> State -> Prop) (postA : State -> Prop) fld z,
      map.get m.(csrs) fld = Some z ->
      postF z m ->
      free.interpret run_primitive (getCSRField fld) m postF postA.
  Proof. intros. cbn -[map.get map.rep]. rewrite H. assumption. Qed.

  Lemma interpret_setCSRField: forall (m: State) (postF : _->_->Prop) (postA : State -> Prop) fld z,
      map.get m.(csrs) fld <> None ->
      postF tt { m with csrs ::= map.set fld z } ->
      free.interpret run_primitive (setCSRField fld z) m postF postA.
  Proof.
    intros. cbn -[map.get map.rep]. destruct_one_match. 1: assumption. congruence.
  Qed.

  Lemma build_fetch_one_instr:
    forall (initial: State) iset post (instr1: Instruction) (R: Mem -> Prop),
      sep (initial.(pc) :-> instr1 : instr iset) R initial.(mem) ->
      mcomp_sat (Execute.execute instr1;; endCycleNormal)
                { initial with nextPc := word.add (pc initial) (word.of_Z 4) } post ->
      mcomp_sat (run1 iset) initial post.
  Proof.
    intros. unfold run1, mcomp_sat in *.
    eapply interpret_bind.
    eapply interpret_startCycle.
    eapply interpret_bind.
    eapply interpret_getPC.
    eapply interpret_bind.
    unfold instr in H. extract_ex1_and_emp_in H. fwd.
    eapply interpret_loadWord. split. {
      unfold scalar. cbn [seps].
      unfold truncated_scalar, truncated_word in *.
      unfold Scalars.truncated_word, Scalars.truncated_scalar in *.
      rewrite <- (word.unsigned_of_Z_nowrap z) in H by assumption.
      exact H.
    }
    eqapply H0. do 3 f_equal.
    rewrite LittleEndian.combine_split.
    ZnWords.
  Qed.

  Lemma run_store: forall n addr (v_old v_new: tuple byte n) R (initial: State)
                          (kind: SourceType) (post: State -> Prop),
      sep (ptsto_bytes.ptsto_bytes n addr v_old) R initial.(mem) ->
      (forall m: Mem, sep (ptsto_bytes.ptsto_bytes n addr v_new) R m ->
                      post { initial with mem := m }) ->
      MinimalCSRs.store n kind addr v_new initial post.
  Proof.
    intros. unfold store. cbn [seps] in *.
    eapply store_bytes_of_sep in H. 2: exact H0.
    destruct H as (m' & H & HP). change store_bytes with Memory.store_bytes. rewrite H.
    apply HP.
  Qed.

  Lemma interpret_storeWord: forall addr (v_old v_new: word) R (initial: State)
                                    (postF: unit -> State -> Prop) (postA: State -> Prop),
      (* /\ instead of separate hypotheses because changes to the goal made while
         proving the first hyp are needed to continue with the second hyp
         (to remember how to undo the splitting of the word_array in which the scalar
         was found) *)
      sep (addr :-> v_old : scalar) R initial.(mem) /\
      (forall m, sep (addr :-> v_new : scalar) R m ->
                 postF tt { initial with mem := m }) ->
      free.interpret run_primitive (Machine.storeWord Execute addr
         (LittleEndian.split 4 (word.unsigned v_new))) initial postF postA.
  Proof.
    (* Note: some unfolding/conversion is going on here that we prefer to control with
       this lemma rather than to control each time we store a word *)
    intros. destruct H. eapply run_store; eassumption.
  Qed.

  Definition bytes{n: nat}(v: tuple byte n)(addr: word): Mem -> Prop :=
    eq (map.of_list_word_at addr (tuple.to_list v)).

  Lemma interpret_getPrivMode: forall (m: State) (postF: PrivMode -> State -> Prop) (postA: State -> Prop),
      postF Machine m -> (* we're always in machine mode *)
      free.interpret run_primitive getPrivMode m postF postA.
  Proof. intros. cbn -[map.get map.rep]. assumption. Qed.

  Lemma interpret_setPrivMode: forall (s: State) (postF : unit -> State -> Prop) (postA : State -> Prop) (m: PrivMode),
      (* this simple machine only allows setting the mode to Machine mode *)
      m = Machine ->
      postF tt s ->
      free.interpret run_primitive (setPrivMode m) s postF postA.
  Proof. intros * E. subst. exact id. Qed.

  Ltac program_index l :=
    lazymatch l with
    | program _ _ :: _ => constr:(0%nat)
    | _ :: ?rest => let i := program_index rest in constr:(S i)
    end.

  Ltac instr_lookup :=
    lazymatch goal with
    | |- nth_error ?insts ?index = Some ?inst =>
      repeat match goal with
             | |- context[word.unsigned ?x] => progress ring_simplify x
             end;
      rewrite ?word.unsigned_of_Z_nowrap by
          match goal with
          | |- 0 <= ?x < 2 ^ 32 =>
            lazymatch isZcst x with
            | true => vm_compute; intuition congruence
            end
          end;
      reflexivity
    end.

  Ltac step :=
    match goal with
    | |- _ => rewrite !Monads.associativity
    | |- _ => rewrite !Monads.left_identity
    | |- _ => progress cbn [Execute.execute ExecuteCSR.execute ExecuteCSR.checkPermissions
                            CSRGetSet.getCSR CSRGetSet.setCSR
                            ExecuteI.execute]
    | |- _ => progress cbn_MachineWidth
    | |- _ => progress intros
    | |- _ => progress unfold ExecuteCSR.checkPermissions, CSRSpec.getCSR, CSRSpec.setCSR,
                              PseudoInstructions.Csrr, PseudoInstructions.Csrw,
                              raiseExceptionWithInfo, updatePc
    | |- context[(@Monads.when ?M ?MM ?A ?B)] => change (@Monads.when M MM A B) with (@Monads.Return M MM _ tt)
    | |- context[(@Monads.when ?M ?MM ?A ?B)] => change (@Monads.when M MM A B) with B
    | |- _ => (*progress already embedded*) record.simp
    | |- _ => progress change (CSR.lookupCSR MScratch) with CSR.MScratch
    | |- _ => progress change (CSR.lookupCSR MTVal) with CSR.MTVal
    | |- _ => progress change (CSR.lookupCSR MEPC) with CSR.MEPC
    | |- _ => unfold Basics.compose, map.set; rewrite !map.get_put_diff
                by (unfold RegisterNames.sp, RegisterNames.ra; congruence)
    | |- mcomp_sat (Monads.Bind _ _) _ _ => eapply mcomp_sat_bind
    | |- free.interpret run_primitive ?x ?initial ?postF _ =>
      lazymatch x with
      | Monads.Bind _ _ => eapply interpret_bind
      | Monads.Return ?a => change (postF a initial); cbv beta
      | free.bind _ _ => eapply interpret_bind
      | free.ret _ => rewrite free.interpret_ret
      | getPC => eapply interpret_getPC
      | setPC _ => eapply interpret_setPC
      | Machine.storeWord Execute _ _ =>
          eapply interpret_storeWord;
          after_mem_modifying_lemma;
          repeat (repeat word_simpl_step_in_hyps; fwd)
      | getRegister ?r =>
        lazymatch r with
        | 0 => eapply interpret_getRegister0
        | RegisterNames.zero => eapply interpret_getRegister0
        | _ => first [ eapply interpret_getRegister ; [solve [repeat step]..|]
                     | eapply interpret_getRegister'; [solve [repeat step]..|] ]
        end
      | setRegister _ _ => eapply interpret_setRegister
      | endCycleEarly _ => eapply interpret_endCycleEarly
      | getCSRField _ => eapply interpret_getCSRField
      | setCSRField _ _ => eapply interpret_setCSRField
      | getPrivMode => eapply interpret_getPrivMode
      | setPrivMode _ => eapply interpret_setPrivMode; [reflexivity|]
      | if (negb (word.eqb ?a ?b)) then _ else _ =>
          rewrite (word.eqb_eq a b) by (apply divisibleBy4_alt; solve_divisibleBy4);
          cbv beta iota delta [negb]
      end
    | |- _ => compareZconsts
    | |- map.get _ _ = Some _ => eassumption
    | |- _ <> None => congruence
    | |- map.get (map.set _ _ _) _ = _ => unfold map.set
    | |- map.get (map.put _ ?x _) ?x = _ => eapply map.get_put_same
    | |- map.get (map.put _ _ _) _ = _ => eapply get_put_diff_eq_l; [compareZconsts|]
    | |- map.get (map.set _ _ _) _ <> None => unfold map.set
    | |- map.get (map.put _ ?x _) ?x <> None => rewrite map.get_put_same
    | |- map.get (map.put _ ?x _) ?y <> None => rewrite map.get_put_diff by congruence
    | |- regs_initialized (map.put _ _ _) => eapply preserve_regs_initialized_after_put
    | |- regs_initialized (map.set _ _ _) => eapply preserve_regs_initialized_after_put
    | |- mcomp_sat endCycleNormal _ _ => eapply mcomp_sat_endCycleNormal
    | H: ?P |- ?P => exact H
    | |- mcomp_sat (run1 idecode) _ _ =>
        eapply build_fetch_one_instr; try record.simp; cbn_MachineWidth;
        [ scancel_asm
        | repeat word_simpl_step_in_goal;
          lazymatch goal with
          | |- context[Execute.execute ?x] =>
              first [ let x' := eval hnf in x in let h := head x' in is_constructor h;
                      change x with x'
                    | fail 1000 x "can't be simplified to a concrete instruction" ]
          end ]
    | |- _ => progress change (translate _ _ ?x)
                       with (@free.ret riscv_primitive primitive_result _ x)
    end.

  Local Hint Mode word.word - : typeclass_instances.

  Lemma save_regs_correct_aux: forall n start R (initial: State) stackaddr oldvals spval
                                  vals (post: State -> Prop),
      List.length oldvals = n ->
      map.get initial.(regs) RegisterNames.sp = Some spval ->
      stackaddr = word.add spval (word.of_Z (4 * start)) ->
      initial.(nextPc) = word.add initial.(pc) (word.of_Z 4) ->
      0 < start ->
      (Z.to_nat start + n = 32)%nat ->
      map.getmany_of_list initial.(regs) (List.unfoldn (Z.add 1) n start) = Some vals ->
      <{ * stackaddr :-> oldvals : word_array
         * initial.(pc) :-> (map (fun r => IInstruction (Sw RegisterNames.sp r (4 * r)))
               (List.unfoldn (BinInt.Z.add 1) n start)) : program idecode
         * R }> initial.(mem) /\
      (forall m: Mem,
         <{ * stackaddr :-> vals : word_array
            * initial.(pc) :-> (map (fun r => IInstruction (Sw RegisterNames.sp r (4 * r)))
                 (List.unfoldn (Z.add 1) n start)) : program idecode
            * R }> m ->
         runsTo (mcomp_sat (run1 idecode)) { initial with mem := m;
           nextPc ::= word.add (word.of_Z (4 * Z.of_nat n));
           pc ::= word.add (word.of_Z (4 * Z.of_nat n)) } post) ->
      runsTo (mcomp_sat (run1 idecode)) initial post.
  Proof.
    induction n; intros.
    - repeat word_simpl_step_in_hyps.
      destruct oldvals. 2: discriminate.
      destruct vals. 2: discriminate.
      match goal with
      | H: _ |- _ => destruct H as [A B]; eqapply B
      end.
      1: eassumption.
      destruct initial.
      record.simp.
      f_equal; autorewrite with rew_word_morphism; ring.
    - destruct vals as [|val vals]. {
        apply_in_hyps map.getmany_of_list_length. discriminate.
      }
      destruct oldvals as [|oldval oldvals]. 1: discriminate.
      fwd.
      assert (0 < start < 32) by lia.
      eapply runsToStep_cps. repeat step.
      subst stackaddr.
      repeat (repeat word_simpl_step_in_hyps; fwd).
      cbn [List.skipn List.map] in *.
      eapply IHn with (start := 1 + start) (oldvals := oldvals); try record.simp.
      + reflexivity.
      + eassumption.
      + reflexivity.
      + ring.
      + lia.
      + lia.
      + eassumption.
      + after_mem_modifying_lemma.
        eqapply H6p1. 2: {
          destruct initial; record.simp.
          f_equal; try ZnWords.
        }
        scancel_asm.
  Qed.

  Lemma save_regs3to31_correct: forall R (initial: State) oldvals spval
                                  (post: State -> Prop),
      map.get initial.(regs) RegisterNames.sp = Some spval ->
      initial.(nextPc) = word.add initial.(pc) (word.of_Z 4) ->
      regs_initialized initial.(regs) ->
      (<{ * word.add spval (word.of_Z 12) :-> oldvals : word_array
          * initial.(pc) :-> save_regs3to31 : program idecode
          * R }> initial.(mem) /\
       List.length oldvals = 29%nat /\
       forall m vals,
         map.getmany_of_list initial.(regs) regs3to31 = Some vals ->
         <{ * word.add spval (word.of_Z 12) :-> vals : word_array
            * initial.(pc) :-> save_regs3to31 : program idecode
            * R }> m ->
         runsTo (mcomp_sat (run1 idecode)) { initial with mem := m;
           nextPc ::= word.add (word.of_Z (4 * Z.of_nat 29));
           pc ::= word.add (word.of_Z (4 * Z.of_nat 29)) } post) ->
      runsTo (mcomp_sat (run1 idecode)) initial post.
  Proof.
    unfold save_regs3to31. intros.
    assert (exists vals,
       map.getmany_of_list (regs initial) regs3to31 = Some vals) as E. {
      eapply map.getmany_of_list_exists with (P := fun r => 3 <= r < 32).
      - change 32 with (3 + Z.of_nat 29).
        eapply List.unfoldn_Z_seq_Forall.
      - intros k Bk. unfold regs_initialized in H1.
        eapply H1. lia.
    }
    destruct E as [vals G].
    match goal with
    | H: _ /\ _ /\ forall _, _ |- _ => destruct H as (HM & L & HPost)
    end.
    eapply save_regs_correct_aux with (start := 3); try eassumption; try reflexivity.
    intros. split.
    - exact HM.
    - intros; eapply HPost. 1: eassumption. assumption.
  Qed.

  Lemma restore_regs3to31_correct_aux: forall n vals R (initial: State) spval stackaddr start
                                  (post: State -> Prop),
      List.length vals = n ->
      map.get initial.(regs) RegisterNames.sp = Some spval ->
      stackaddr = word.add spval (word.of_Z (4 * start)) ->
      initial.(nextPc) = word.add initial.(pc) (word.of_Z 4) ->
      3 <= start ->
      (Z.to_nat start + n = 32)%nat ->
      <{ * stackaddr :-> vals : word_array
         * initial.(pc) :-> map (fun r => IInstruction (Lw r RegisterNames.sp (4 * r)))
                                (List.unfoldn (BinInt.Z.add 1) n start)
            : program idecode
         * R }> initial.(mem) ->
      runsTo (mcomp_sat (run1 idecode)) { initial with
           regs := map.putmany initial.(regs) (map.of_list_Z_at start vals);
           nextPc ::= word.add (word.of_Z (4 * Z.of_nat n));
           pc ::= word.add (word.of_Z (4 * Z.of_nat n)) } post ->
      runsTo (mcomp_sat (run1 idecode)) initial post.
  Proof.
    induction n; intros.
    - destruct vals. 2: discriminate.
      replace (map.of_list_Z_at start []) with map.empty in *. 2: {
        unfold map.of_list_Z_at. cbn. unfold MapKeys.map.map_keys.
        symmetry. apply map.fold_empty.
      }
      rewrite map.putmany_empty_r in H6.
      eqapply H6. destruct initial. record.simp. f_equal; ZnWords.
    - destruct vals as [|val vals]. 1: discriminate.
      assert (0 < start < 32) by lia.
      eapply runsToStep_cps. repeat step.
      subst stackaddr.
      eapply interpret_loadWord. scancel_asm. clear_split_sepclause_stack.
      repeat step.
      repeat word_simpl_step_in_goal. cbn [List.nth List.length] in *.
      repeat (repeat word_simpl_step_in_hyps; fwd).
      cbn [List.map] in *.
      eapply IHn with (start := 1 + start) (vals := vals); try record.simp.
      + congruence.
      + unfold map.set. rewrite map.get_put_diff. 1: eassumption.
        unfold RegisterNames.sp. lia.
      + reflexivity.
      + ring.
      + lia.
      + lia.
      + scancel_asm.
      + eqapply H6.
        destruct initial; record.simp.
        f_equal; try ZnWords.
        unfold map.set.
        apply map.map_ext.
        intro k.
        rewrite ?map.get_putmany_dec, ?map.get_put_dec, ?map.get_of_list_Z_at.
        unfold List.Znth_error.
        destr (start =? k).
        * destr (k - k <? 0). 1: exfalso; lia.
          destr (k - (1 + k) <? 0). 2: exfalso; lia.
          rewrite Z.sub_diag. cbn [List.nth_error Z.to_nat].
          f_equal. rewrite LittleEndian.combine_split. unfold signExtend. ZnWords.
        * destr (k - start <? 0); destr (k - (1 + start) <? 0);
            try (exfalso; lia); try reflexivity.
          replace (Z.to_nat (k - start)) with (S (Z.to_nat (k - (1 + start)))) by lia.
          cbn [List.nth_error Z.to_nat]. reflexivity.
  Qed.

  Lemma restore_regs3to31_correct: forall R (initial: State) vals spval
                                  (post: State -> Prop),
      map.get initial.(regs) RegisterNames.sp = Some spval ->
      initial.(nextPc) = word.add initial.(pc) (word.of_Z 4) ->
      <{ * word.add spval (word.of_Z 12) :-> vals : word_array
         * initial.(pc) :-> restore_regs3to31 : program idecode
         * R }> initial.(mem) /\
      List.length vals = 29%nat /\
      runsTo (mcomp_sat (run1 idecode)) { initial with
           regs := map.putmany initial.(regs) (map.of_list_Z_at 3 vals);
           nextPc ::= word.add (word.of_Z (4 * Z.of_nat 29));
           pc ::= word.add (word.of_Z (4 * Z.of_nat 29)) } post ->
      runsTo (mcomp_sat (run1 idecode)) initial post.
  Proof.
    unfold restore_regs3to31. intros. fwd.
    eapply restore_regs3to31_correct_aux with (start := 3).
    - eassumption.
    - eassumption.
    - reflexivity.
    - assumption.
    - cbv. discriminate 1.
    - reflexivity.
    - eassumption.
    - eassumption.
  Qed.

  Lemma related_with_nextPc: forall initialH initialL,
      related initialH initialL ->
      related { initialH with nextPc := word.add (pc initialH) (word.of_Z 4) }
              { initialL with nextPc := word.add (pc initialL) (word.of_Z 4) }.
  Proof.
    destruct initialH, initialL; unfold related; record.simp.
    intros; fwd; eauto 20.
  Qed.

  Lemma softmul_correct: forall initialH initialL post,
      runsTo (mcomp_sat (run1 mdecode)) initialH post ->
      related initialH initialL ->
      runsTo (mcomp_sat (run1 idecode)) initialL (fun finalL =>
        exists finalH, related finalH finalL /\ post finalH).
  Proof.
    intros *. intros R. revert initialL. induction R; intros. {
      apply runsToDone. eauto.
    }
    unfold run1 in H.
    pose proof H2 as Rel.
    unfold related, basic_CSRFields_supported in H2.
    eapply invert_fetch in H. fwd.
    rename initial into initialH.
    match goal with
    | H1: sep _ _ initialH.(mem), H2: sep _ _ initialL.(mem) |- _ =>
        rename H1 into MH, H2 into ML
    end.
    pose proof MH as MH'. move MH' after MH.
    destruct MH as (mI & mHRest & SpH & MHI & MHRest). clear MHRest.
    unfold instr, ex1 in MHI.
    destruct MHI as (z & MHI).
    eapply sep_emp_r in MHI. destruct MHI as (MHI & Dz & Bz). subst i.
    cbn [seps] in ML.
    eapply subst_split in ML. 2: exact SpH.
    epose proof (proj1 (sep_inline_eq _ _ initialL.(mem))) as ML'.
    especialize ML'. {
      eexists. split. 2: exact MHI. ecancel_assumption.
    }
    flatten_seps_in ML'. cbn [seps] in ML'. clear ML.
    remember (match mdecode z with
              | MInstruction _ => false
              | _ => true
              end) as doSame eqn: E.
    symmetry in E.
    destruct doSame; fwd.

    - (* not a mul instruction, so both machines do the same *)
      replace initialH.(pc) with initialL.(pc) in ML'.
      rename Hp1 into F. move F at bottom.
      unfold mdecode in E, F.
      match type of E with
      | match (if ?x then _ else _) with _ => _ end = true => destr x
      end.
      1: discriminate E.
      eapply @runsToStep with
        (midset := fun midL => exists midH, related midH midL /\ midset midH).
      + eapply build_fetch_one_instr with (instr1 := decode RV32I z).
        { refine (Morphisms.subrelation_refl impl1 _ _ _ (mem initialL) ML').
          cancel.
          cancel_seps_at_indices_by_implication 4%nat 0%nat. 2: exact impl1_refl.
          unfold impl1, instr, ex1, emp. intros m A.
          eexists.
          refine (Morphisms.subrelation_refl impl1 _ _ _ m A).
          cancel.
          cancel_seps_at_indices_by_implication 0%nat 0%nat. 1: exact impl1_refl.
          unfold impl1. cbn [seps]. unfold emp. intros.
          unfold idecode. fwd. auto. }
        eapply mcomp_sat_preserves_related; eauto 2 using related_with_nextPc.
      + intros midL. intros. simp. eapply H1; eassumption.

    - (* MInstruction *)
      rename E0 into E.
      (* fetch M instruction (considered invalid by RV32I machine) *)
      eapply runsToStep_cps.
      replace initialH.(pc) with initialL.(pc) in ML'. rename ML' into ML.
      eapply build_fetch_one_instr with (instr1 := InvalidInstruction z).
      { replace initialH.(pc) with initialL.(pc) in ML.
        refine (Morphisms.subrelation_refl impl1 _ _ _ (mem initialL) ML).
        cancel.
        cancel_seps_at_indices_by_implication 4%nat 0%nat. 2: exact impl1_refl.
        move E at bottom.
        unfold impl1, instr, ex1, emp. intros m A.
        eexists.
        refine (Morphisms.subrelation_refl impl1 _ _ _ m A).
        cancel.
        cancel_seps_at_indices_by_implication 0%nat 0%nat. 1: exact impl1_refl.
        unfold impl1. cbn [seps]. unfold emp. intros.
        fwd.
        eapply mdecodeM_to_InvalidI in E. auto. }

      repeat step.

      (* step through handler code *)

      (* Csrrw sp sp MScratch *)
      eapply runsToStep_cps. repeat step.

      (* Sw sp zero (-128) *)
      eapply runsToStep_cps. repeat step.

      (* Sw sp ra (-124) *)
      eapply runsToStep_cps. repeat step.

      (* Csrr ra MScratch *)
      eapply runsToStep_cps. repeat step.

      (* Sw sp ra (-120) *)
      eapply runsToStep_cps. repeat step.

      (* Csrw sp MScratch *)
      eapply runsToStep_cps. repeat step.

      (* Addi sp sp (-128) *)
      eapply runsToStep_cps. repeat step.

      (* save_regs3to31 *)
      eapply save_regs3to31_correct; try record.simp.
      { repeat step. }
      { ZnWords. }
      { repeat step. }
      autorewrite with rew_word_morphism. repeat word_simpl_step_in_goal.

      unfold handler_insts, asm_handler_insts in ML.
      rewrite !(array_app (E := Instruction)) in ML.
      repeat match type of ML with
             | context[List.length ?l] => let n := concrete_list_length l in
                                         change (List.length l) with n in ML
             end.
      autorewrite with rew_word_morphism in *.
      (* needed because of https://github.com/coq/coq/issues/10848 (otherwise evar
         of `Datatypes.length ?oldvals` gets instantiated to whole LHS of rewrite lemma *)

Ltac set_evars_goal :=
  repeat match goal with
         | |- context[?x] => is_evar x; set x
         end.

Ltac subst_evars :=
  repeat match goal with
         | y:= ?v |- _ => is_evar v; subst y
         end.

      set_evars_goal.
      repeat (repeat word_simpl_step_in_hyps; fwd).
      flatten_seps_in ML. cbn [seps] in ML.
      subst_evars.
      scancel_asm. split. 1: listZnWords.
      intro mNew. intros.
      (* TODO this should be in listZnWords or in sidecondition solvers in SepAutoArray *)
      assert (List.length vals = 29%nat). {
        unfold regs3to31 in *.
        apply_in_hyps @map.getmany_of_list_length.
        symmetry. assumption.
      }
      pop_split_sepclause_stack mNew.
      transfer_sep_order.
      repeat (repeat word_simpl_step_in_hyps; fwd).

      (* TODO to get splitting/merging work for the program as well, we need
         rewrite_ith_in_lhs_of_impl1 to also perform the cancelling, so that
         the clause to be canceled on the right (callee) shows up in the
         sidecondition of split_sepclause and the hints in split_sepclause_sidecond
         can use what's there instead of creating a (List.firstn n (List.skipn i ...))
         that doesn't match the callee's precondition *)

      (* Csrr a0 MTVal       a0 := the invalid instruction i that caused the exception *)
      eapply runsToStep_cps. repeat step.

      (* Addi a1 sp 0        a1 := pointer to registers *)
      eapply runsToStep_cps. repeat step.

      (* Jal ra ofs          call mul_insts *)
      eapply runsToStep_cps. repeat step.

      eapply runsTo_trans_cps.
      pose proof E as E'.
      eapply invert_mdecode_M in E'. fwd.
      pose proof word.unsigned_of_Z_nowrap _ Bz as Q. rewrite <- Q in E. clear Q.
      (* TODO this match should not be needed *)
      match type of ML with
      | context[LowerPipeline.mem_available ?lo ?hi] =>
          eapply mul_correct with (stack_start := lo) (stack_pastend := hi)
            (regvals := [word.of_Z 0] ++ [v0] ++ [v] ++ vals);
          repeat step;
          try ZnWords
      end.
      1: exact E.
      repeat match goal with
             | |- context[List.length ?l] => let n := concrete_list_length l in
                                             change (List.length l) with n
             end.
      autorewrite with rew_word_morphism in *.
      repeat (repeat word_simpl_step_in_goal; fwd).

      scancel_asm. split. 1: listZnWords.
      clear ML m m_1.
      intros m l ML OD RIl.
      flatten_seps_in ML. cbn [seps] in ML.

      (* Csrr t1 MEPC *)
      eapply runsToStep_cps. repeat step.

      (* Addi t1 t1 4 *)
      eapply runsToStep_cps. repeat step.

      (* Csrw t1 MEPC *)
      eapply runsToStep_cps. repeat step.

      (* restore_regs3to31 *)

      eapply restore_regs3to31_correct; try record.simp.
      { unfold map.only_differ, elem_of in OD.
        specialize (OD RegisterNames.sp).
        destruct OD as [OD | OD].
        { cbn in OD. contradiction OD. }
        repeat step.
        unfold map.set in OD.
        rewrite ?map.get_put_diff in OD by compareZconsts.
        rewrite map.get_put_same in OD. symmetry in OD. exact OD. }
      { ZnWords. }
      autorewrite with rew_word_morphism. repeat word_simpl_step_in_goal.
      scancel_asm. split. 1: listZnWords.

      repeat word_simpl_step_in_goal.
      match goal with
      | |- runsTo _ ?mach _ => eassert (Gsp: map.get (regs mach) RegisterNames.sp = Some _)
      end.
      { repeat step.
        rewrite map.get_putmany_left.
        - repeat step.
          unfold map.only_differ, elem_of in OD.
          specialize (OD RegisterNames.sp).
          destruct OD as [OD | OD].
          { cbn in OD. contradiction OD. }
          repeat step.
          unfold map.set in OD.
          rewrite ?map.get_put_diff in OD by compareZconsts.
          rewrite map.get_put_same in OD. symmetry in OD. exact OD.
        - rewrite map.get_of_list_Z_at.
          change (RegisterNames.sp - 3) with (-1).
          unfold List.Znth_error. reflexivity. }
      record.simp.

      (* Lw ra sp 4 *)
      eapply runsToStep_cps. repeat step.
      eapply interpret_loadWord. scancel_asm. clear_split_sepclause_stack.
      repeat step.

      (* Lw sp sp 8 *)
      eapply runsToStep_cps. repeat step.
      eapply interpret_loadWord. scancel_asm. clear_split_sepclause_stack.
      repeat step.

      (* Mret *)
      eapply runsToStep_cps. repeat step.

      rename H1 into IH.
      eapply IH with (mid := updatePc { initialH with
        nextPc := word.add (pc initialH) (word.of_Z 4);
        regs ::= setReg rd (word.mul (getReg initialH.(regs) rs1)
                                     (getReg initialH.(regs) rs2)) }).
      { move Hp1 at bottom.
        cbn in Hp1.
        exact Hp1. }
      unfold related, updatePc, map.set, basic_CSRFields_supported; record.simp.
      cbn [List.app] in *.
      rewrite ?word.of_Z_unsigned.
      unfold map.set in *.
      match goal with
      | H: _ |- _ => rewrite map.get_put_diff in H by compareZconsts
      end.
      assert (OD': map.only_differ initialH.(regs)
                       (union (singleton_set RegisterNames.sp)
                              Registers.reg_class.caller_saved) l). {
        replace initialH.(regs) with initialL.(regs).
        eapply only_differ_trans. 2: {
          eapply only_differ_subset. 1: exact OD.
          eapply subset_union_rr. eapply subset_refl.
        }
        repeat (eapply only_differ_put_r;
                [ first [ eapply in_union_r; reflexivity
                        | eapply in_union_l; reflexivity ] | ]).
        eapply only_differ_refl.
      }
      match goal with
      | H: map.getmany_of_list _ _ = Some _ |- _ =>
          rename H into GetVals; move GetVals at bottom
      end.
      match goal with
      | H: regs_initialized (regs initialL) |- _ => rename H into RI; move RI at bottom
      end.
      replace (regs initialL) with (regs initialH) in *.
      assert (GetVal: forall k, 0 <= k < 29 ->
        nth_error vals (Z.to_nat k) = map.get initialH.(regs) (k + 3)). {
        intros k kR.
        unfold regs_initialized in RI. specialize (RI (k + 3)).
        destruct RI as [kv Gkv]. 1: lia.
        rewrite nth_error_nth' with (d := default) by lia.
        symmetry.
        epose proof map.getmany_of_list_get _ (Z.to_nat k) _ _ (k + 3) as Q.
        specialize Q with (1 := GetVals).
        rewrite !map.get_put_diff in Q by (unfold RegisterNames.sp, RegisterNames.ra; lia).
        eapply Q.
        - change (nth_error (List.map (fun i => Z.of_nat i + 3) (List.seq 0 29)) (Z.to_nat k)
                          = Some (k + 3)).
          rewrite map_nth_error with (d := Z.to_nat k).
          + f_equal. lia.
          + erewrite nth_error_nth'. 2: rewrite seq_length; lia.
            f_equal. rewrite seq_nth by lia. reflexivity.
        - erewrite nth_error_nth' by lia. reflexivity.
      }

      replace (nth (Z.to_nat rs1) (word.of_Z 0 :: v0 :: v :: vals) default) with
              (getReg (regs initialH) rs1) in *.
      2: {
        unfold getReg.
        specialize (GetVal (rs1 - 3)). replace (rs1 - 3 + 3) with rs1 in GetVal by lia.
        assert (rs1 < 0 \/ rs1 = 0 \/ rs1 = 1 \/ rs1 = 2 \/ 3 <= rs1 < 32 \/ 32 <= rs1) as C
            by lia.
        repeat destruct C as [C | C];
          (destr ((0 <? rs1) && (rs1 <? 32)); try (exfalso; lia); []);
          try replace (Z.to_nat rs1) with 0%nat by lia;
          try replace (Z.to_nat rs1) with 1%nat by lia;
          try replace (Z.to_nat rs1) with 2%nat by lia;
          try replace (Z.to_nat rs1) with (S (S (S (Z.to_nat (rs1 - 3))))) by lia;
          try subst rs1;
          cbn [nth];
          unfold RegisterNames.sp, RegisterNames.ra in *;
          rewrite_match;
          try reflexivity.
        - rewrite <- GetVal by lia.
          erewrite nth_error_nth' by lia.
          reflexivity.
        - rewrite nth_overflow by lia. reflexivity.
      }
      replace (nth (Z.to_nat rs2) (word.of_Z 0 :: v0 :: v :: vals) default) with
              (getReg (regs initialH) rs2) in *.
      2: {
        unfold getReg.
        specialize (GetVal (rs2 - 3)). replace (rs2 - 3 + 3) with rs2 in GetVal by lia.
        assert (rs2 < 0 \/ rs2 = 0 \/ rs2 = 1 \/ rs2 = 2 \/ 3 <= rs2 < 32 \/ 32 <= rs2) as C
            by lia.
        repeat destruct C as [C | C];
          (destr ((0 <? rs2) && (rs2 <? 32)); try (exfalso; lia); []);
          try replace (Z.to_nat rs2) with 0%nat by lia;
          try replace (Z.to_nat rs2) with 1%nat by lia;
          try replace (Z.to_nat rs2) with 2%nat by lia;
          try replace (Z.to_nat rs2) with (S (S (S (Z.to_nat (rs2 - 3))))) by lia;
          try subst rs2;
          cbn [nth];
          unfold RegisterNames.sp, RegisterNames.ra in *;
          rewrite_match;
          try reflexivity.
        - rewrite <- GetVal by lia.
          erewrite nth_error_nth' by lia.
          reflexivity.
        - rewrite nth_overflow by lia. reflexivity.
      }
      rewrite !LittleEndian.combine_split.
      rewrite !sextend_width_nop by reflexivity.
      rewrite !Z.mod_small by apply word.unsigned_range.
      rewrite !word.of_Z_unsigned.
      ssplit.
      { unfold setReg.
        apply map.map_ext. intro k.
        repeat (rewrite ?map.get_put_dec, ?map.get_putmany_dec, ?map.get_of_list_Z_at).
        unfold List.Znth_error.
        assert ((k <= 0 \/ 32 <= k) \/ 0 < k < 32) as C by lia.
        unfold RegisterNames.ra, RegisterNames.sp, RegisterNames.t1 in *.
        destruct C as [C | C].
        { repeat match goal with
                 | |- context[if ?b then _ else _] => destr b; try (exfalso; lia); []
                 end.
          destr ((0 <? rd) && (rd <? 32)).
          { assert (0 < rd < 32) by lia.
            rewrite ?map.get_put_dec.
            repeat match goal with
                   | |- context[if ?b then _ else _] => destr b; try (exfalso; lia)
                   end.
            { eapply only_differ_get_unchanged.
              2: eapply only_differ_sym; exact OD'. 1: reflexivity.
              unfold union, singleton_set, elem_of, Registers.reg_class.caller_saved,
                     Registers.reg_class.get.
              intro A. destruct A. 1: lia.
              repeat match goal with
                   | H: context[if ?b then _ else _] |- _ =>
                       destr b; try (exfalso; lia); []
                     end.
              destr (k =? 0); contradiction. }
            rewrite (proj2 (nth_error_None _ (Z.to_nat (k - 3)))). 2: {
              unfold List.upd, List.upds.
              list_length_rewrites_without_sideconds_in_goal.
              lia.
            }
            eapply only_differ_get_unchanged.
            2: eapply only_differ_sym; exact OD'. 1: reflexivity.
            unfold union, singleton_set, elem_of, Registers.reg_class.caller_saved,
              Registers.reg_class.get.
            intro A. destruct A. 1: lia.
            repeat match goal with
                   | H: context[if ?b then _ else _] |- _ =>
                       destr b; try (exfalso; lia); []
                   end.
            destr ((28 <=? k) && (k <=? 31)); lia.
          }
          { assert (rd <= 0 \/ 32 <= rd) by lia.
            rewrite ?map.get_put_dec.
            repeat match goal with
                   | |- context[if ?b then _ else _] => destr b; try (exfalso; lia)
                   end.
            { eapply only_differ_get_unchanged.
              2: eapply only_differ_sym; exact OD'. 1: reflexivity.
              unfold union, singleton_set, elem_of, Registers.reg_class.caller_saved,
                     Registers.reg_class.get.
              intro A. destruct A. 1: lia.
              repeat match goal with
                   | H: context[if ?b then _ else _] |- _ =>
                       destr b; try (exfalso; lia); []
                     end.
              destr (k =? 0); contradiction. }
            rewrite (proj2 (nth_error_None _ (Z.to_nat (k - 3)))). 2: {
              unfold List.upd, List.upds.
              list_length_rewrites_without_sideconds_in_goal.
              lia.
            }
            eapply only_differ_get_unchanged.
            2: eapply only_differ_sym; exact OD'. 1: reflexivity.
            unfold union, singleton_set, elem_of, Registers.reg_class.caller_saved,
              Registers.reg_class.get.
            intro A. destruct A. 1: lia.
            repeat match goal with
                   | H: context[if ?b then _ else _] |- _ =>
                       destr b; try (exfalso; lia); []
                   end.
            destr ((28 <=? k) && (k <=? 31)); lia.
          }
        }

        (* Now we know that k is in range 1..31 *)
        destr ((0 <? rd) && (rd <? 32)).
        { assert (0 < rd < 32) by lia.
          rewrite ?map.get_put_dec.
          destr (rd =? k).
          { destr (2 =? k).
            { change (Z.to_nat 2) with 2%nat. cbn. reflexivity. }
            { destr (1 =? k).
              { change (Z.to_nat 1) with 1%nat. cbn. reflexivity. }
              { destr (k - 3 <? 0).
                1: exfalso; lia.
                rewrite List.nth_error_firstn by lia.
                rewrite List.nth_error_skipn.
                rewrite List.nth_error_upd_same_eq.
                1: reflexivity.
                1: listZnWords.
                lia.
              } } }
          { destr (2 =? k).
            { rewrite List.nth_upd_diff by lia.
              cbn. congruence. }
            { destr (1 =? k).
              { rewrite List.nth_upd_diff by lia.
                cbn. congruence. }
              { destr (k - 3 <? 0).
                1: exfalso; lia.
                rewrite List.nth_error_firstn by lia.
                rewrite List.nth_error_skipn.
                rewrite List.nth_error_upd_diff by lia.
                change (nth_error (word.of_Z 0 :: v0 :: v :: vals) (3 + Z.to_nat (k - 3)))
                       with (nth_error vals (Z.to_nat (k - 3))).
                rewrite GetVal by lia.
                replace (k - 3 + 3) with k by lia.
                unfold regs_initialized in RI.
                edestruct RI as [kv Gkv]. 2: {
                  rewrite Gkv. reflexivity.
                }
                lia.
              } } } }
        { destr (2 =? k).
          { rewrite List.nth_upd_diff by lia.
            cbn. congruence. }
          { destr (1 =? k).
            { rewrite List.nth_upd_diff by lia.
              cbn. congruence. }
            { destr (k - 3 <? 0).
              1: exfalso; lia.
              rewrite List.nth_error_firstn by lia.
              rewrite List.nth_error_skipn.
              rewrite List.nth_error_upd_diff by lia.
              change (nth_error (word.of_Z 0 :: v0 :: v :: vals) (3 + Z.to_nat (k - 3)))
                with (nth_error vals (Z.to_nat (k - 3))).
              rewrite GetVal by lia.
              replace (k - 3 + 3) with k by lia.
              unfold regs_initialized in RI.
              edestruct RI as [kv Gkv]. 2: rewrite Gkv; reflexivity.
              lia.
        } } } }
      { congruence. }
      { congruence. }
      { congruence. }
      { repeat step. }
      { repeat step. }
      { repeat step. }
      { repeat step. }
      { repeat step. }
      { repeat step. }
      { repeat step.
        eapply regs_initialized_putmany.
        repeat step. }
      { do 3 eexists. ssplit.
        { repeat step. }
        { repeat step. }
        2: {
          move ML at bottom.
          move MHI at bottom.
          instantiate (1 := (List.upd (word.of_Z 0 :: v0 :: v :: vals)
                                      (Z.to_nat rd)
                                      (word.mul (getReg (regs initialH) rs1)
                                         (getReg (regs initialH) rs2)))).
          cbn [seps]. eapply subst_split_bw. 1: eassumption.
          rewrite (truncated_scalar_unique' MHI).

          unfold handler_insts, asm_handler_insts.
          rewrite !(array_app (E := Instruction)).
          repeat match goal with
                 | |- context[List.length ?l] => let n := concrete_list_length l in
                                                 change (List.length l) with n
                 end.
          autorewrite with rew_word_morphism.
          repeat (repeat word_simpl_step_in_goal; repeat word_simpl_step_in_hyps; fwd).
          replace (pc initialH) with (pc initialL) in *.
          cbn [seps] in ML. use_sep_assumption.
          cancel.
        }
        { listZnWords. }
      }
    Unshelve.
    all: try solve [constructor].
  Qed. (* takes several minutes... *)
End Riscv.
