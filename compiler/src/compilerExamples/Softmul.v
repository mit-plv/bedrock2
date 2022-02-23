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
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Z.prove_Zeq_bitwise.
Require Import riscv.Utility.runsToNonDet.
Require riscv.Spec.PseudoInstructions.
Require Import compiler.SeparationLogic.
Require Import coqutil.Tactics.Simp.
Require Import bedrock2.Syntax.
Require Import bedrock2.ZnWords.
Require Import riscv.Platform.Run.
Require Import riscv.Utility.Encode.
Require Import riscv.Proofs.EncodeBound.
Require Import riscv.Platform.MinimalCSRs.
Require Import riscv.Proofs.InstructionSetOrder.
Require Import riscv.Proofs.DecodeEncodeProver.
Require Import riscv.Proofs.DecodeEncode.
Require riscv.Utility.InstructionCoercions.
Require Import riscv.Platform.MaterializeRiscvProgram.
Require Import compiler.regs_initialized.
Require Import compilerExamples.SoftmulCompile.
Require Import bedrock2.SepAutoArray bedrock2.SepAuto.

Axiom TODO: False.

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

Section WithRegisterNames.
  Import RegisterNames PseudoInstructions.
  Import InstructionCoercions. Open Scope ilist_scope.

  Definition save_regs3to31 :=
    @List.map Register Instruction (fun r => Sw sp r (4 * r)) (List.unfoldn (Z.add 1) 29 3).
  Definition restore_regs3to31 :=
    @List.map Register Instruction (fun r => Lw r sp (4 * r)) (List.unfoldn (Z.add 1) 29 3).

  (* TODO write encoder (so far there's only a decoder called CSR.lookupCSR) *)
  Definition MTVal    := 835.
  Remark MTVal_correct   : CSR.lookupCSR MTVal    = CSR.MTVal.    reflexivity. Qed.
  Definition MEPC     := 833.
  Remark MEPC_correct    : CSR.lookupCSR MEPC     = CSR.MEPC.     reflexivity. Qed.
  Definition MScratch := 832.
  Remark MScratch_correct: CSR.lookupCSR MScratch = CSR.MScratch. reflexivity. Qed.

  Definition handler_init := [[
    Csrrw sp sp MScratch;
    Sw sp zero 0;
    Sw sp ra 4;
    Csrr ra MScratch;
    Sw sp ra 8
  ]].

  Definition inc_mepc := [[
    Csrr t1 MEPC;
    Addi t1 t1 4;
    Csrw t1 MEPC
  ]].

  Definition handler_final := [[
    Lw ra sp 4;
    Csrr sp MScratch;
    Mret
  ]].

  Definition call_mul := [[
    Csrr a0 MTVal;  (* argument 0: value of invalid instruction *)
    Addi a1 sp 0;   (* argument 1: pointer to memory with register values before trap *)
    Jal ra (Z.of_nat (List.length inc_mepc + 29 + List.length handler_final) * 4)
  ]].

  Definition handler_insts :=
    handler_init ++ save_regs3to31 ++ call_mul ++ inc_mepc ++
       restore_regs3to31 ++ handler_final ++ mul_insts.
End WithRegisterNames.


Section Riscv.
  Context {word: Word.Interface.word 32}.
  Context {word_ok: word.ok word}.
  Context {Mem: map.map word byte}.
  Context {Mem_ok: map.ok Mem}.
  Context {registers: map.map Z word}.
  Context {registers_ok: map.ok registers}.

  Add Ring wring : (word.ring_theory (word := word))
      ((*This preprocessing is too expensive to be always run, especially if
         we do many ring_simplify in a sequence, in which case it's sufficient
         to run it once before the ring_simplify sequence.
         preprocess [autorewrite with rew_word_morphism],*)
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  (* RISC-V Monad *)
  Local Notation M := (free riscv_primitive primitive_result).

  (*
  Definition mcomp_sat{A: Type}(m: M A)(initial: State)(post: A -> State -> Prop): Prop :=
      free.interpret run_primitive m initial post (fun _ => False).
   *)

  Local Hint Mode map.map - - : typeclass_instances.

  Definition instr(iset: InstructionSet)(inst: Instruction)(addr: word): Mem -> Prop :=
    ex1 (fun z => sep (addr |-> truncated_scalar access_size.four z)
                      (emp (decode iset z = inst /\ 0 <= z < 2 ^ 32))).

  (* TODO more generic handling of ex1 *)
  Lemma instr_decode: forall {addr iset inst R m},
    (sep (addr |-> instr iset inst) R) m ->
    exists z, (sep (addr |-> truncated_scalar access_size.four z) R) m /\
              decode iset z = inst /\ 0 <= z < 2 ^ 32.
  Proof.
    intros.
    unfold instr, at_addr, ex1 in *.
    unfold sep, emp, map.split in *. fwd.
    exists a.
    split; auto.
    do 2 eexists. split; eauto.
    split; eauto.
    rewrite map.putmany_empty_r.
    assumption.
  Qed.

  Declare Scope array_abbrevs_scope.
  Open Scope array_abbrevs_scope.
  Notation "'program' iset" := (array (instr iset) 4) (at level 10): array_abbrevs_scope.

  (* both the finish-postcondition and the abort-postcondition are set to `post`
     to make sure `post` holds in all cases: *)
  Definition mcomp_sat(m: M unit)(initial: State)(post: State -> Prop): Prop :=
    free.interpret run_primitive m initial (fun tt => post) post.

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

  Lemma invert_fetch: forall initial post iset,
      mcomp_sat (run1 iset) initial post ->
      exists R i, seps [initial.(pc) |-> instr iset i; R] initial.(mem) /\
                  verify i iset /\
                  mcomp_sat (Execute.execute i;; endCycleNormal) initial post.
  Proof.
    intros. apply invert_fetch0 in H. simp.
  Admitted.

  Lemma build_fetch_one_instr:
    forall (initial: State) iset post (instr1: Instruction) (R: Mem -> Prop),
      seps [initial.(pc) |-> instr iset instr1; R] initial.(mem) ->
      mcomp_sat (Execute.execute instr1;; endCycleNormal) initial post ->
      mcomp_sat (run1 iset) initial post.
  Proof.
    intros. unfold run1, mcomp_sat in *. cbn -[HList.tuple load_bytes] in *.
    unfold load.
    change load_bytes with bedrock2.Memory.load_bytes.
    eapply instr_decode in H. destruct H as (z & H & ? & ?). subst instr1.
    erewrite load_bytes_of_sep; cycle 1. {
      unfold instr, at_addr, scalar, truncated_word, truncated_word,
        truncated_scalar, Scalars.truncated_scalar, Scalars.littleendian in H.
      cbn in H.
      unfold ptsto_bytes.ptsto_bytes in *.
      exact H.
    }
    eqapply H0. do 3 f_equal.
    rewrite LittleEndian.combine_eq.
    match goal with
    | |- context[LittleEndianList.le_combine ?x] =>
        replace x with (LittleEndianList.le_split 4 z)
    end.
    2: {
      etransitivity.
      1: symmetry. 1: eapply tuple.to_list_of_list.
      reflexivity.
    }
    rewrite LittleEndianList.le_combine_split.
    symmetry. apply Z.mod_small. assumption.
  Qed.

  Lemma decode_verify_iset: forall iset i, verify_iset (decode iset i) iset.
  Proof.
  Abort.

  Lemma decode_IM_I_to_I: forall i inst,
      decode RV32IM i = IInstruction inst ->
      decode RV32I  i = IInstruction inst.
  Proof.
  Admitted.

  Lemma decode_IM_M_to_Invalid_I: forall z minst,
      decode RV32IM z = MInstruction minst ->
      decode RV32I z = InvalidInstruction z.
  Proof.
  Admitted.

  Lemma decode_IM_CSR_to_I: forall i inst,
      decode RV32IM i = CSRInstruction inst ->
      decode RV32I  i = CSRInstruction inst.
  Proof.
  Admitted.

  Lemma instr_IM_impl1_I: forall iinst addr,
      impl1 (addr |-> instr RV32IM (IInstruction iinst))
            (addr |-> instr RV32I (IInstruction iinst)).
  Proof.
    unfold impl1. intros. eapply (fun x => conj x I) in H. eapply sep_emp_r in H.
    eapply instr_decode in H. fwd.
    eapply sep_emp_r in Hp0. fwd.
    unfold at_addr, instr, ex1. exists z. apply sep_emp_r.
    auto using decode_IM_I_to_I.
  Qed.
  Hint Resolve instr_IM_impl1_I : ecancel_impl.

  Lemma decode_verify: forall iset i, verify (decode iset i) iset.
  Proof.
  Abort. (* maybe not needed *)

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
    map.get r.(csrs) CSRField.MEPC <> None /\
    map.get r.(csrs) CSRField.MCauseCode <> None.

  Definition related(r1 r2: State): Prop :=
    r1.(regs) = r2.(regs) /\
    r1.(pc) = r2.(pc) /\
    r1.(nextPc) = r2.(nextPc) /\
    r1.(log) = r2.(log) /\
    r1.(csrs) = map.empty /\
    basic_CSRFields_supported r2 /\
    exists mtvec_base mscratch stacktrash,
      map.get r2.(csrs) CSRField.MTVecBase = Some mtvec_base /\
      map.get r2.(csrs) CSRField.MScratch = Some mscratch /\
      List.length stacktrash = 32%nat /\
      seps [eq r1.(mem);
            word.of_Z mscratch |-> word_array stacktrash;
            word.of_Z (mtvec_base * 4) |-> program RV32I handler_insts] r2.(mem) /\
      regs_initialized r2.(regs).

  Lemma related_preserves_load_bytes: forall n sH sL a w,
      related sH sL ->
      load_bytes n sH.(mem) a = Some w ->
      load_bytes n sL.(mem) a = Some w.
  Proof.
  Admitted.

  Lemma load_preserves_related: forall n c a initialH initialL postH,
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
      related initialH initialL ->
      store n c a v initialH postH ->
      store n c a v initialL
            (fun finalL => exists finalH, related finalH finalL /\ postH finalH).
  Proof.
    unfold store.
    cbn. intros.
    destruct_one_match_hyp. 2: contradiction.
    (* TODO separation logic/memory stuff *)
  Admitted.

  Lemma run_primitive_preserves_related: forall a initialH initialL postF postA,
      related initialH initialL ->
      run_primitive a initialH postF postA ->
      run_primitive a initialL
                    (fun res finalL => exists finalH, related finalH finalL /\ postF res finalH)
                    (fun finalL => exists finalH, related finalH finalL /\ postA finalH).
  Proof.
    intros. pose proof H as R.
    unfold related, basic_CSRFields_supported in H|-*.
    simp.
    destruct a; cbn [run_primitive] in *.
    - exists initialH. intuition (congruence || eauto 10).
    - exists { initialH with regs ::= setReg z r }. record.simp.
      unfold setReg in *. destr (Z.eq_dec z 0). 1: intuition (congruence || eauto 10).
      intuition (congruence || eauto 10 using preserve_regs_initialized_after_put).
    - eapply load_preserves_related; eauto.
    - eapply load_preserves_related; eauto.
    - eapply load_preserves_related; eauto.
    - eapply load_preserves_related; eauto.
    - eapply store_preserves_related; eauto.
    - eapply store_preserves_related; eauto.
    - eapply store_preserves_related; eauto.
    - eapply store_preserves_related; eauto.
    - contradiction.
    - contradiction.
    - contradiction.
    - simp. rewrite Hp4 in E. rewrite map.get_empty in E. discriminate E.
    - simp. rewrite Hp4 in E. rewrite map.get_empty in E. discriminate E.
    - eauto 10.
    - simp. eauto 10.
    - simp. eauto 10.
    - exists initialH.
      intuition (congruence || eauto 10).
    - eexists. ssplit; cycle -1. 1: eassumption. all: record.simp; try congruence. eauto 10.
    - eexists. unfold updatePc in *. ssplit; cycle -1. 1: eassumption.
      all: record.simp; try congruence. eauto 10.
    - eexists. unfold updatePc in *. ssplit; cycle -1. 1: eassumption.
      all: record.simp; try congruence. eauto 10.
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

(*
  Lemma go_exception: forall iset initial post R,
      R \*/
      runsTo (mcomp_sat (run1 iset)) initial(.(pc) := ini post.
      runsTo (mcomp_sat (run1 iset)) initial post.
*)

  Lemma mcomp_sat_endCycleNormal: forall (mach: State) (post: State -> Prop),
      post { mach with pc := mach.(nextPc); nextPc ::= word.add (word.of_Z 4) } ->
      mcomp_sat endCycleNormal mach post.
  Proof. intros. assumption. Qed.

  Lemma interpret_bind{T}(initial: State)(postF: T -> State -> Prop)(postA: State -> Prop) a b s:
    free.interpret run_primitive a s
                   (fun (x: T) s0 => free.interpret run_primitive (b x) s0 postF postA) postA ->
    free.interpret run_primitive (free.bind a b) s postF postA.
  Proof. eapply free.interpret_bind. apply weaken_run_primitive. Qed.

  Lemma interpret_getPC: forall (initial: State) (postF : word -> State -> Prop) (postA : State -> Prop),
      postF initial.(pc) initial ->
      free.interpret run_primitive getPC initial postF postA.
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
      r <> 0 ->
      map.get initial.(regs) r = Some v ->
      postF v initial ->
      free.interpret run_primitive (getRegister r) initial postF postA.
  Proof.
    intros. simpl. unfold getReg. destr (Z.eq_dec r 0). 1: exfalso; congruence. rewrite H0. assumption.
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
      r <> 0 ->
      postF tt { initial with regs ::= map.set r v } ->
      free.interpret run_primitive (setRegister r v) initial postF postA.
  Proof.
    intros. simpl. unfold setReg. destr (Z.eq_dec r 0). 1: exfalso; congruence. assumption.
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

  Lemma run_store: forall n addr (v_old v_new: tuple byte n) R (initial: State)
                          (kind: SourceType) (post: State -> Prop),
      seps [ptsto_bytes.ptsto_bytes n addr v_old; R] initial.(mem) ->
      (forall m: Mem, seps [ptsto_bytes.ptsto_bytes n addr v_new; R] m ->
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
      seps [addr |-> scalar v_old; R] initial.(mem) /\
      (forall m, seps [addr |-> scalar v_new; R] m -> postF tt { initial with mem := m }) ->
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
                              PseudoInstructions.Csrr, raiseExceptionWithInfo, updatePc
    | |- context[(@Monads.when ?M ?MM ?A ?B)] => change (@Monads.when M MM A B) with (@Monads.Return M MM _ tt)
    | |- context[(@Monads.when ?M ?MM ?A ?B)] => change (@Monads.when M MM A B) with B
    | |- _ => (*progress already embedded*) record.simp
    | |- _ => progress change (CSR.lookupCSR MScratch) with CSR.MScratch
    | |- _ => unfold Basics.compose, map.set; rewrite !map.get_put_diff
                by (unfold RegisterNames.sp, RegisterNames.ra; congruence)
    | |- mcomp_sat (Monads.Bind _ _) _ _ => eapply mcomp_sat_bind
    | |- free.interpret run_primitive ?x _ _ _ =>
      lazymatch x with
      | Monads.Bind _ _ => eapply interpret_bind
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
      end
    | |- RegisterNames.sp <> 0 => cbv; congruence
    | |- RegisterNames.ra <> 0 => cbv; congruence
    | |- 0 < RegisterNames.sp < 32 => do 2 split
    | |- 0 < RegisterNames.ra < 32 => do 2 split
    | |- map.get _ _ = Some _ => eassumption
    | |- map.get _ _ <> None => congruence
    | |- map.get (map.put _ ?x _) ?x = _ => eapply map.get_put_same
    | |- map.get (map.set ?x _ _) ?x = _ => eapply map.get_put_same
    | |- regs_initialized (map.put _ _ _) => eapply preserve_regs_initialized_after_put
    | |- regs_initialized (map.set _ _ _) => eapply preserve_regs_initialized_after_put
    | |- mcomp_sat endCycleNormal _ _ => eapply mcomp_sat_endCycleNormal
    | H: ?P |- ?P => exact H
    | |- mcomp_sat (run1 RV32I) _ _ =>
        eapply build_fetch_one_instr; try record.simp; cbn_MachineWidth;
        [ impl_ecancel_assumption
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
      0 < start -> (* <-- could probably be removed if needed *)
      map.getmany_of_list initial.(regs) (List.unfoldn (Z.add 1) n start) = Some vals ->
      seps [stackaddr |-> word_array oldvals;
        initial.(pc) |-> program RV32I
           (map (fun r => IInstruction (Sw RegisterNames.sp r (4 * r)))
                           (List.unfoldn (BinInt.Z.add 1) n start)); R] initial.(mem) ->
      (forall m: Mem,
         seps [stackaddr |-> word_array vals;
               initial.(pc) |-> program RV32I
                            (map (fun r => IInstruction (Sw RegisterNames.sp r (4 * r)))
                                 (List.unfoldn (Z.add 1) n start)); R] m ->
         runsTo (mcomp_sat (run1 RV32I)) { initial with mem := m;
           nextPc ::= word.add (word.of_Z (4 * Z.of_nat n));
           pc ::= word.add (word.of_Z (4 * Z.of_nat n)) } post) ->
      runsTo (mcomp_sat (run1 RV32I)) initial post.
  Proof.
    induction n; intros.
    - repeat word_simpl_step_in_hyps.
      destruct oldvals. 2: discriminate.
      destruct vals. 2: discriminate.
      match goal with
      | H: _ |- _ => eqapply H
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
      assert (start <> 0) by Lia.lia.
      eapply runsToStep_cps. repeat step.
      eapply IHn with (start := 1 + start) (oldvals := oldvals); try record.simp.
      + reflexivity.
      + eassumption.
      + reflexivity.
      + ring.
      + Lia.lia.
      + eassumption.
      + use_sep_asm. impl_ecancel.
        case TODO. (* separation logic automation *)
      + intros.
        eqapply H6. 2: {
          match goal with
          | H: nextPc _ = _ |- _ => rewrite H
          end.
          destruct initial; record.simp.
          f_equal; try ZnWords.
        }
        use_sep_asm.
        impl_ecancel. (* TODO should not instantiate R on lhs! *)
        case TODO. (* separation logic automation *)
  Qed.

  Lemma save_regs3to31_correct: forall R (initial: State) oldvals spval
                                  (post: State -> Prop),
      map.get initial.(regs) RegisterNames.sp = Some spval ->
      initial.(nextPc) = word.add initial.(pc) (word.of_Z 4) ->
      regs_initialized initial.(regs) ->
      (seps [word.add spval (word.of_Z 12) |-> with_len 29 word_array oldvals;
        initial.(pc) |-> program RV32I save_regs3to31; R] initial.(mem) /\
       forall m vals,
         map.getmany_of_list initial.(regs) (List.unfoldn (Z.add 1) 29 3) = Some vals ->
         seps [word.add spval (word.of_Z 12) |-> with_len 29 word_array vals;
               initial.(pc) |-> program RV32I save_regs3to31; R] m ->
         runsTo (mcomp_sat (run1 RV32I)) { initial with mem := m;
           nextPc ::= word.add (word.of_Z (4 * Z.of_nat 29));
           pc ::= word.add (word.of_Z (4 * Z.of_nat 29)) } post) ->
      runsTo (mcomp_sat (run1 RV32I)) initial post.
  Proof.
    unfold save_regs3to31. intros.
    assert (exists vals,
       map.getmany_of_list (regs initial) (List.unfoldn (Z.add 1) 29 3) = Some vals) as E
        by case TODO. (* from regs_initialized *)
    destruct E as [vals G].
    match goal with
    | H: _ /\ forall _, _ |- _ => destruct H as [HM HPost]
    end.
    replace (with_len 29 word_array oldvals)
      with (word_array oldvals) in HM by case TODO.
    assert (List.length oldvals = 29%nat) by case TODO.
    eapply save_regs_correct_aux with (start := 3); try eassumption; try reflexivity.
    intros.
    eapply HPost. 1: exact G.
    replace (with_len 29 word_array vals)
      with (word_array vals) by case TODO.
    assumption.
  Qed.

  Lemma softmul_correct: forall initialH initialL post,
      runsTo (mcomp_sat (run1 RV32IM)) initialH post ->
      related initialH initialL ->
      runsTo (mcomp_sat (run1 RV32I)) initialL (fun finalL =>
        exists finalH, related finalH finalL /\ post finalH).
  Proof.
    intros *. intros R. revert initialL. induction R; intros. {
      apply runsToDone. eauto.
    }
    unfold run1 in H.
    pose proof H2 as Rel.
    unfold related, basic_CSRFields_supported in H2.
    eapply invert_fetch in H. simp.
    rename initial into initialH.
    match goal with
    | H1: seps _ initialH.(mem), H2: seps _ initialL.(mem) |- _ =>
        rename H1 into MH, H2 into ML
    end.
    cbn [seps] in ML.
    epose proof (proj1 (sep_inline_eq _ _ initialL.(mem))) as ML'.
    especialize ML'. {
      exists initialH.(mem). split. 1: ecancel_assumption. 1: exact MH.
    }
    flatten_seps_in ML'. clear ML.
    pose proof (proj2 Hp1) as V.
    destruct i as [inst|inst|inst|inst|inst|inst|inst|inst|inst|inst] eqn: E;
      cbn in V; try (intuition congruence).
    - (* IInstruction *)
      subst.
      eapply @runsToStep with (midset := fun midL => exists midH, related midH midL /\ midset midH).
      + eapply build_fetch_one_instr.
        { replace initialH.(pc) with initialL.(pc) in ML'.
          impl_ecancel_assumption. }
        eapply mcomp_sat_preserves_related; eassumption.
      + intros midL. intros. simp. eapply H1; eassumption.
    - (* MInstruction *)
      (* fetch M instruction (considered invalid by RV32I machine) *)
      eapply runsToStep_cps.
      replace initialH.(pc) with initialL.(pc) in ML'.

      unfold instr in ML' at 2. unfold at_addr in ML' at 3.
      match type of ML' with
      | seps [?A; ?B; ?C; ?D] ?M => assert (sep C (seps [A; B; D]) M) as ML
            by (cbn [seps] in *; ecancel_assumption)
      end.
      clear ML'.
      eapply sep_ex1_l in ML. unfold ex1 in ML. destruct ML as [z ML].
      match type of ML with
      | sep (sep ?A ?B) ?C ?M => assert (sep B (sep A C) M) as ML'
            by (cbn [seps] in *; ecancel_assumption)
      end.
      clear ML.
      eapply sep_emp_l in ML'.
      destruct ML' as ((Ez & Bz) & ML).
      flatten_seps_in ML.

      eapply build_fetch_one_instr.
      { replace initialH.(pc) with initialL.(pc) in ML.
        unfold instr, at_addr, seps.
        eapply sep_ex1_l. unfold ex1. exists z. cbn [seps] in ML.
        refine (Morphisms.subrelation_refl impl1 _ _ _ (mem initialL) ML).
        cancel.
        impl_ecancel.
        unfold seps at 2.
        rewrite sep_comm.
        cancel.
        finish_impl_ecancel.
        split. 2: assumption.
        eapply decode_IM_M_to_Invalid_I.
        exact Ez. }

      repeat step.

      (* step through handler code *)

      (* Csrrw sp sp MScratch *)
      eapply runsToStep_cps. repeat step.

      (* Sw sp zero 0        (needed if the instruction to be emulated reads register 0) *)
      eapply runsToStep_cps. repeat step.

      (* Sw sp ra 4 *)
      eapply runsToStep_cps. repeat step.

      (* Csrr ra MScratch *)
      eapply runsToStep_cps. repeat step.

      (* Sw sp ra 8 *)
      eapply runsToStep_cps. repeat step.

      (* save_regs3to31 *)
      eapply save_regs3to31_correct; try record.simp.
      { repeat step. }
      { ZnWords. }
      { repeat step. }
      autorewrite with rew_word_morphism. repeat word_simpl_step_in_goal.

      unfold handler_insts in ML.
      rewrite !(array_app (E := Instruction)) in ML.
      repeat match type of ML with
             | context[List.length ?l] => let n := concrete_list_length l in
                                         change (List.length l) with n in ML
             end.
      autorewrite with rew_word_morphism in *.
      repeat (repeat word_simpl_step_in_hyps; fwd).
      flatten_seps_in ML.

      (* TODO automate *)

      put_cont_into_emp_seps.
      use_sep_asm.
      cancel_seps.
      once ecancel_step_by_implication.
      impl_ecancel_step_with_splitting.
      once ecancel_step_by_implication.
      finish_impl_ecancel.

Hint Extern 1 (?listL = ?listR1 ++ ?listR2 ++ ?listR3 /\ ?lenR1 = ?i /\ ?lenR2 = ?n) =>
    apply_in_hyps @map.getmany_of_list_length; rewrite List.length_unfoldn in *;
    is_evar listL; split; [ reflexivity | split; listZnWords ]
: merge_sepclause_sidecond.

      intro_new_mem.
      clear ML. rename H4 into ML.
      flatten_seps_in ML.
      repeat (repeat word_simpl_step_in_hyps; fwd).

      (* Csrr a0 MTVal       a0 := the invalid instruction i that caused the exception *)
      eapply runsToStep_cps. repeat step.

      case TODO.

      (*
      (* Addi a1 sp 0        a1 := pointer to registers *)
      eapply runsToStep_cps. repeat step.

      (* Jal ra ofs          call mul_insts *)
      eapply runsToStep_cps. repeat step.
      *)

    - (* CSRInstruction *)
      subst.
      eapply @runsToStep with (midset := fun midL => exists midH, related midH midL /\ midset midH).
      + unfold instr in ML' at 2. unfold at_addr in ML' at 3.
        match type of ML' with
        | seps [?A; ?B; ?C; ?D] ?M => assert (sep C (seps [A; B; D]) M) as ML
              by (cbn [seps] in *; ecancel_assumption)
        end.
        clear ML'.
        eapply sep_ex1_l in ML. unfold ex1 in ML. destruct ML as [z ML].
        match type of ML with
        | sep (sep ?A ?B) ?C ?M => assert (sep B (sep A C) M) as ML'
              by (cbn [seps] in *; ecancel_assumption)
        end.
        clear ML.
        eapply sep_emp_l in ML'.
        destruct ML' as ((Ez & Bz) & ML).
        flatten_seps_in ML.
        eapply build_fetch_one_instr.
        { replace initialH.(pc) with initialL.(pc) in ML.
          unfold instr, at_addr, seps.
          eapply sep_ex1_l. unfold ex1. exists z. cbn [seps] in ML.
          refine (Morphisms.subrelation_refl impl1 _ _ _ (mem initialL) ML).
          cancel.
          impl_ecancel.
          unfold seps at 2.
          rewrite sep_comm.
          cancel.
          finish_impl_ecancel.
          split. 2: assumption.
          eapply decode_IM_CSR_to_I.
          exact Ez. }
        eapply mcomp_sat_preserves_related; eassumption.
      + intros midL. intros. simp. eapply H1; eassumption.

    Unshelve.
    all: try exact (fun _ => True).
  Qed.
End Riscv.
