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
Require Import riscv.Examples.SoftmulInsts.
Require Import riscv.Platform.MaterializeRiscvProgram.
Require Import compiler.UniqueSepLog.
Require Import compiler.regs_initialized.

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

Section Riscv.
  Context {word: Word.Interface.word 32}.
  Context {word_ok: word.ok word}.
  Context {Mem: map.map word byte}.
  Context {Mem_ok: map.ok Mem}.
  Context {registers: map.map Z word}.
  Context {registers_ok: map.ok registers}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  (* RISC-V Monad *)
  Local Notation M := (free riscv_primitive primitive_result).

  (*
  Definition mcomp_sat{A: Type}(m: M A)(initial: State)(post: A -> State -> Prop): Prop :=
      free.interpret run_primitive m initial post (fun _ => False).
   *)

  Local Hint Mode map.map - - : typeclass_instances.

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
      exists R i, Some initial.(mem) = R \*/ instr initial.(pc) i /\
                  verify i iset /\
                  mcomp_sat (Execute.execute i;; endCycleNormal) initial post.
  Proof.
    intros. apply invert_fetch0 in H. simp.
  Admitted.

  Definition store'(n: nat)(ctxid: SourceType)(a: word)(v: tuple byte n)(mach: State)(post: State -> Prop) :=
    exists (R: option Mem) (v_old: tuple byte n),
      Some mach.(mem) = R \*/ bytes a v_old /\ post { mach with mem := mmap.force (R \*/ bytes a v) }.

  Definition store_orig(n: nat)(ctxid: SourceType)(a: word) v (mach: State)(post: State -> Prop) :=
    match Memory.store_bytes n mach.(mem) a v with
    | Some m => post { mach with mem := m }
    | None => False
    end.

  Definition load'(n: nat)(ctxid: SourceType)(a: word)(mach: State)(post: tuple byte n -> State -> Prop): Prop :=
    exists (R: option Mem) (v: tuple byte n), Some mach.(mem) = R \*/ bytes a v /\ post v mach.

  Definition load_orig(n: nat)(ctxid: SourceType)(a: word)(mach: State)(post: tuple byte n -> State -> Prop) :=
    match Memory.load_bytes n mach.(mem) a with
    | Some v => post v mach
    | None => False
    end.

  Lemma build_fetch_one_instr: forall (initial: State) iset post (instr1 instr2: Instruction) (R: option Mem),
      Some initial.(mem) = R \*/ (instr initial.(pc) instr1) ->
      decode iset (encode instr1) = instr2 ->
      mcomp_sat (Execute.execute instr2;; endCycleNormal) initial post ->
      mcomp_sat (run1 iset) initial post.
  Proof.
    intros. subst instr2. unfold run1, mcomp_sat in *. cbn -[HList.tuple load_bytes].
    assert (load = load') as E by case TODO. rewrite E; clear E.
    unfold load'. do 2 eexists. split; try eassumption.
    rewrite LittleEndian.combine_split. rewrite word.unsigned_of_Z_nowrap. 2: apply encode_range.
    rewrite Z.mod_small. 2: apply encode_range.
    eassumption.
  Qed.

  Lemma array_split{T: Type}: forall elem size (l1 l2: list T) addr,
      array elem size addr (l1 ++ l2) =
      array elem size addr l1 \*/
      array elem size (word.add addr (word.mul size (word.of_Z (Z.of_nat (List.length l1))))) l2.
  Proof.
    induction l1; intros.
    - cbn [List.app array List.length Z.of_nat]. rewrite mmap.du_empty_l.
      replace (word.add addr (word.mul size (word.of_Z 0))) with addr by ring.
      reflexivity.
    - cbn [List.app array List.length]. rewrite IHl1. reify_goal.
      cancel_at 0%nat 0%nat. 1: reflexivity.
      cancel_at 0%nat 0%nat. 1: reflexivity.
      cancel_at 0%nat 0%nat. 2: reflexivity.
      f_equal.
      rewrite Nat2Z.inj_succ. (* <-- without this, lia checker fails, but it's already fixed on Coq master *)
      ZnWords.
  Qed.

  Lemma build_fetch: forall (initial: State) iset post addr p (instr1 instr2: Instruction) (R: option Mem),
      Some initial.(mem) = R \*/ (program addr p) ->
      let offset := word.unsigned (word.sub initial.(pc) addr) in
      offset mod 4 = 0 ->
      nth_error p (Z.to_nat (offset / 4)) = Some instr1 ->
      decode iset (encode instr1) = instr2 ->
      mcomp_sat (Execute.execute instr2;; endCycleNormal) initial post ->
      mcomp_sat (run1 iset) initial post.
  Proof.
    intros.
    edestruct nth_error_split as (p0 & p1 & ? & E). 1: eassumption.
    subst p.
    unfold program in *.
    rewrite array_split in H. cbn [array] in H.
    eapply build_fetch_one_instr; [|eassumption..].
    etransitivity. 1: eassumption.
    reify_goal.
    cancel_at 2%nat 1%nat. 2: reflexivity.
    rewrite E. f_equal. subst offset. ZnWords.
  Qed.

  Lemma decode_verify_iset: forall iset i, verify_iset (decode iset i) iset.
  Proof.
  Abort.

  Lemma decode_I_to_IM: forall i inst,
      decode RV32IM i = IInstruction inst ->
      decode RV32I  i = IInstruction inst.
  Proof.
  Abort.

  Lemma decode_CSR_to_IM: forall i inst,
      decode RV32IM i = CSRInstruction inst ->
      decode RV32I  i = CSRInstruction inst.
  Proof.
  Abort.

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
      Some r2.(mem) = Some r1.(mem) \*/
                      word_array (word.of_Z mscratch) stacktrash \*/
                      program (word.of_Z (mtvec_base * 4)) handler_insts /\
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
      unfold setReg in *. destr ((0 <? z) && (z <? 32))%bool;
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

  Lemma interpret_getRegister: forall (initial: State) (postF: word -> State -> Prop) (postA: State -> Prop) r,
      postF (getReg initial.(regs) r) initial ->
      free.interpret run_primitive (getRegister r) initial postF postA.
  Proof.
    intros. simpl. assumption.
  Qed.

  Lemma interpret_setRegister: forall (initial: State) (postF: unit -> State -> Prop)
                                      (postA: State -> Prop) r (v: word),
      postF tt { initial with regs ::= setReg r v } ->
      free.interpret run_primitive (setRegister r v) initial postF postA.
  Proof.
    intros. simpl. assumption.
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

  Lemma run_store: forall n addr (v_old v_new: tuple byte n) R (initial: State) (kind: SourceType)
                          (post: State -> Prop),
      Some initial.(mem) = R \*/ bytes addr v_old ->
      (forall m: Mem, Some m = R \*/ bytes addr v_new -> post { initial with mem := m }) ->
      MinimalCSRs.store n kind addr v_new initial post.
  Proof.
    intros. unfold store, store_bytes.
  Admitted.

  Lemma interpret_storeWord: forall addr (v_old v_new: tuple byte 4) R (initial: State)
                                    (postF: unit -> State -> Prop) (postA: State -> Prop),
      Some initial.(mem) = R \*/ bytes addr v_old ->
      (forall m, Some m = R \*/ bytes addr v_new -> postF tt {initial with mem := m}) ->
      free.interpret run_primitive (Machine.storeWord Execute addr v_new) initial postF postA.
  Proof.
    (* Note: some unfolding/conversion is going on here that we prefer to control with
       this lemma rather than to control each time we store a word *)
    intros. eapply run_store; eassumption.
  Qed.

  Lemma interpret_getPrivMode: forall (m: State) (postF: PrivMode -> State -> Prop) (postA: State -> Prop),
      postF Machine m -> (* we're always in machine mode *)
      free.interpret run_primitive getPrivMode m postF postA.
  Proof. intros. cbn -[map.get map.rep]. assumption. Qed.

  Ltac program_index l :=
    lazymatch l with
    | program _ _ :: _ => constr:(0%nat)
    | _ :: ?rest => let i := program_index rest in constr:(S i)
    end.

  Ltac cancel_program :=
    match goal with
    | |- mmap.dus ?LHS = mmap.dus ?RHS =>
      let i := program_index LHS in
      let j := program_index RHS in
      cancel_at i j; [reflexivity|]
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
    | |- _ => progress record.simp
    | |- _ => progress change (CSR.lookupCSR MScratch) with CSR.MScratch
    | |- _ => unfold map.set; rewrite !map.get_put_diff
                by (unfold RegisterNames.sp, RegisterNames.ra; congruence)
    | |- mcomp_sat (Monads.Bind _ _) _ _ => eapply mcomp_sat_bind
    | |- free.interpret run_primitive ?x _ _ _ =>
      lazymatch x with
      | Monads.Bind _ _ => eapply interpret_bind
      | free.bind _ _ => eapply interpret_bind
      | free.ret _ => rewrite free.interpret_ret
      | getPC => eapply interpret_getPC
      | setPC _ => eapply interpret_setPC
      | getRegister ?r =>
        lazymatch r with
        | 0 => eapply interpret_getRegister0
        | RegisterNames.zero => eapply interpret_getRegister0
        | _ => eapply interpret_getRegister
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
    | |- mcomp_sat endCycleNormal _ _ => eapply mcomp_sat_endCycleNormal
    | H: ?P |- ?P => exact H
    | |- mcomp_sat (run1 RV32I) _ _ =>
      eapply build_fetch; record.simp; cbn_MachineWidth;
        [ etransitivity; [eassumption|]; reify_goal; cancel_program; reflexivity
        | ZnWords
        | instr_lookup
        | apply decode_encode; vm_compute; intuition congruence
        | ]
    | |- _ => progress change (translate _ _ ?x)
                       with (@free.ret riscv_primitive primitive_result _ x)
    end.

  Local Hint Mode word.word - : typeclass_instances.

  (*
  Lemma save_regs_correct: forall start n R addr initial pcval stacktrash (post: State -> Prop),
      List.length stacktrash = n ->
      stackaddr = word.add spval (word.of_Z (4 * (Z.of_nat start))) ->
      Some initial.(mem) = R \*/ word_array addr stacktrash \*/
              program addr (map (fun r : Z => IInstruction (Sw RegisterNames.sp r (4 * r)))
                                (List.unfoldn (BinInt.Z.add 1) n start)) ->
      (forall m, Some m = R \*/ word_array addr
              program addr (map (fun r : Z => IInstruction (Sw RegisterNames.sp r (4 * r)))
                                (List.unfoldn (BinInt.Z.add 1) n start))) ->
      mcomp_sat (run1 iset) initial post.
   *)

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
    rewrite Hp0 in H2p6p3.
    pose proof (proj2 Hp1) as V.
    destruct i as [inst|inst|inst|inst|inst|inst|inst|inst|inst|inst] eqn: E;
      cbn in V; try (intuition congruence).
    - (* IInstruction *)
      subst.
      eapply @runsToStep with (midset := fun midL => exists midH, related midH midL /\ midset midH).
      + eapply build_fetch_one_instr.
        { etransitivity. 1: exact H2p6p3.
          reify_goal.
          cancel_at 1%nat 1%nat. { rewrite H2p1. reflexivity. }
          reflexivity.
        }
        { apply decode_encode.
          eapply verify_I_swap_extensions; try eassumption; reflexivity. }
        eapply mcomp_sat_preserves_related; eassumption.
      + intros midL. intros. simp. eapply H1; eassumption.
    - (* MInstruction *)
      (* fetch M instruction (considered invalid by RV32I machine) *)
      eapply runsToStep_cps.
      eapply build_fetch_one_instr. {
          etransitivity. 1: exact H2p6p3.
          reify_goal.
          cancel_at 1%nat 1%nat. {
            unfold instr, one. rewrite H2p1. reflexivity.
          }
          reflexivity.
      }
      { rewrite decode_M_on_RV32I_Invalid. 1: reflexivity.
        destruct (isValidM inst) eqn: EVM. 1: reflexivity.
        exfalso. clear -Hp1 EVM. destruct inst; cbn in *; try discriminate EVM.
        unfold verify in *. apply proj1 in Hp1. exact Hp1.
      }

      repeat step.
(*
      destruct stacktrash as [|zero_trash stacktrash]. 1: discriminate.
      destruct stacktrash as [|ra_trash stacktrash]. 1: discriminate.
      destruct stacktrash as [|sp_trash stacktrash]. 1: discriminate.
      cbn [word_array array] in *.
      change (Memory.bytes_per_word 32) with 4 in *.
      replace (word.add (word.add (word.add (word.of_Z mscratch) (word.of_Z 4)) (word.of_Z 4))
                        (word.of_Z 4))
        with (word.add (word.of_Z mscratch) (word.of_Z 12)) in * by ring.
      replace (word.add (word.add (word.of_Z mscratch) (word.of_Z 4)) (word.of_Z 4))
        with (word.add (word.of_Z mscratch) (word.of_Z 8)) in * by ring.

      (* step through handler code *)

      (* Csrrw sp sp MScratch *)
      eapply runsToStep_cps. repeat step.

      (* Sw sp zero 0        (needed if the instruction to be emulated reads register 0) *)
      eapply runsToStep_cps. repeat step.
      eapply interpret_storeWord.
      { repeat step.
        etransitivity. 1: eassumption.
        reify_goal.
        cancel_at 2%nat 1%nat. {
          unfold one. f_equal. ring.
        }
        cbn [mmap.dus].
        reflexivity.
      }
      match goal with
      | H: Some _ = _ |- _ => clear H
      end.
      repeat step.

      (* Sw sp ra 4 *)
      eapply runsToStep_cps. repeat step.
      eapply interpret_storeWord.
      { repeat step.
        etransitivity. 1: eassumption.
        reify_goal.
        cancel_at 2%nat 1%nat. {
          unfold one. f_equal.
        }
        cbn [mmap.dus].
        reflexivity.
      }
      match goal with
      | H: Some _ = _ |- _ => clear H
      end.
      repeat step.

      (* Csrr ra MScratch *)
      eapply runsToStep_cps. repeat step.

      (* Sw sp ra 8 *)
      eapply runsToStep_cps. repeat step.
      eapply interpret_storeWord.
      { repeat step.
        etransitivity. 1: eassumption.
        reify_goal.
        cancel_at 2%nat 1%nat. {
          unfold one. f_equal.
        }
        cbn [mmap.dus].
        reflexivity.
      }
      match goal with
      | H: Some _ = _ |- _ => clear H
      end.
      repeat step.

      (* save_regs3to31 *)
      (* Csrr t1 MTVal       t1 := the invalid instruction i that caused the exception *)
      (* Srli t1 t1 5        t1 := t1 >> 5                                             *)
      (* Andi s3 t1 (31*4)   s3 := i[7:12]<<2   // (rd of the MUL)*4                   *)
      (* Srli t1 t1 8        t1 := t1 >> 8                                             *)
      (* Andi s1 t1 (31*4)   s1 := i[15:20]<<2  // (rs1 of the MUL)*4                  *)
      (* Srli t1 t1 5        t1 := t1 >> 5                                             *)
      (* Andi s2 t1 (31*4)   s2 := i[20:25]<<2  // (rs2 of the MUL)*4                  *)
      (* Add s1 s1 sp        s1 := s1 + stack_start                                    *)
      (* Add s2 s2 sp        s2 := s2 + stack_start                                    *)
      (* Add s3 s3 sp        s3 := s3 + stack_start                                    *)
      (* Lw a1 s1 0          a1 := stack[s1]                                           *)
      (* Lw a2 s2 0          a2 := stack[s2]                                           *)
      (* softmul_insts       a3 := softmul(a1, a2)                                     *)
      (* Sw s3 a3 0          stack[s3] := a3                                           *)
      (* Csrr t1 MEPC *)
      (* Addi t1 t1 4 *)
      (* Csrw t1 MEPC        MEPC := MEPC + 4                                          *)
      (* restore_regs3to31 *)
      (* Lw ra sp 4 *)
      (* Csrr sp MScratch *)
      (* Mret *)

      (* ExecuteCSR.execute run_primitive *)

      (* instruction-specific handler code *)
      destruct inst.
      + (* Mul *)
        case TODO.
      + (* Mulh *)
        case TODO.
      + (* Mulhsu *)
        case TODO.
      + (* Mulhu *)
        case TODO.
      + (* Div *)
        case TODO.
      + (* Divu *)
        case TODO.
      + (* Rem *)
        case TODO.
      + (* Remu *)
        case TODO.
      + (* InvalidM *)
        case TODO.
    - (* CSRInstruction *)
      subst.
      eapply @runsToStep with (midset := fun midL => exists midH, related midH midL /\ midset midH).
      + eapply build_fetch_one_instr.
        { etransitivity. 1: exact H2p6p3.
          reify_goal.
          cancel_at 1%nat 1%nat. { rewrite H2p1. reflexivity. }
          reflexivity.
        }
        { apply decode_encode. eapply verify_CSR_swap_extensions. eassumption.
          (* "assumption" and relying on conversion would work too *) }
        eapply mcomp_sat_preserves_related; eassumption.
      + intros midL. intros. simp. eapply H1; eassumption.

    Unshelve.
    all: try exact (fun _ => True).
  Qed. *)
  Abort.

End Riscv.
