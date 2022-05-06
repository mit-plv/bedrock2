Require Import Coq.Strings.String.
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Lists.List. Import ListNotations.
Require Import coqutil.Word.Bitwidth32.
From bedrock2 Require Import Semantics BasicC32Semantics WeakestPrecondition ProgramLogic.
From coqutil Require Import Word.Properties Word.Interface Tactics.letexists.
Require Import riscv.Utility.MonadNotations.
Require Import riscv.Utility.FreeMonad.
Require Import riscv.Utility.RegisterNames.
Require riscv.Spec.PseudoInstructions.
Require riscv.Utility.InstructionCoercions.
Require Import riscv.Spec.Decode.
Require riscv.Spec.Execute.
Require Import riscv.Spec.Machine.
Require Import riscv.Platform.Memory.
Require Import riscv.Spec.CSRFile.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.RecordSetters.
Require Import coqutil.Decidable.
Require Import coqutil.Z.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.SeparationLogic.
Require Import bedrock2.Syntax.
Require Import bedrock2.ZnWords.
Require Import riscv.Utility.Encode.
Require Import riscv.Proofs.EncodeBound.
Require Import riscv.Proofs.DecodeByExtension.
Require Import riscv.Proofs.VerifyDecode.
Require Import riscv.Proofs.EncodeDecode.
Require Import riscv.Platform.MinimalCSRs.
Require Import riscv.Platform.MaterializeRiscvProgram.
Require Import riscv.Platform.MetricMinimalNoMul.
Require Import compiler.regs_initialized.
Require Import compiler.Registers.
Require compiler.NaiveRiscvWordProperties.
Require Import compilerExamples.SoftmulBedrock2.
Require compiler.Pipeline.
Require Import bedrock2.BasicC32Semantics.
Require Import bedrock2.SepBulletPoints. Local Open Scope sep_bullets_scope.
Require Import bedrock2.SepAutoArray bedrock2.SepAutoExports.

Section Riscv.
  Import bedrock2.BasicC32Semantics.
  Context {registers: map.map Z word}.
  Context {registers_ok: map.ok registers}.

  (* RISC-V Monad *)
  Local Notation M := (free riscv_primitive primitive_result).

  Local Hint Mode map.map - - : typeclass_instances.

  Instance RV32I_bitwidth: FlatToRiscvCommon.bitwidth_iset 32 RV32I.
  Proof. reflexivity. Qed.

  Ltac change_if_goal :=
    match goal with
    | |- context[if ?b then ?x else ?y] =>
        change (if b then x else y) with x || change (if b then x else y) with y
    end.

  Ltac change_if_hyp :=
    match goal with
    | H: context[if ?b then ?x else ?y] |- _ =>
        change (if b then x else y) with x in H || change (if b then x else y) with y in H
    end.

  Ltac decode_implication_pre :=
    intros *;
    cbv beta delta [decode];
    change (bitwidth RV32IM =? 64) with false;
    change (bitwidth RV32I =? 64) with false;
    repeat lazymatch goal with
           | x := bitSlice _ 25 26 |- _ =>
               (* shamtHi is the only field which another field depends on *)
               subst x
           | |- (let x := ?a in ?b) = ?c -> (let x' := ?a in @?b' x') = ?c' =>
               change (let x := a in (b = c -> b' x = c')); cbv beta; intro
           end;
    repeat change_if_goal;
    cbv zeta;
    let E := fresh "E" in intro E.

  Lemma decode_IM_I_to_I: forall i inst,
      decode RV32IM i = IInstruction inst ->
      decode RV32I  i = IInstruction inst.
  Proof.
    decode_implication_pre.
    destruct_one_match_hyp. 1: discriminate E.
    clearbody decodeI decodeM decodeCSR.
    subst resultI resultM resultCSR.
    clear -E0 E.
    destr (isValidI decodeI); destr (isValidM decodeM); destr (isValidCSR decodeCSR);
      cbn -[Z.gtb Z.of_nat] in *; subst;
      try discriminate; destruct_one_match; try (exfalso; Lia.lia);
      try congruence.
  Qed.

  Lemma decode_IM_Invalid_to_I: forall i z,
      decode RV32IM i = InvalidInstruction z ->
      decode RV32I  i = InvalidInstruction z.
  Proof.
    intros. rewrite <- decode_alt_correct in *. unfold decode_alt in *.
    pose proof (extensions_disjoint RV32IM i) as D.
    unfold decode_results in *.
    cbn in *.
    unfold decode_resultI, decode_resultM, decode_resultCSR in *.
    do 3 destruct_one_match_hyp;
    cbn [List.app List.length List.nth] in *;
    try congruence.
  Qed.

  Lemma decode_IM_M_to_Invalid_I: forall z minst,
      decode RV32IM z = MInstruction minst ->
      decode RV32I z = InvalidInstruction z.
  Proof.
    intros. rewrite <- decode_alt_correct in *. unfold decode_alt in *.
    pose proof (extensions_disjoint RV32IM z) as D.
    unfold decode_results in *.
    cbn in *.
    unfold decode_resultI, decode_resultM, decode_resultCSR in *.
    do 3 destruct_one_match_hyp;
    cbn [List.app List.length List.nth] in *;
    try congruence.
    exfalso. Lia.lia.
  Qed.

  Lemma decode_I_cases: forall z,
      (exists iinst, decode RV32I z = IInstruction iinst) \/
      (exists cinst, decode RV32I z = CSRInstruction cinst) \/
      (decode RV32I z = InvalidInstruction z).
  Proof.
    intros. rewrite <- decode_alt_correct in *. unfold decode_alt in *.
    pose proof (extensions_disjoint RV32I z) as D.
    unfold decode_results in *.
    cbn in *.
    unfold decode_resultI, decode_resultCSR in *.
    do 2 destruct_one_match_hyp;
    cbn [List.app List.length List.nth] in *;
    eauto.
  Qed.

  Lemma decode_IM_cases: forall z,
      (exists iinst, decode RV32IM z = IInstruction iinst) \/
      (exists minst, decode RV32IM z = MInstruction minst) \/
      (exists cinst, decode RV32IM z = CSRInstruction cinst) \/
      (decode RV32IM z = InvalidInstruction z).
  Proof.
    intros. rewrite <- decode_alt_correct in *. unfold decode_alt in *.
    pose proof (extensions_disjoint RV32IM z) as D.
    unfold decode_results in *.
    cbn in *.
    unfold decode_resultI, decode_resultM, decode_resultCSR in *.
    do 3 destruct_one_match_hyp;
    cbn [List.app List.length List.nth] in *;
    eauto.
  Qed.

  Lemma decode_Imul_I_to_I: forall i inst,
      mdecode i = IInstruction inst ->
      idecode i = IInstruction inst.
  Proof.
    unfold mdecode, idecode. intros.
    destruct_one_match_hyp. 1: discriminate. assumption.
  Qed.

  Lemma decode_IM_CSR_to_I: forall i inst,
      decode RV32IM i = CSRInstruction inst ->
      decode RV32I  i = CSRInstruction inst.
  Proof.
    intros. rewrite <- decode_alt_correct in *. unfold decode_alt in *.
    pose proof (extensions_disjoint RV32IM i) as D.
    unfold decode_results in *.
    cbn in *.
    unfold decode_resultI, decode_resultM, decode_resultCSR in *.
    do 3 destruct_one_match_hyp;
    cbn [List.app List.length List.nth] in *;
    eauto; try (exfalso; Lia.lia); try discriminate.
  Qed.

  (* To use the compiler correctness statement, we need to apply two transformation steps:
     1) Change decode from RV32IM to RV32I (lemma run1_IM_to_I)
     2) Change state representation from MetricRiscvMachine to State (with CSRs) *)

  (* valid_machine contains the extra condition no_M saying that all executable addresses
     are not an M instruction, which will only hold for certain input programs, and we
     will check it instruction-by-instruction for the compiled softmul handler program,
     in order to turn the compiler proof, which usually is about an execution on an RV32IM
     machine into a statement about an execution on an RV32I machine. *)
  Lemma run1_IM_to_I_run1: forall (initial: MetricRiscvMachine) post,
      Primitives.valid_machine initial ->
      GoFlatToRiscv.mcomp_sat (Run.run1 RV32IM) initial post ->
      word.unsigned initial.(getPc) mod 4 = 0 ->
      GoFlatToRiscv.mcomp_sat (Run.run1 RV32I) initial post.
  Proof.
    unfold Run.run1. cbn -[HList.tuple].
    unfold MinimalNoMul.no_M, MinimalNoMul.load.
    intros. fwd. split. 1: assumption.
    replace (decode RV32I (LittleEndian.combine 4 t)) with
      (decode RV32IM (LittleEndian.combine 4 t)). 1: assumption.
    clear H0p1.
    specialize (H0p0 eq_refl).
    specialize (H _ _ H0p0 H1 E).
    destruct (decode_IM_cases (LittleEndian.combine 4 t)) as [ C | [C | [C | C] ] ];
      fwd; rewrite C; symmetry.
    - eapply decode_IM_I_to_I. exact C.
    - exfalso. eapply H. exact C.
    - eapply decode_IM_CSR_to_I. exact C.
    - eapply decode_IM_Invalid_to_I. exact C.
  Qed.

  Local Hint Extern 3 (_ mod 4 = 0) => DivisibleBy4.solve_divisibleBy4 : div4db.

  Lemma run1_preserves_mod4_0: forall (initial: MetricRiscvMachine) post,
      word.unsigned initial.(getPc) mod 4 = 0 ->
      word.unsigned initial.(getNextPc) mod 4 = 0 ->
      GoFlatToRiscv.mcomp_sat (Run.run1 RV32IM) initial post ->
      GoFlatToRiscv.mcomp_sat (Run.run1 RV32IM) initial
       (fun final => post final /\
                     word.unsigned final.(getPc) mod 4 = 0 /\
                     word.unsigned final.(getNextPc) mod 4 = 0).
  Proof.
    unfold Run.run1. cbn -[HList.tuple]. unfold MinimalNoMul.load. intros.
    fwd. split. 1: assumption.
    only_destruct_RiscvMachine initial. record.simp.
    destruct (decode_IM_cases (LittleEndian.combine 4 t)) as [ C | [C | [C | C] ] ]; fwd;
      rewrite C in *.
    4: exact H1p1.
    all: match goal with
         | |- context[Execute.execute (_ ?inst)] => destruct inst
         end.
    all: unfold Execute.execute, ExecuteI.execute, ExecuteM.execute, ExecuteCSR.execute in *.
    all: cbn -[load_bytes] in *.
    all: unfold MinimalNoMul.load, MinimalNoMul.store, Monads.when in *;
      cbn -[load_bytes] in *.
    all: try assumption.
    all: try (split; [assumption|]).
    all: fwd.
    all: auto with div4db.
    all: repeat destruct_one_match.
    all: cbn -[load_bytes] in *.
    all: auto with div4db.
    all: split; [assumption|].
    all: try
      match goal with
      | H: negb _ = _ |- _ => apply Bool.negb_false_iff in H; fwd;
                              apply (f_equal word.unsigned) in H;
                              rewrite word.unsigned_modu_nowrap in H by ZnWords
      end;
      ZnWords.
  Qed.

  Lemma run1_IM_to_I: forall s post,
      runsTo (GoFlatToRiscv.mcomp_sat (Run.run1 RV32IM)) s post ->
      Primitives.valid_machine s ->
      word.unsigned s.(getPc) mod 4 = 0 ->
      word.unsigned s.(getNextPc) mod 4 = 0 ->
      runsTo (GoFlatToRiscv.mcomp_sat (Run.run1 RV32I )) s post.
  Proof.
    induction 1; intros.
    - eapply runsToDone. assumption.
    - eapply runsToStep with (midset := fun m => midset m /\ Primitives.valid_machine m
         /\ word.unsigned m.(getPc) mod 4 = 0 /\ word.unsigned m.(getNextPc) mod 4 = 0).
      + eapply run1_IM_to_I_run1. 1,3: assumption.
        eapply run1_preserves_mod4_0 in H. 2,3: assumption.
        eapply GoFlatToRiscv.mcomp_sat_weaken.
        2: eapply GoFlatToRiscv.run1_get_sane.
        2,3: eassumption.
        1: intros mach A; exact A.
        cbv beta. intros. fwd. auto.
      + intros. fwd. eapply H1; try assumption.
  Qed.

  Definition states_related(sH: MetricRiscvMachine)(sL: State): Prop :=
    sH.(getRegs) = sL.(regs) /\
    sH.(getPc) = sL.(pc) /\
    sH.(getNextPc) = sL.(nextPc) /\
    sH.(getMem) = sL.(MinimalCSRs.mem).
    (* no constraints on sH.(getXAddrs), sH.(getLog), sL.(log) *)

  Lemma change_state_rep_primitive: forall a sH sL postH,
      states_related sH sL ->
      interp_action a sH postH ->
      run_primitive a sL (fun a sL' =>
           exists sH', states_related sH' sL' /\ sL'.(csrs) = sL.(csrs) /\
                         sL'.(log) = sL.(log) /\ postH a sH')
        (fun _ => False).
  Proof.
    pose proof Radd_comm word.ring_theory.
    destruct a; intros; destruct sH as [sH logH]; destruct sH, sL;
      unfold states_related, getReg, interp_action in *;
      cbn -[Memory.load_bytes map.get] in *;
      unfold load, store, MinimalNoMul.load, MinimalNoMul.store in *;
      fwd; cbn -[Memory.load_bytes map.get] in *;
      try contradiction;
      try rewrite_match;
      try (eexists {| getMachine := {| getRegs := _ |} |});
      cbn -[map.get]; eauto 10.
  Qed.

  Lemma change_state_rep_free: forall A (m: M A) sH sL postH,
      states_related sH sL ->
      free.interp MetricMinimalNoMul.interp_action m sH postH ->
      free.interpret run_primitive m sL (fun a sL' =>
           exists sH', states_related sH' sL' /\ sL'.(csrs) = sL.(csrs) /\
                         sL'.(log) = sL.(log) /\ postH a sH')
        (fun _ => False).
  Proof.
    induction m; intros.
    - cbn in *.
      eapply weaken_run_primitive with (postA1 := fun _ => False). 2: auto.
      2: eapply change_state_rep_primitive; eassumption.
      cbv beta.
      intros. fwd. rewrite <- H2p1, <- H2p2. eapply H; eauto.
    - cbn in *. eauto.
  Qed.

  Definition run1(decoder: Z -> Instruction): M unit :=
    startCycle;;
    pc <- getPC;
    inst <- Machine.loadWord Fetch pc;
    Execute.execute (decoder (LittleEndian.combine 4 inst));;
    endCycleNormal.

  (* both the finish-postcondition and the abort-postcondition are set to `post`
     to make sure `post` holds in all cases: *)
  Definition mcomp_sat(m: M unit)(initial: State)(post: State -> Prop): Prop :=
    free.interpret (@run_primitive _ _ _ mem registers) m initial (fun tt => post) post.

  Lemma change_state_rep: forall (sH: MetricRiscvMachine) postH,
      runsTo (GoFlatToRiscv.mcomp_sat (Run.run1 RV32I)) sH postH ->
      sH.(getNextPc) = word.add sH.(getPc) (word.of_Z 4) ->
      forall sL, states_related sH sL ->
      runsTo (mcomp_sat (run1 idecode)) sL (fun sL' =>
         exists sH', states_related sH' sL' /\ sL'.(csrs) = sL.(csrs) /\
                     sL'.(log) = sL.(log) /\ postH sH').
  Proof.
    induction 1; intros.
    - eapply runsToDone. eauto.
    - eapply runsToStep with (midset := fun sL' =>
         exists sH', states_related sH' sL' /\ sL'.(csrs) = sL.(csrs) /\
                     sL'.(log) = sL.(log) /\ midset sH' /\
                     sH'.(getNextPc) = word.add sH'.(getPc) (word.of_Z 4)).
      + unfold mcomp_sat.
        replace (run1 idecode) with
          (startCycle;;
             (pc <- getPC;
              inst <- Machine.loadWord Fetch pc;
              Execute.execute (idecode (LittleEndian.combine 4 inst)));;
           endCycleNormal). 2: {
          unfold run1.
          unfold Monads.Bind, free.Monad_free.
          rewrite <-?free.bind_assoc. reflexivity.
        }
        unfold GoFlatToRiscv.mcomp_sat, Run.run1 in H.
        unfold Primitives.mcomp_sat, MetricMinimalNoMulPrimitivesParams in *.
        replace (pc <- getPC;
          inst <- Machine.loadWord Fetch pc;
          Execute.execute (decode RV32I (LittleEndian.combine_deprecated 4 inst));;
          endCycleNormal)
        with ((pc <- getPC;
          inst <- Machine.loadWord Fetch pc;
          Execute.execute (decode RV32I (LittleEndian.combine_deprecated 4 inst)));;
          endCycleNormal) in H. 2: {
          unfold Monads.Bind, free.Monad_free.
          rewrite <-?free.bind_assoc. reflexivity.
        }
        eapply free.interp_bind_ex_mid in H.
        2: eapply interp_action_weaken_post.
        destruct H as (pre_mid & A & B).
        eapply free.interpret_bind. 1: eapply weaken_run_primitive.
        unfold startCycle.
        unfold free.interpret at 1. unfold free.interpret_fix at 1.
        unfold free.interpret_body.
        unfold run_primitive at 1.
        eapply free.interpret_bind. 1: eapply weaken_run_primitive.
        eapply free.interpret_weaken_post.
        4: {
          eapply change_state_rep_free with (sH := initial). {
            clear -H2 H3. unfold states_related in *.
            destruct initial, getMachine, sL; record.simp.
            intuition congruence.
          }
          exact A.
        }
        1: eapply weaken_run_primitive.
        all: cbv beta; intros.
        2: contradiction.
        cbn.
        unfold states_related in H|-*. fwd.
        destruct sH' as [sH' mc]. destruct sH'. destruct s. unfold updatePc.
        record.simp. subst.
        move B at bottom.
        specialize (B _ _ Hp3). cbn in B. eexists. ssplit.
        7: exact B.
        all: try reflexivity.
        record.simp. ring.
      + cbv beta; intros.
        fwd. rewrite <- H4p1, <- H4p2. eauto.
  Qed.

  Definition instr(decoder: Z -> Instruction): sep_predicate mem Instruction :=
    fun (addr: word) (inst: Instruction) =>
    ex1 (fun z => sep (addr :-> z : truncated_scalar access_size.four)
                      (emp (decoder z = inst /\ 0 <= z < 2 ^ 32))).

  Lemma instr_IM_impl1_I: forall iinst addr,
      impl1 (addr :-> IInstruction iinst : instr mdecode)
            (addr :-> IInstruction iinst : instr idecode).
  Proof.
    unfold impl1, instr. intros.
    extract_ex1_and_emp_in H. fwd.
    extract_ex1_and_emp_in_goal.
    eauto using decode_Imul_I_to_I.
  Qed.
  Hint Resolve instr_IM_impl1_I : ecancel_impl.

  (* TODO move *)
  Lemma Proper_impl1_array : forall T (P Q: word->T->mem->Prop) p a l,
      (forall a e, impl1 (P a e) (Q a e)) ->
      impl1 (array P p a l) (array Q p a l).
  Proof.
    intros. revert dependent a; revert p.
    induction l; cbn [array]; eauto; intros; [reflexivity|].
    eapply Proper_sep_impl1; eauto.
  Qed.

  (* TODO move *)
  Lemma Proper_impl1_array_with_offset : forall T (P Q: word->T->mem->Prop) sz l a,
      (forall i e, List.nth_error l i = Some e ->
                   let a' := (word.add a (word.of_Z (Z.of_nat i * sz))) in
                   impl1 (P a' e) (Q a' e)) ->
      impl1 (array P (word.of_Z sz) a l) (array Q (word.of_Z sz) a l).
  Proof.
    induction l; cbn [array]; intros; [reflexivity|].
    rename a0 into addr.
    eapply Proper_sep_impl1.
    - specialize (H O). cbn in H. specialize (H _ eq_refl). rewrite add_0_r in H.
      exact H.
    - eapply IHl. cbv zeta. intros.
      specialize (H (S i)). cbn -[Z.of_nat] in H. specialize (H _ H0).
      eqapply H; f_equal; ZnWords.
  Qed.

  Lemma idecode_array_implies_program: forall addr insts,
      word.unsigned addr mod 4 = 0 ->
      impl1 (addr :-> insts : array (instr idecode) (word.of_Z 4))
            (program RV32IM addr insts).
  Proof.
    intros. eapply Proper_impl1_array_with_offset.
    intros.
    unfold instr, ptsto_instr, impl1, ex1.
    intros m Hm. fwd.
    eapply sep_emp_r in Hm. fwd.
    unfold idecode in *.
    rewrite encode_decode. 2: reflexivity. 2: assumption.
    repeat (eapply sep_emp_r; split).
    - assumption.
    - pose proof (verify_decode RV32I a eq_refl) as P.
      destruct P as [P | P].
      + left. unfold verify, verify_iset in *. destruct P.
        split. 1: assumption. destruct (decode RV32I a); intuition discriminate.
      + right. rewrite P. unfold valid_InvalidInstruction. eauto.
    - subst a'. DivisibleBy4.solve_divisibleBy4.
  Qed.

  Lemma of_list_word_at_implies_program: forall iset insts addr,
      Forall (fun inst => verify inst iset) insts ->
      word.unsigned addr mod 4 = 0 ->
      Z.of_nat (Datatypes.length (Pipeline.instrencode insts)) < 2 ^ 32 ->
      impl1 (eq (map.of_list_word_at addr (Pipeline.instrencode insts)))
            (SeparationLogic.program iset addr insts).
  Proof.
    unfold impl1. intros. subst. revert addr H0 H1. induction H; intros.
    - cbn. unfold emp. auto.
    - unfold program in *. eapply array_cons.
      unfold Pipeline.instrencode at 1. unfold Pipeline.instrencode in H2.
      cbn [List.flat_map] in *.
      change (flat_map
                (fun inst : Instruction =>
                   HList.tuple.to_list (LittleEndian.split_deprecated 4 (encode inst))) l)
        with (Pipeline.instrencode l) in *.
      rewrite List.app_length in *.
      rewrite HList.tuple.length_to_list in H2.
      unfold sep. do 2 eexists. ssplit.
      3: eapply IHForall.
      2: {
        unfold ptsto_instr.
        eapply sep_emp_r. split; [|assumption].
        eapply sep_emp_r. split; [|auto].
        unfold truncated_scalar, littleendian, ptsto_bytes.
        rewrite HList.tuple.to_list_of_list. change (bytes_per access_size.four) with 4%nat.
        eapply array1_iff_eq_of_list_word_at.
        1: typeclasses eauto.
        2: reflexivity.
        rewrite LittleEndianList.length_le_split. cbv. discriminate 1.
      }
      2: DivisibleBy4.solve_divisibleBy4. 2: ZnWords.
      rewrite LittleEndian.to_list_split in *.
      unfold map.split. split.
      + apply map.map_ext. intro a.
        repeat rewrite ?map.get_of_list_word_at, ?map.get_putmany_dec.
        destruct_one_match.
        * pose proof E as B.
          eapply List.nth_error_Some_bound_index in B.
          rewrite nth_error_app2. 2: {
            rewrite LittleEndianList.length_le_split.
            ZnWords.
          }
          rewrite <- E. f_equal. rewrite LittleEndianList.length_le_split. ZnWords.
        * match goal with
          | |- _ = ?r => destr r
          end.
          { rewrite <- E0. apply nth_error_app1.
            rewrite LittleEndianList.length_le_split.
            eapply nth_error_None in E.
            eapply List.nth_error_Some_bound_index in E0.
            rewrite LittleEndianList.length_le_split in E0.
            exact E0. }
          match goal with
          | |- ?l = _ => destr l; [|reflexivity]
          end.
          eapply List.nth_error_app_Some in E1.
          rewrite E0 in E1.
          destruct E1 as [C | C]; [discriminate C|].
          rewrite <- C.
          rewrite <- E.
          f_equal.
          eapply nth_error_None in E.
          eapply nth_error_None in E0.
          eapply List.nth_error_Some_bound_index in C.
          rewrite LittleEndianList.length_le_split in *.
          ZnWords.
      + unfold map.disjoint.
        intros a b1 b2 G1 G2.
        rewrite map.get_of_list_word_at in G1,G2.
        eapply List.nth_error_Some_bound_index in G1.
        eapply List.nth_error_Some_bound_index in G2.
        rewrite LittleEndianList.length_le_split in G1.
        ZnWords.
  Qed.

  Notation program d := (array (instr d) (word.of_Z 4)) (only parsing).

  Definition funimplsList := softmul :: rpmul.rpmul :: nil.
  Definition prog := map.of_list funimplsList.

  Lemma funs_valid: ExprImp.valid_funs (map.of_list funimplsList).
  Proof.
    unfold ExprImp.valid_funs, ExprImp.valid_fun.
    intros.
    set (funnames := (List.map fst funimplsList)). cbv in funnames.
    destruct (List.In_dec String.string_dec f funnames).
    - subst funnames. simpl in i.
      repeat destruct i as [i | i]; try contradiction; subst f; vm_compute in H; fwd; split;
        repeat constructor; intro C; simpl in C; intuition discriminate.
    - exfalso. apply n; clear n.  change funnames with (List.map fst funimplsList).
      clear funnames.
      generalize dependent funimplsList. induction l; intros.
      + simpl in H. discriminate.
      + destruct a. unfold map.of_list in H. rewrite map.get_put_dec in H.
        destruct_one_match_hyp.
        * fwd. subst. simpl. auto.
        * simpl. right. eapply IHl. exact H.
  Qed.

  Definition mul_insts_result := Pipeline.compile (fun _ _ _ _ => []) prog.

  Definition mul_insts_tuple: list Instruction * SortedListString.map Z * Z.
    let r := eval vm_compute in mul_insts_result in
    match r with
    | Result.Success ?p => exact p
    end.
  Defined.

  Definition mul_insts: list Instruction := Eval compute in fst (fst mul_insts_tuple).
  Definition mul_insts_fpos: SortedListString.map Z :=
    Eval compute in snd (fst mul_insts_tuple).
  Definition mul_insts_req_stack: Z := Eval compute in snd (mul_insts_tuple).

  Lemma mul_insts_result_eq:
    mul_insts_result = Result.Success (mul_insts, mul_insts_fpos, mul_insts_req_stack).
  Proof. vm_compute. reflexivity. Qed.

  Definition no_M_insts: list Instruction -> bool :=
    List.forallb (fun i => match i with
                           | MInstruction _ => false
                           | _ => true
                           end).

  Lemma verify_mul_insts : Forall (fun i => verify i RV32I) mul_insts.
  Proof.
    repeat (eapply Forall_cons || eapply Forall_nil).
    all : cbv; ssplit; trivial; try congruence.
  Qed.

  Lemma verify_not_Invalid: forall inst iset,
      verify inst iset ->
      match inst with
      | InvalidInstruction _ => False
      | _ => True
      end.
  Proof. intros. destruct inst; auto. cbv in H. apply H. Qed.

  Lemma In_word_seq: forall n (a start: word),
      In a (List.unfoldn (word.add (word.of_Z 1)) n start) <->
      word.unsigned (word.sub a start) < Z.of_nat n.
  Proof.
    induction n; cbn -[Z.of_nat]; intros; split; intros.
    - contradiction H.
    - ZnWords.
    - destruct H as [H | H].
      + ZnWords.
      + eapply IHn in H. ZnWords.
    - destr (word.unsigned start =? word.unsigned a).
      + left. ZnWords.
      + right. eapply IHn. ZnWords.
  Qed.

  Lemma no_M_from_I_sep: forall insts (mach: RiscvMachine) R,
      word.unsigned mach.(getPc) mod 4 = 0 ->
      sep (mach.(getPc) :-> insts : program idecode) R mach.(getMem) ->
      mach.(getXAddrs) = List.unfoldn (word.add (word.of_Z 1))
                                      (4 * Datatypes.length insts) mach.(getPc) ->
      List.Forall (fun inst => match inst with
                               | InvalidInstruction _ => False
                               | _ => True
                               end) insts ->
      MinimalNoMul.no_M mach.
  Proof.
    unfold MinimalNoMul.no_M. intros.
    destruct mach as [regs pc npc m xAddrs log].
    cbn -[load_bytes HList.tuple Nat.mul] in *.
    subst.
    revert dependent m. revert minst. revert a v pc H H2 H3 H4 R.
    clear log npc regs.
    induction insts; cbn -[load_bytes HList.tuple Nat.mul]; intros.
    - unfold isXAddr4 in H3. apply proj1 in H3. simpl in H3. contradiction H3.
    - pose proof H3 as XA. replace (4 * (S (List.length insts)))%nat
        with (S (S (S (S (4 * List.length insts))))) in H3 by Lia.lia.
      unfold isXAddr4, isXAddr1 in H3. apply proj1 in H3.
      cbn [List.unfoldn In] in H3.
      fwd.
      repeat destruct H3 as [H3 | H3]; try subst a0.
      { intro C. unfold idecode in *.
        eapply decode_IM_M_to_Invalid_I in C.
        apply sep_assoc in H0.
        unfold instr at 1 in H0. extract_ex1_and_emp_in H0.
        fwd.
        replace (LittleEndian.combine_deprecated 4 v) with z in C. {
          rewrite C in H2p0. exact H2p0.
        }
        pose proof load_four_of_sep as P.
        unfold scalar32, truncated_word, Memory.load, Memory.load_Z in P.
        change (bedrock2.Memory.load_bytes (bytes_per access_size.four))
               with (load_bytes (mem := mem) 4) in P.
        specialize P with (addr := pc) (m := m) (value := word.of_Z z).
        rewrite H5 in P.
        rewrite word.unsigned_of_Z_nowrap in P by assumption.
        specialize P with (1 := H0).
        apply Option.eq_of_eq_Some in P.
        unfold truncate_word, truncate_Z in P.
        rewrite LittleEndian.combine_eq.
        rewrite Z.land_ones in P by (cbv; discriminate 1).
        clear -P H0_emp0. apply (f_equal word.unsigned) in P.
        rewrite word.unsigned_of_Z_nowrap in P by apply LittleEndianList.le_combine_bound.
        etransitivity. 2: symmetry. 2: exact P. clear P.
        change (Z.of_nat (bytes_per access_size.four) * 8) with 32.
        ZnWords. }
      1-3: repeat match goal with
           | H: ?T |- _ => lazymatch T with
                           | word.unsigned _ mod 4 = 0 => fail
                           | _ => clear H
                           end
           end;
           exfalso;
           ZnWords.
      eapply IHinsts. 6: eassumption. 5: ecancel_assumption.
      all: try assumption.
      1: DivisibleBy4.solve_divisibleBy4.
      eapply In_word_seq in H3.
      unfold isXAddr4, isXAddr1. ssplit; eapply In_word_seq; try ZnWords.
  Qed.

  Lemma link_softmul_bedrock2: spec_of_softmul funimplsList.
  Proof.
    eapply softmul_ok. eapply rpmul.rpmul_ok.
  Qed.

  Lemma unfoldn_word_seq_add: forall n m (start: word),
      List.unfoldn (word.add (word.of_Z 1)) (n + m) start =
      List.unfoldn (word.add (word.of_Z 1)) n start ++
      List.unfoldn (word.add (word.of_Z 1)) m (word.add start (word.of_Z (Z.of_nat n))).
  Proof.
    induction n; intros.
    - word_simpl_step_in_goal. reflexivity.
    - cbn -[Z.of_nat]. f_equal. eqapply (IHn m (word.add start (word.of_Z 1))).
      + f_equal. ring.
      + f_equal; f_equal; ZnWords.
  Qed.

  Import FunctionalExtensionality PropExtensionality.

  Lemma of_list_app_eq[E: Type]: forall (l1 l2: list E),
      of_list (l1 ++ l2) = union (of_list l1) (of_list l2).
  Proof.
    intros. extensionality x. eapply propositional_extensionality.
    unfold of_list, union, elem_of. eapply in_app_iff.
  Qed.

  (* TODO move to bedrock2.footpr *)
  Lemma rearrange_footpr_subset_impl1: forall {key value : Type} {map : map.map key value}
                                        (P Q : map -> Prop) (A : key -> Prop),
      subset (footpr P) A -> impl1 P Q -> subset (footpr Q) A.
  Proof.
    unfold subset, impl1, footpr, footprint_underapprox, elem_of. intros.
    eapply H. intros. specialize (H0 _ H2). exact (H1 _ H0).
  Qed.

  Lemma mul_correct: forall initial a_regs regvals invalidIInst R (post: State -> Prop)
                            ret_addr stack_start stack_pastend rd rs1 rs2,
      word.unsigned initial.(pc) mod 4 = 0 ->
      initial.(nextPc) = word.add initial.(pc) (word.of_Z 4) ->
      map.get initial.(regs) RegisterNames.a0 = Some invalidIInst ->
      map.get initial.(regs) RegisterNames.a1 = Some a_regs ->
      map.get initial.(regs) RegisterNames.ra = Some ret_addr ->
      map.get initial.(regs) RegisterNames.sp = Some stack_pastend ->
      word.unsigned ret_addr mod 4 = 0 ->
      word.unsigned (word.sub stack_pastend stack_start) mod 4 = 0 ->
      regs_initialized initial.(regs) ->
      mdecode (word.unsigned invalidIInst) = MInstruction (Mul rd rs1 rs2) ->
      (* At the time of writing, mul_insts_req_stack = 17, so 68 bytes of stack
         are sufficient, but to be more robust agains future changes in the
         handler implementation, we require a bit more stack space *)
      128 <= word.unsigned (word.sub stack_pastend stack_start) ->
      <{ * a_regs :-> regvals : word_array
         * initial.(pc) :-> mul_insts : program idecode
         * LowerPipeline.mem_available stack_start stack_pastend
         * R }> initial.(MinimalCSRs.mem) /\
      List.length regvals = 32%nat /\
      (forall newMem newRegs,
        <{ * a_regs :-> List.upd regvals (Z.to_nat rd) (word.mul
                   (List.nth (Z.to_nat rs1) regvals default)
                   (List.nth (Z.to_nat rs2) regvals default)) : word_array
           * initial.(pc) :-> mul_insts : program idecode
           * LowerPipeline.mem_available stack_start stack_pastend
           * R }> newMem ->
        map.only_differ initial.(regs) reg_class.caller_saved newRegs ->
        regs_initialized newRegs ->
        post { initial with pc := ret_addr;
                            nextPc := word.add ret_addr (word.of_Z 4);
                            MinimalCSRs.mem := newMem;
                            regs := newRegs
                            (* log and csrs remain the same *) }) ->
      runsTo (mcomp_sat (run1 idecode)) initial post.
  Proof.
    intros.
    match goal with
    | H: _ /\ _ /\ _ |- _ => destruct H as (ML & rL & C)
    end.
    pose proof ML as ML'.
    destruct ML as (mH & mL & Sp & MH & ML).
    eapply runsTo_weaken.
    { eapply change_state_rep with (sH := {|
            (****************)
        getMachine := {|
          getRegs := initial.(regs);
          getPc := initial.(pc);
          getNextPc := word.add initial.(pc) (word.of_Z 4);
          getMem := initial.(MinimalCSRs.mem);
          getXAddrs := List.unfoldn (word.add (word.of_Z 1)) (4 * List.length mul_insts)
                                    initial.(pc);
          getLog := []
        |};
        getMetrics := MetricLogging.EmptyMetricLog
      |}).
      2: reflexivity.
      2: {
        unfold states_related; cbn -[array HList.tuple] in *.
        ssplit; try congruence.
      }
      eapply run1_IM_to_I.
            (************)
      2: {
        unfold Primitives.valid_machine, MetricMinimalNoMulPrimitivesParams.
        eapply no_M_from_I_sep with (insts := mul_insts);
        cbn -[array HList.tuple List.unfoldn List.length Nat.mul load_bytes].
        1: assumption.
        2: reflexivity.
        2: { eapply Forall_impl. 2: eapply verify_mul_insts.
             cbv beta. intros. eapply verify_not_Invalid. eassumption. }
        cbn [seps] in ML'. ecancel_assumption.
      }
      2: { cbn. assumption. }
      2: { cbn. DivisibleBy4.solve_divisibleBy4. }
      eapply (Pipeline.compiler_correct_wp (ext_spec := fun _ _ _ _ _ => False))
             (****************************)
             with (stack_lo := stack_start) (stack_hi := stack_pastend) (Rexec := emp True).
      5: {
        pose proof mul_insts_result_eq as P. unfold mul_insts_result in P.
        exact P.
      }
      { clear C.
        unfold FlatToRiscvCommon.compiles_FlatToRiscv_correctly.
        intros.
        match goal with
        | H: FlatImp.exec.exec _ (FlatImp.SInteract _ _ _) _ _ _ _ _ |- _ => inversion H
        end.
        contradiction. }
      { intros. reflexivity. }
      { exact funs_valid. }
      { constructor.
        - intro A. inversion A; try discriminate. eapply in_nil. eassumption.
        - constructor. 2: constructor. intro B. eapply in_nil. eassumption. }
      { pose proof link_softmul_bedrock2 as P.
                  (*********************)
        unfold spec_of_softmul in P.
        eapply P with (regvals := regvals) (R := emp True) (m := mH); clear P.
        ssplit; try eassumption.
        cbn [seps]. ecancel_assumption. }
      { reflexivity. }
      { unfold mul_insts_req_stack. change bytes_per_word with 4.
        Z.div_mod_to_equations. Lia.lia. }
      { assumption. }
      { cbn -[array HList.tuple Datatypes.length]. instantiate (1 := pc initial).
        ring. }
      { cbn -[array HList.tuple Datatypes.length]. eassumption. }
      { assumption. }
      { unfold LowerPipeline.arg_regs_contain.
        cbn -[array HList.tuple].
        unfold a0, a1 in *. rewrite_match.
        reflexivity. }
      { cbn -[array HList.tuple Datatypes.length]. reflexivity. }
      { unfold LowerPipeline.machine_ok. record.simp. ssplit.
        { exists mL, mH. ssplit.
          - eapply map.split_comm. assumption.
          - instantiate (1 := R).
            eapply sep_emp_True_r.
            use_sep_asm. refine (conj _ I). repeat ecancel_step_by_implication.
            unfold SeparationLogic.program.
            eapply idecode_array_implies_program.
            assumption.
          - reflexivity. }
        { match goal with
          | |- subset (footpr (sep ?p _)) _ => eapply rearrange_footpr_subset with (P :=  p)
          end.
          2: cancel.
          eapply rearrange_footpr_subset_impl1 with
            (P := (eq (map.of_list_word_at (pc initial)
                                           (Pipeline.instrencode mul_insts)))).
          { clear.
            unfold subset, footpr, footprint_underapprox, elem_of, of_list. intros.
            specialize (H _ eq_refl). fwd.
            rewrite map.get_of_list_word_at in H.
            eapply In_word_seq.
            eapply List.nth_error_Some_bound_index in H.
            change (Datatypes.length (Pipeline.instrencode mul_insts))
              with (4 * List.length mul_insts)%nat in H.
            forget (4 * List.length mul_insts)%nat as L.
            ZnWords. }
          { eapply of_list_word_at_implies_program. 2: assumption.
            2: vm_compute; reflexivity.
            eapply Forall_impl. 2: eapply verify_mul_insts.
            cbv beta. clear. unfold verify. intros i [V1 V2]. split. 1: exact V1.
            unfold verify_iset in *.
            destruct i; intuition congruence. } }
        { assumption. }
        { reflexivity. }
        { assumption. }
        { assumption. }
        { remember (List.unfoldn (word.add (word.of_Z 1)) (4 * Datatypes.length mul_insts)
                                 (pc initial)) as L.
          cbn.
          eapply no_M_from_I_sep; try record.simp.
          1: assumption.
          1: cbn[seps] in *; ecancel_assumption.
          1: exact HeqL.
          eapply Forall_impl. 2: eapply verify_mul_insts.
          cbv beta. intros. eapply verify_not_Invalid. eassumption. } } }
    { cbv beta. cbn -[array HList.tuple Datatypes.length].
      intros. fwd.
      specialize (C final.(MinimalCSRs.mem) final.(regs)).
      eqapply C; clear C.
      - unfold LowerPipeline.machine_ok, states_related in *; fwd.
        Import eplace.
        eplace (MinimalCSRs.mem final) with _ by (symmetry;eassumption).
        match goal with | |- _ ?m1 => match goal with | H:_ ?m2 |- _ =>
          unify m1 m2; refine (Morphisms.subrelation_refl impl1 _ _ _ m1 H) end end.
        etransitivity; [eapply Proper_sep_impl1; [reflexivity|] | ].
        { intros ? []. eassumption. }
        change (@word.of_Z ?wi ?wo 0) with (@default (@word.rep wi wo) _).
        unfold SeparationLogic.program.
        cancel.
        repeat ecancel_step_by_implication.
        intros m Hm; eapply sep_assoc, (proj1 (sep_emp_True_r _ _)), (proj1 (sep_emp_True_r _ _)) in Hm.
        case ML as (?&?&?&?&?&?).
        move H11 at bottom.
        unfold ptsto_instr, instr, truncated_scalar in *.

        assert (array_exmem : forall T (P:word->T->mem->Prop) p a l m,
          array P p a l m -> Forall (fun e => exists a m, P a e m) l).
        { clear.
          intros. revert dependent a; revert p; revert P; revert m.
          induction l; cbn [array]; eauto; intros.
          inversion H as (?&?&?&?&HI); eapply IHl in HI; eauto. }

        assert (array_Forall : forall T (Q:T->Prop) (P:word->T->mem->Prop) p a l m,
          Forall Q l -> array P p a l m -> array (fun a e => sep (emp (Q e)) (P a e)) p a l m).
        { clear.
          intros. revert dependent a; revert p; revert P; revert m.
          induction l; cbn [array]; eauto; intros.
          inversion H; subst; clear H.
          eapply sep_assoc, sep_emp_l; split; trivial.
          match goal with | |- _ ?m1 => match goal with | H:_ ?m2 |- _ =>
            unify m1 m2; refine (Morphisms.subrelation_refl impl1 _ _ _ m1 H) end end.
          eapply Proper_sep_impl1; [reflexivity|cbv[impl1];intros].
          eapply IHl; eauto. }

        eapply array_exmem in H11.
        eapply (Forall_and verify_mul_insts) in H11.
        epose proof (array_Forall _ _ _ _ _ _ _ H11 Hm).
        eapply Proper_impl1_array; try eassumption.

        intros ? ? mx Hmx.
        eapply sep_emp_l in Hmx; case Hmx as [[? [? [? [? Hmx]]]] Hmy].
        eapply sep_emp_r in Hmx; intuition idtac; subst.
        eapply sep_assoc in Hmy.
        eapply Proper_sep_iff1 in Hmy. 3: symmetry; eapply sep_emp_emp. 2: reflexivity.
        eapply sep_emp_r in Hmy as (?&?&?).

        eexists.
        eapply sep_emp_r.
        split.
        1:eassumption.
        split; eauto using encode_range.
        unfold idecode.
        rewrite DecodeEncode.decode_encode; trivial.

      - destruct sH' as [sH' lg]. destruct sH'.
        unfold states_related in *. record.simp. fwd.
        assumption.
      - unfold LowerPipeline.machine_ok, states_related in *. fwd.
        replace (regs final) with (getRegs sH').
        assumption.
      - unfold states_related, LowerPipeline.machine_ok in *. fwd.
        destruct final. destruct initial. record.simp. f_equal; try congruence. }
    Unshelve.
    all: try exact SortedListString.ok.
    all: try exact (NaiveRiscvWordProperties.naive_word_riscv_ok 5).
    all: try constructor.
  Qed.
End Riscv.

#[export] Hint Resolve instr_IM_impl1_I : ecancel_impl.
