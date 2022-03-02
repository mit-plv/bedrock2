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
Require Import riscv.Platform.MinimalCSRs.
Require Import riscv.Platform.MaterializeRiscvProgram.
Require Import riscv.Platform.MetricMinimalNoMul.
Require Import compiler.regs_initialized.
Require Import compiler.Registers.
Require Import compilerExamples.SoftmulBedrock2.
Require compiler.Pipeline.
Require Import bedrock2.BasicC32Semantics.
Require Import bedrock2.SepAutoArray bedrock2.SepAuto.

(* TODO might need slight change to Naive.word to make these hold
   (shifts ignore high bits) *)
Axiom word_riscv_ok: RiscvWordProperties.word.riscv_ok BasicC32Semantics.word.

Section Riscv.
  Import bedrock2.BasicC32Semantics.
  Context {registers: map.map Z word}.
  Context {registers_ok: map.ok registers}.

  (* RISC-V Monad *)
  Local Notation M := (free riscv_primitive primitive_result).

  Local Hint Mode map.map - - : typeclass_instances.

  Instance RV32I_bitwidth: FlatToRiscvCommon.bitwidth_iset 32 RV32I.
  Proof. reflexivity. Qed.

  Lemma decode_IM_I_to_I: forall i inst,
      decode RV32IM i = IInstruction inst ->
      decode RV32I  i = IInstruction inst.
  Proof.
  Admitted.

  Lemma decode_IM_Invalid_to_I: forall i z,
      decode RV32IM i = InvalidInstruction z ->
      decode RV32I  i = InvalidInstruction z.
  Proof.
  Admitted.

  Lemma decode_IM_M_to_Invalid_I: forall z minst,
      decode RV32IM z = MInstruction minst ->
      decode RV32I z = InvalidInstruction z.
  Proof.
  Admitted.

  Lemma decode_IM_cases: forall z,
      (exists iinst, decode RV32IM z = IInstruction iinst) \/
      (exists minst, decode RV32IM z = MInstruction minst) \/
      (decode RV32IM z = InvalidInstruction z).
  Admitted.

  Lemma decode_Imul_I_to_I: forall i inst,
      mdecode i = IInstruction inst ->
      idecode i = IInstruction inst.
  Proof.
  Admitted.

  Lemma decode_IM_CSR_to_I: forall i inst,
      decode RV32IM i = CSRInstruction inst ->
      decode RV32I  i = CSRInstruction inst.
  Proof.
  Admitted.

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
      GoFlatToRiscv.mcomp_sat (Run.run1 RV32I) initial post.
  Proof.
    unfold Run.run1. cbn -[HList.tuple].
    unfold MinimalNoMul.no_M, MinimalNoMul.load.
    intros. fwd. split. 1: assumption.
    replace (decode RV32I (LittleEndian.combine 4 t)) with
      (decode RV32IM (LittleEndian.combine 4 t)). 1: assumption.
    clear H0p1.
    specialize (H0p0 eq_refl).
    specialize (H _ _ H0p0 E).
    destruct (decode_IM_cases (LittleEndian.combine 4 t)) as [ C | [C | C] ];
      fwd; rewrite C; symmetry.
    - eapply decode_IM_I_to_I. exact C.
    - exfalso. eapply H. exact C.
    - eapply decode_IM_Invalid_to_I. exact C.
  Qed.

  Lemma run1_IM_to_I: forall s post,
      runsTo (GoFlatToRiscv.mcomp_sat (Run.run1 RV32IM)) s post ->
      Primitives.valid_machine s ->
      runsTo (GoFlatToRiscv.mcomp_sat (Run.run1 RV32I )) s post.
  Proof.
    induction 1; intros.
    - eapply runsToDone. assumption.
    - eapply runsToStep with (midset := fun m => midset m /\ Primitives.valid_machine m).
      + eapply run1_IM_to_I_run1. 1: assumption.
        eapply GoFlatToRiscv.mcomp_sat_weaken.
        2: eapply GoFlatToRiscv.run1_get_sane.
        2,3: eassumption.
        1: intros mach A; exact A.
        intros. fwd. auto.
      + intros. fwd. eapply H1; assumption.
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
    pc <- getPC;
    inst <- Machine.loadWord Fetch pc;
    Execute.execute (decoder (LittleEndian.combine 4 inst));;
    endCycleNormal.

  (* both the finish-postcondition and the abort-postcondition are set to `post`
     to make sure `post` holds in all cases: *)
  Definition mcomp_sat(m: M unit)(initial: State)(post: State -> Prop): Prop :=
    free.interpret run_primitive m initial (fun tt => post) post.

  Lemma change_state_rep: forall sH postH,
      runsTo (GoFlatToRiscv.mcomp_sat (Run.run1 RV32I)) sH postH ->
      forall sL, states_related sH sL ->
      runsTo (mcomp_sat (run1 idecode)) sL (fun sL' =>
         exists sH', states_related sH' sL' /\ sL'.(csrs) = sL.(csrs) /\
                     sL'.(log) = sL.(log) /\ postH sH').
  Proof.
    induction 1; intros.
    - eapply runsToDone. eauto.
    - eapply runsToStep.
      + unfold mcomp_sat.
        eapply free.interpret_weaken_post.
        4: {
          eapply change_state_rep_free. 1: eassumption.
          unfold GoFlatToRiscv.mcomp_sat, Primitives.mcomp_sat,
                 MetricMinimalNoMulPrimitivesParams in *.
          exact H.
        }
        1: eapply weaken_run_primitive.
        all: cbv beta; intros.
        2: contradiction.
        exact H3.
      + cbv beta; intros.
        fwd. rewrite <- H3p1, <- H3p2. eauto.
  Qed.

  Definition instr(decoder: Z -> Instruction)(inst: Instruction)(addr: word): mem -> Prop :=
    ex1 (fun z => sep (addr |-> truncated_scalar access_size.four z)
                      (emp (decoder z = inst /\ 0 <= z < 2 ^ 32))).

  (* TODO more generic handling of ex1 *)
  Lemma instr_decode: forall {addr decoder inst R m},
    (sep (addr |-> instr decoder inst) R) m ->
    exists z, (sep (addr |-> truncated_scalar access_size.four z) R) m /\
              decoder z = inst /\ 0 <= z < 2 ^ 32.
  Proof.
    intros.
    unfold instr, at_addr, ex1 in *.
    unfold sep, emp, map.split in *. fwd.
    exists a.
    split; auto.
    do 2 eexists. split; eauto.
  Qed.

  Lemma instr_IM_impl1_I: forall iinst addr,
      impl1 (addr |-> instr mdecode (IInstruction iinst))
            (addr |-> instr idecode (IInstruction iinst)).
  Proof.
    unfold impl1. intros. eapply (fun x => conj x I) in H. eapply sep_emp_r in H.
    eapply instr_decode in H. fwd.
    eapply sep_emp_r in Hp0. fwd.
    unfold at_addr, instr, ex1. exists z. apply sep_emp_r.
    auto using decode_Imul_I_to_I.
  Qed.
  Hint Resolve instr_IM_impl1_I : ecancel_impl.

  Lemma idecode_array_implies_program: forall addr insts,
      impl1 (addr |-> array (instr idecode) 4 insts)
            (program RV32IM addr insts).
  Proof.
  Admitted.

  Declare Scope array_abbrevs_scope.
  Open Scope array_abbrevs_scope.
  Notation "'program' d" := (array (instr d) 4) (at level 10): array_abbrevs_scope.

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

  (* TODO implement in bedrock2 and compile to riscv, and also need to prove that
     programs running on the RISC-V machine used by the compiler (without CSRs)
     also run correctly on a RISC-V machine with CSRs and a different state type. *)
  Definition mul_insts_result := Pipeline.compile (fun _ _ _ _ => []) prog.

  Definition mul_insts_tuple: list Instruction * SortedListString.map (nat * nat * Z) * Z.
    let r := eval vm_compute in mul_insts_result in
    match r with
    | Result.Success ?p => exact p
    end.
  Defined.

  Definition mul_insts: list Instruction := Eval compute in fst (fst mul_insts_tuple).
  Definition mul_insts_fpos: SortedListString.map (nat * nat * Z) :=
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

  Lemma no_M_from_I_sep: forall (mach: RiscvMachine) insts R,
      sep (mach.(getPc) |-> program idecode insts) R mach.(getMem) ->
      mach.(getXAddrs) = List.unfoldn (word.add (word.of_Z 1))
                                      (4 * Datatypes.length insts) mach.(getPc) ->
      MinimalNoMul.no_M mach.
  Admitted.

  Lemma link_softmul_bedrock2: spec_of_softmul funimplsList.
  Proof.
    eapply softmul_ok. eapply rpmul.rpmul_ok.
  Qed.

  Lemma array_footpr_subset_unfoldn[V: Type]: forall addr elem sz (vs: list V),
      (forall a v, subset (footpr (elem a v))
             (of_list (List.unfoldn (word.add (word.of_Z 1)) (Z.to_nat sz) a))) ->
      subset (footpr (Array.array elem (word.of_Z sz) addr vs))
             (of_list (List.unfoldn (word.add (word.of_Z 1))
                                    (Z.to_nat sz * List.length vs) addr)).
  Admitted.

  Lemma ptsto_instr_subset_unfoldn: forall (a : word) (v : Instruction),
      subset (footpr (ptsto_instr RV32IM a v))
             (of_list (List.unfoldn (word.add (word.of_Z 1)) (Z.to_nat 4) a)).
  Admitted.

  Axiom TODO: False.

  (* TODO will need some stack space *)
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
      seps [a_regs |-> with_len 32 word_array regvals;
            initial.(pc) |-> program idecode mul_insts;
            LowerPipeline.mem_available stack_start stack_pastend;
            R] initial.(MinimalCSRs.mem) /\
      (forall newMem newRegs,
        seps [a_regs |-> with_len 32 word_array (List.upd regvals (Z.to_nat rd) (word.mul
                   (List.nth (Z.to_nat rs1) regvals default)
                   (List.nth (Z.to_nat rs2) regvals default)));
              initial.(pc) |-> program idecode mul_insts;
              LowerPipeline.mem_available stack_start stack_pastend;
              R] newMem ->
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
    | H: _ /\ _ |- _ => destruct H as [ML C]
    end.
    pose proof ML as ML'.
    destruct ML as (mH & mL & Sp & MH & ML).
    eapply runsTo_weaken.
    { eapply change_state_rep with (sH := {|
            (****************)
        getMachine := {|
          getRegs := initial.(regs);
          getPc := initial.(pc);
          getNextPc := initial.(nextPc);
          getMem := initial.(MinimalCSRs.mem);
          getXAddrs := List.unfoldn (word.add (word.of_Z 1)) (4 * List.length mul_insts)
                                    initial.(pc);
          getLog := []
        |};
        getMetrics := MetricLogging.EmptyMetricLog
      |}).
      2: {
        unfold states_related; cbn -[array HList.tuple] in *.
        ssplit; congruence.
      }
      eapply run1_IM_to_I.
            (************)
      2: {
        unfold Primitives.valid_machine, MetricMinimalNoMulPrimitivesParams.
        eapply no_M_from_I_sep with (insts := mul_insts);
        cbn -[array HList.tuple List.unfoldn List.length Nat.mul load_bytes].
        2: reflexivity. cbn [seps] in ML'. ecancel_assumption.
      }
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
        unfold with_len, with_pure, at_addr in MH.
        eapply sep_emp_r in MH. destruct MH as [MH L].
        ssplit; try eassumption.
        cbn [seps]. unfold at_addr. ecancel_assumption. }
      { reflexivity. }
      { unfold mul_insts_req_stack. change bytes_per_word with 4.
        Z.div_mod_to_equations. Lia.lia. }
      { assumption. }
      { cbn -[array HList.tuple Datatypes.length]. instantiate (1 := pc initial).
        ring. }
      { cbn -[array HList.tuple Datatypes.length]. eassumption. }
      { assumption. }
      { cbn -[array HList.tuple Datatypes.length]. unfold a0, a1 in *. rewrite_match.
        reflexivity. }
      { cbn -[array HList.tuple Datatypes.length]. reflexivity. }
      { unfold LowerPipeline.machine_ok. record.simp. ssplit.
        { exists mL, mH. ssplit.
          - eapply map.split_comm. assumption.
          - match goal with
            | |- sep (sep (sep ?A ?B) ?C) ?D mL =>
                enough (seps [A; B; C; D] mL) as E
            end.
            1: cbn [seps] in E; ecancel_assumption.
            instantiate (1 := R).
            (* TODO weird Notation aliasing because program is a keyword *)
            match goal with
            | |- seps (?p _ _ _ _ _ _ :: _) _ => unfold p
            end.
            use_sep_asm. impl_ecancel.
            cbn [seps].
            eapply idecode_array_implies_program.
          - reflexivity. }
        { match goal with
          | |- subset (footpr (sep ?p _)) _ => eapply rearrange_footpr_subset with (P :=  p)
          end.
          2: cancel.
          eapply array_footpr_subset_unfoldn.
          eapply ptsto_instr_subset_unfoldn. }
        { assumption. }
        { assumption. }
        { assumption. }
        { assumption. }
        { remember (List.unfoldn (word.add (word.of_Z 1)) (4 * Datatypes.length mul_insts)
                                 (pc initial)) as L.
          cbn.
          eapply no_M_from_I_sep; record.simp.
          1: cbn[seps] in *; ecancel_assumption.
          exact HeqL. } } }
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
        { intros ? []; eassumption. }
        unfold "|->", with_len, with_pure; cbn [seps]; reify_goal; impl_ecancel; cbn [seps].
        intros m Hm; eapply sep_assoc, (proj1 (sep_emp_True_r _ _)), (proj1 (sep_emp_True_r _ _)) in Hm.
        eapply sep_emp_l; split; eauto with ecancel_impl.
        { rewrite List.upd_length.
          unfold with_len, with_pure, "|->" in MH. eapply sep_emp_r in MH; intuition eauto. }
        cbn [seps] in ML. case ML as (?&?&?&?&?&?).
        unfold "|->" in *. move H11 at bottom.
        unfold "program" in *.
        match type of Hm with ?f _ _ _ _ _ _ _ => unfold f in * end.
        unfold ptsto_instr, instr, truncated_scalar, "|->" in *.

        Import Scalars Array.

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

        assert (Proper_impl1_array :
          forall T (P Q:word->T->mem->Prop) p a l,
          (forall a e, impl1 (P a e) (Q a e)) -> impl1 (array P p a l) (array Q p a l)).
        { clear.
          intros. revert dependent a; revert p.
          induction l; cbn [array]; eauto; intros; [reflexivity|].
          eapply Proper_sep_impl1; eauto. }

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
    all: try exact word_riscv_ok.
    all: try constructor.
  Qed.

  (* Needed if the handler wants to handle the case where the instruction is not
     a multiplication: *)
  Lemma mul_correct_2: forall initial a_regs regvals invalidIInst R (post: State -> Prop),
      initial.(nextPc) = word.add initial.(pc) (word.of_Z 4) ->
      map.get initial.(regs) RegisterNames.a0 = Some invalidIInst ->
      map.get initial.(regs) RegisterNames.a1 = Some a_regs ->
      seps [a_regs |-> word_array regvals; initial.(pc) |-> program idecode mul_insts; R]
           initial.(MinimalCSRs.mem) /\
      (forall final,
        ((* case 1: It was not the Mul instruction *)
         (map.get final.(regs) RegisterNames.a0 = Some (word.of_Z 0) /\
          (forall rd rs1 rs2, decode RV32IM (word.unsigned invalidIInst) <>
                                MInstruction (Mul rd rs1 rs2)) /\
          seps [a_regs |-> word_array regvals;
                initial.(pc) |-> program idecode mul_insts; R] final.(MinimalCSRs.mem))
         \/ (* case 2: It was the Mul instruction *)
         (exists ans rd rs1 rs2 v1 v2,
          map.get final.(regs) RegisterNames.a0 = Some ans /\
          word.unsigned ans <> 0 /\
          decode RV32IM (word.unsigned invalidIInst) = MInstruction (Mul rd rs1 rs2) /\
          nth_error regvals (Z.to_nat rs1) = Some v1 /\
          nth_error regvals (Z.to_nat rs2) = Some v2 /\
          seps [a_regs |-> word_array (List.upd regvals (Z.to_nat rd) (word.mul v1 v2));
               initial.(pc) |-> program idecode mul_insts; R] final.(MinimalCSRs.mem))) ->
        (* In common: *)
        final.(pc) = word.add initial.(pc) (word.mul (word.of_Z 4)
                           (word.of_Z (Z.of_nat (List.length mul_insts)))) ->
        final.(nextPc) = word.add final.(pc) (word.of_Z 4) ->
        post final) ->
      runsTo (mcomp_sat (run1 idecode)) initial post.
  Admitted.
End Riscv.

#[export] Hint Resolve instr_IM_impl1_I : ecancel_impl.
