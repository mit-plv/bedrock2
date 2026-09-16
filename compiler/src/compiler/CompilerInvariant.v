Require Import coqutil.Tactics.rewr.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Bitwidth coqutil.Word.Properties.
Require Import coqutil.Byte.
Require Import riscv.Utility.bverify.
Require Import riscv.Spec.LeakageOfInstr.
Require Import bedrock2.Array.
Require Import bedrock2.Map.SeparationLogic.
Require Import compiler.SeparationLogic.
Require Import coqutil.Tactics.Simp.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import compiler.LowerPipeline.
Require Import compiler.Pipeline.
Require Import compiler.ExprImpEventLoopSpec.
Require Import compiler.ToplevelLoop.
Require Import coqutil.Semantics.OmniSmallstepCombinators.

(* TODO decide if we want to replace runsTo by eventually everywhere, or move
   this compatibility lemma to an appropriate place *)
Lemma runsTo_is_eventually[State: Type](step: State -> (State -> Prop) -> Prop):
  forall initial P, runsToNonDet.runsTo step initial P <-> eventually step P initial.
Proof. intros. split; induction 1; try (econstructor; solve [eauto]). Qed.

Global Existing Instance riscv.Spec.Machine.DefaultRiscvState.

Open Scope Z_scope.

Local Open Scope ilist_scope.

Section Pipeline1.
  Context {width: Z}.
  Context {BW: Bitwidth width}.
  Local Notation word := (bits width).
  Context {mem: map.map word byte}.
  Context {Registers: map.map Z word}.
  Context {string_keyed_map: forall T: Type, map.map string T}. (* abstract T for better reusability *)
  Context {ext_spec: LeakageSemantics.ExtSpec}.
  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgramWithLeakage M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {string_keyed_map_ok: forall T, map.ok (string_keyed_map T)}.
  Context {Registers_ok: map.ok Registers}.
  Context {PR: MetricPrimitives PRParams}.
  Context {iset: InstructionSet}.
  Context {BWM: bitwidth_iset width iset}.
  Context {mem_ok: map.ok mem}.
  Context {ext_spec_ok: LeakageSemantics.ext_spec.ok ext_spec}.
  Context (compile_ext_call : string_keyed_map Z -> Z -> Z -> FlatImp.stmt Z -> list Instruction).
  Context (leak_ext_call: word -> string_keyed_map Z -> Z -> Z -> FlatImp.stmt Z -> list word -> list LeakageEvent).
  Context (compile_ext_call_correct: forall resvars extcall argvars,
              compiles_FlatToRiscv_correctly compile_ext_call leak_ext_call compile_ext_call
                                             (FlatImp.SInteract resvars extcall argvars)).
  Context (compile_ext_call_length_ignores_positions: forall stackoffset posmap1 posmap2 c pos1 pos2,
              List.length (compile_ext_call posmap1 pos1 stackoffset c) =
              List.length (compile_ext_call posmap2 pos2 stackoffset c)).

  Add Ring wring : (Zmod.ring_theory (2 ^ width))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (width := width)),
       constants [word_cst]).


  Context (ml: MemoryLayout)
          (mlOk: MemoryLayoutOk ml).

  Lemma instrencode_cons: forall instr instrs,
      instrencode (instr :: instrs) =
      HList.tuple.to_list (LittleEndian.split 4 (encode instr)) ++ instrencode instrs.
  Proof. intros. reflexivity. Qed.

  Lemma instrencode_app: forall instrs1 instrs2,
      instrencode (instrs1 ++ instrs2) = instrencode instrs1 ++ instrencode instrs2.
  Proof.
    induction instrs1; intros.
    - reflexivity.
    - change ((a :: instrs1) ++ instrs2) with (a :: instrs1 ++ instrs2).
      rewrite !instrencode_cons.
      rewrite <-!List.app_assoc.
      f_equal.
      apply IHinstrs1.
  Qed.

  Definition imem(code_start code_pastend: word)(instrs: list Instruction): mem -> Prop :=
    (ptsto_bytes code_start (instrencode instrs) *
     mem_available (Zmod.add code_start (bits.of_Z width (Z.of_nat (List.length (instrencode instrs)))))
                   code_pastend)%sep.

  Lemma ptsto_bytes_to_program: forall instrs (p_code: word),
      Zmod.unsigned p_code mod 4 = 0 ->
      Forall (fun i => verify i iset \/ valid_InvalidInstruction i) instrs ->
      iff1 (ptsto_bytes p_code (instrencode instrs))
           (program iset p_code instrs).
  Proof.
    induction instrs; intros.
    - reflexivity.
    - simp. unfold program in *. rewrite array_cons.
      rewrite <- IHinstrs; [|DivisibleBy4.solve_divisibleBy4|assumption].
      cbn [instrencode flat_map]; fold (instrencode instrs); rewrite !LittleEndian.to_list_split.
      cbv [ptsto_bytes]. rewrite array_append'. Morphisms.f_equiv; cycle 1.
      { rewrite Zmod.mul_1_l, LittleEndianList.length_le_split; Morphisms.f_equiv. }
      cbv [ptsto_instr truncated_scalar].
      etransitivity. { eapply array1_iff_eq_of_list_word_at; trivial.
        rewrite LittleEndianList.length_le_split. case width_cases; intros ->; blia. }
      rewrite !sep_assoc, !sep_emp_emp, <-sep_emp_True_r; Morphisms.f_equiv; [cancel|].
      apply RunInstruction.iff1_emp; simpl Memory.bytes_per; intuition auto.
      all : case width_cases; intros ->; blia.
  Qed.

  Lemma ptsto_bytes_range: forall bs (start pastend : word) m a v,
      ptsto_bytes start bs m ->
      Zmod.unsigned start + Z.of_nat (List.length bs) <= Zmod.unsigned pastend ->
      map.get m a = Some v ->
      Zmod.unsigned start <= Zmod.unsigned a < Zmod.unsigned pastend.
  Proof.
    induction bs; intros.
    - simpl in *. unfold emp in *. simp. rewrite map.get_empty in H1. discriminate.
    - simpl in *.
      unfold sep in H. simp.
      specialize IHbs with (1 := Hp2).
      destr (Z.eqb (Zmod.unsigned a0) (Zmod.unsigned start)). 1: blia.
      specialize (IHbs pastend a0 v).
      destruct IHbs as [L R].
      + rewrite Zmod.unsigned_add.
        eapply Z.le_trans. 2: eassumption.
        eapply Z.le_trans
          with (m := Zmod.unsigned start + Zmod.unsigned (bits.of_Z width 1) + Z.of_nat (Datatypes.length bs)).
        * apply Z.add_le_mono_r.
          apply Z.mod_le.
          -- repeat match goal with
                    | |- context [Zmod.unsigned ?w] => unique pose proof (bits.unsigned_range w width_nonneg)
                    end.
             blia.
          -- destruct width_cases as [F|F]; simpl in *; rewrite F; reflexivity.
         * rewrite bits.unsigned_of_Z.
           replace (1 mod 2 ^ width) with 1. 1: blia.
           simpl.
           destruct width_cases as [F|F]; simpl in *; rewrite F; reflexivity.
      + unfold map.split in *. simp.
        rewrite map.get_putmany_dec in H1.
        destr (map.get mq a0). 1: congruence.
        exfalso.
        unfold ptsto in *. subst mp.
        rewrite map.get_put_dec in H1.
        destr (Zmod.eqb start a0).
        * apply E. congruence.
        * rewrite map.get_empty in H1. discriminate.
      + rewrite Zmod.unsigned_add in L.
        split; try assumption.
        eapply Z.le_trans. 2: eassumption.
        repeat match goal with
               | |- context [Zmod.unsigned ?w] => unique pose proof (bits.unsigned_range w width_nonneg)
               end.
        rewrite Z.mod_small. 1: blia.
        split; [blia|].
        eapply Z.le_lt_trans.
        2: exact (proj2 (bits.unsigned_range pastend width_nonneg)).
        eapply Z.le_trans. 2: eassumption.
        rewrite bits.unsigned_of_Z.
        replace (1 mod 2 ^ width) with 1. 1: blia.
        simpl.
        destruct width_cases as [F|F]; simpl in *; rewrite F; reflexivity.
  Qed.

  Context (spec: ProgramSpec).

  Definition initial_conditions(initial: MetricRiscvMachine): Prop :=
    exists srcprog (instrs: list Instruction) positions required_stack_space,
      ProgramSatisfiesSpec "init"%string "loop"%string srcprog spec /\
      spec.(datamem_start) = ml.(heap_start) /\
      spec.(datamem_pastend) = ml.(heap_pastend) /\
      compile_prog compile_ext_call ml srcprog = Success (instrs, positions, required_stack_space) /\
      required_stack_space <= Zmod.unsigned (Zmod.sub (stack_pastend ml) (stack_start ml)) / bytes_per_word /\
      Zmod.unsigned ml.(code_start) + Z.of_nat (List.length (instrencode instrs)) <=
        Zmod.unsigned ml.(code_pastend) /\
      bvalidInstructions iset instrs = true /\
      (imem ml.(code_start) ml.(code_pastend) instrs *
       mem_available ml.(heap_start) ml.(heap_pastend) *
       mem_available ml.(stack_start) ml.(stack_pastend))%sep initial.(getMem) /\
      (forall a, Zmod.unsigned ml.(code_start) <= Zmod.unsigned a < Zmod.unsigned ml.(code_pastend) ->
                 List.In a initial.(getXAddrs)) /\
      initial.(getPc) = ml.(code_start) /\
      initial.(getNextPc) = Zmod.add initial.(getPc) (bits.of_Z width 4) /\
      regs_initialized.regs_initialized initial.(getRegs) /\
      initial.(getLog) = nil /\
      initial.(getTrace) = Some nil /\
      valid_machine initial.

  Lemma compiler_invariant_proofs:
    (forall initial, initial_conditions initial -> ll_inv compile_ext_call ml spec initial) /\
    (forall st, ll_inv compile_ext_call ml spec st ->
                GoFlatToRiscv.mcomp_sat (run1 iset) st (ll_inv compile_ext_call ml spec)) /\
    (forall st, ll_inv compile_ext_call ml spec st ->
                exists suff, spec.(goodTrace) (suff ++ st.(getLog))).
  Proof.
    ssplit; intros.
    - eapply (establish_ll_inv _ _ compile_ext_call_correct compile_ext_call_length_ignores_positions).
      1: assumption.
      unfold initial_conditions, ToplevelLoop.initial_conditions in *.
      simp.
      eassert ((ptsto_bytes (code_start ml) (instrencode instrs) * _)%sep initial.(getMem)) as SplitImem by (unfold imem in *; ecancel_assumption).
      destruct SplitImem as [i_mem [non_imem [SplitImem [Imem NonImem] ] ] ].
      do 5 eexists.
      ssplit; try eassumption.
      + unfold subset, footpr, footprint_underapprox, of_list, elem_of, program.
        intros a M0.
        match goal with
        | H: _ |- _ => eapply H
        end.
        specialize (M0 i_mem).
        destruct mlOk.
        destruct M0 as [v M0].
        * apply ptsto_bytes_to_program; try assumption.
          eapply bvalidInstructions_valid. assumption.
        * unfold ptsto_bytes in Imem.
          eapply ptsto_bytes_range; try eassumption.
      + unfold imem in *.
        wcancel_assumption.
        unfold ptsto_bytes.
        cancel_seps_at_indices 0%nat 0%nat. 2: reflexivity.
        eapply iff1ToEq.
        destruct mlOk.
        eapply ptsto_bytes_to_program; try eassumption.
        eapply bvalidInstructions_valid. assumption.
    - eapply @ll_inv_is_invariant; eassumption.
    - eapply ll_inv_implies_prefix_of_good. eassumption.
  Qed.

  Definition good_trace(st: MetricRiscvMachine): Prop := spec.(goodTrace) st.(getLog).
  Definition always: (MetricRiscvMachine -> Prop) -> MetricRiscvMachine -> Prop :=
    always (GoFlatToRiscv.mcomp_sat (run1 iset)).
  Definition eventually: (MetricRiscvMachine -> Prop) -> MetricRiscvMachine -> Prop :=
    eventually (GoFlatToRiscv.mcomp_sat (run1 iset)).

  Lemma always_eventually_good_trace: forall initial,
      initial_conditions initial ->
      always (eventually good_trace) initial.
  Proof.
    intros * IC. unfold always, eventually, good_trace.
    apply mk_always with (invariant := ll_inv compile_ext_call ml spec).
    - apply (proj1 compiler_invariant_proofs _ IC).
    - apply (proj1 (proj2 compiler_invariant_proofs)).
    - intros st HInv. unfold ll_inv, RiscvEventLoop.runsToGood_Invariant, ll_good in HInv.
      apply proj1 in HInv. apply runsTo_is_eventually in HInv.
      eapply eventually_weaken. 1: exact HInv.
      clear initial IC st HInv. cbv beta. intros. simp. assumption.
  Qed.

End Pipeline1.
