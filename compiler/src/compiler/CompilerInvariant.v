Require Import coqutil.Tactics.rewr.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Byte.
Require Import bedrock2.Array.
Require Import bedrock2.Map.SeparationLogic.
Require Import compiler.SeparationLogic.
Require Import coqutil.Tactics.Simp.
Require Import compiler.FlatToRiscvFunctions.
Require Import compiler.PipelineWithRename.
Require Import compiler.ExprImpEventLoopSpec.
Require Import compiler.ToplevelLoop.


Existing Instance riscv.Spec.Machine.DefaultRiscvState.

Open Scope Z_scope.

Local Open Scope ilist_scope.

Section Pipeline1.

  Context {p: Pipeline.parameters}.
  Context {h: Pipeline.assumptions}.

  Local Notation word := (@Utility.word (@Pipeline.W p)).
  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := (@Utility.word (@Pipeline.W p)))),
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

  (* PARAMRECORDS: "unfold imem" below relies on the syntactic form of this definition. *)
  Definition imem(code_start code_pastend: Semantics.word)(instrs: list Instruction): Semantics.mem -> Prop :=
    (ptsto_bytes (word:=word)(mem:=(@Pipeline.mem p)) code_start (instrencode instrs) *
     mem_available (word.add code_start (word.of_Z (Z.of_nat (List.length (instrencode instrs)))))
                   code_pastend)%sep.

  Lemma ptsto_bytes_to_program: forall instrs p_code,
      word.unsigned p_code mod 4 = 0 ->
      Forall (fun i => verify i FlatToRiscvDef.FlatToRiscvDef.iset) instrs ->
      iff1 (ptsto_bytes p_code (instrencode instrs))
           (program FlatToRiscvDef.FlatToRiscvDef.iset p_code instrs).
  Proof.
    induction instrs; intros.
    - reflexivity.
    - simp. unfold program in *. rewrite array_cons.
      specialize (IHinstrs (word.add p_code (word.of_Z 4))).
      unfold ptsto_instr at 1.
      unfold truncated_scalar, littleendian, ptsto_bytes, ptsto_bytes.ptsto_bytes.
      simpl.
      assert (map.ok Pipeline.mem) as Ok by exact FlatToRiscvCommon.mem_ok. (* PARAMRECORDS *)
      simpl.
      rewrite <- IHinstrs; [|DivisibleBy4.solve_divisibleBy4|assumption].
      wwcancel.
      cbn [seps].
      rewrite sep_emp_emp.
      match goal with
      | |- iff1 (emp ?P) (emp ?Q) => apply (RunInstruction.iff1_emp P Q)
      end.
      split; intros _; try exact I.
      auto.
  Qed.

  Lemma ptsto_bytes_range: forall bs (start pastend : FlatImp.word) m a v,
      ptsto_bytes start bs m ->
      word.unsigned start + Z.of_nat (List.length bs) <= word.unsigned pastend ->
      map.get m a = Some v ->
      word.unsigned start <= word.unsigned a < word.unsigned pastend.
  Proof.
    assert (map.ok Pipeline.mem) as Ok by exact FlatToRiscvCommon.mem_ok.
    induction bs; intros.
    - simpl in *. unfold emp in *. simp. rewrite map.get_empty in H1. discriminate.
    - simpl in *.
      unfold sep in H. simp.
      specialize IHbs with (1 := Hp2).
      destr (Z.eqb (word.unsigned a0) (word.unsigned start)). 1: blia.
      specialize (IHbs pastend a0 v).
      destruct IHbs as [L R].
      + rewrite word.unsigned_add. unfold word.wrap.
        eapply Z.le_trans. 2: eassumption.
        eapply Z.le_trans
          with (m := word.unsigned start + word.unsigned (word.of_Z 1) + Z.of_nat (Datatypes.length bs)).
        * apply Z.add_le_mono_r.
          apply Z.mod_le.
          -- repeat match goal with
                    | |- context [word.unsigned ?w] => unique pose proof (word.unsigned_range w)
                    end.
             blia.
          -- destruct width_cases as [F|F]; simpl in *; rewrite F; reflexivity.
         * rewrite word.unsigned_of_Z.
           unfold word.wrap.
           replace (1 mod 2 ^ width) with 1. 1: blia.
           simpl.
           destruct width_cases as [F|F]; simpl in *; rewrite F; reflexivity.
      + unfold map.split in *. simp.
        rewrite map.get_putmany_dec in H1.
        destr (map.get mq a0). 1: congruence.
        exfalso.
        unfold ptsto in *. subst mp.
        rewrite map.get_put_dec in H1.
        destr (word.eqb start a0).
        * apply E. congruence.
        * rewrite map.get_empty in H1. discriminate.
      + rewrite word.unsigned_add in L. unfold word.wrap in L.
        split; try assumption.
        eapply Z.le_trans. 2: eassumption.
        repeat match goal with
               | |- context [word.unsigned ?w] => unique pose proof (word.unsigned_range w)
               end.
        rewrite Z.mod_small. 1: blia.
        split; [blia|].
        eapply Z.le_lt_trans.
        2: exact (proj2 (word.unsigned_range pastend)).
        eapply Z.le_trans. 2: eassumption.
        rewrite word.unsigned_of_Z.
        unfold word.wrap.
        replace (1 mod 2 ^ width) with 1. 1: blia.
        simpl.
        destruct width_cases as [F|F]; simpl in *; rewrite F; reflexivity.
  Qed.

  Context (spec: @ProgramSpec (FlattenExpr.mk_Semantics_params _)).

  Definition initial_conditions(initial: MetricRiscvMachine): Prop :=
    exists (srcprog: Semantics.env) (instrs: list Instruction) positions,
      ProgramSatisfiesSpec "init"%string "loop"%string srcprog spec /\
      spec.(datamem_start) = ml.(heap_start) /\
      spec.(datamem_pastend) = ml.(heap_pastend) /\
      compile_prog ml srcprog = Some (instrs, positions) /\
      word.unsigned ml.(code_start) + Z.of_nat (List.length (instrencode instrs)) <=
        word.unsigned ml.(code_pastend) /\
      Forall (fun i : Instruction => verify i FlatToRiscvDef.FlatToRiscvDef.iset) instrs /\
      (imem ml.(code_start) ml.(code_pastend) instrs *
       mem_available ml.(heap_start) ml.(heap_pastend) *
       mem_available ml.(stack_start) ml.(stack_pastend))%sep initial.(getMem) /\
      (forall a, word.unsigned ml.(code_start) <= word.unsigned a < word.unsigned ml.(code_pastend) ->
                 List.In a initial.(getXAddrs)) /\
      initial.(getPc) = ml.(code_start) /\
      initial.(getNextPc) = word.add initial.(getPc) (word.of_Z 4) /\
      FlatToRiscvCommon.regs_initialized initial.(getRegs) /\
      initial.(getLog) = nil /\
      valid_machine initial.

  Lemma compiler_invariant_proofs:
    (forall initial, initial_conditions initial -> ll_inv ml spec initial) /\
    (forall st, ll_inv ml spec st ->
                GoFlatToRiscv.mcomp_sat (run1 FlatToRiscvDef.FlatToRiscvDef.iset) st (ll_inv ml spec)) /\
    (forall st, ll_inv ml spec st -> exists suff, spec.(goodTrace) (suff ++ st.(getLog))).
  Proof.
    assert (map.ok Pipeline.mem) as Okk by exact FlatToRiscvCommon.mem_ok. (* PARAMRECORDS *)
    assert (word.ok Semantics.word) by exact word_ok.
    ssplit; intros.
    - eapply establish_ll_inv. 1: assumption.
      unfold initial_conditions, ToplevelLoop.initial_conditions in *.
      simp.
      eassert ((ptsto_bytes (code_start ml) (instrencode instrs) * _)%sep initial.(getMem)) as SplitImem by (unfold imem in *; ecancel_assumption).
      destruct SplitImem as [i_mem [non_imem [SplitImem [Imem NonImem] ] ] ].
      do 4 eexists.
      ssplit; try eassumption.
      + unfold subset, footpr, footprint_underapprox, of_list, elem_of, program.
        intros a M.
        match goal with
        | H: _ |- _ => eapply H
        end.
        specialize (M i_mem).
        destruct mlOk.
        destruct M as [v M].
        * apply ptsto_bytes_to_program; assumption.
        * unfold ptsto_bytes in Imem.
          eapply ptsto_bytes_range; try eassumption.
      + unfold imem in *.
        wcancel_assumption.
        unfold ptsto_bytes.
        cancel_seps_at_indices 0%nat 0%nat. 2: reflexivity.
        eapply iff1ToEq.
        destruct mlOk.
        eapply ptsto_bytes_to_program; try eassumption.
    - eapply @ll_inv_is_invariant; eassumption.
    - eapply ll_inv_implies_prefix_of_good. eassumption.
  Qed.

End Pipeline1.
