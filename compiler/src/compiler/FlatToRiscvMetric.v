Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.runsToNonDet.
Require Import riscv.Utility.InstructionCoercions.
Require Import compiler.util.Common.
Require Import compiler.eqexact.
Require Import compiler.Simp.
Require Import compiler.on_hyp_containing.
Require Import compiler.SeparationLogic.
Require Import compiler.SimplWordExpr.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.DivisibleBy4.
Require Import compiler.EmitsValid.
Require Import compiler.MetricsToRiscv.
Require Import compiler.FlatImp.
Require Import compiler.RiscvWordProperties.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvLiterals.
Import Utility.

Open Scope ilist_scope.

Section Proofs.
  Context {p: FlatToRiscvCommon.parameters}.
  Context {h: FlatToRiscvCommon.assumptions}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Notation RiscvMachineL := MetricRiscvMachine.

  Ltac run1done :=
    apply runsToDone;
    simpl_MetricRiscvMachine_get_set;
    rewrite ?word.sru_ignores_hibits,
            ?word.slu_ignores_hibits,
            ?word.srs_ignores_hibits,
            ?word.mulhuu_simpl,
            ?word.divu0_simpl,
            ?word.modu0_simpl;
    simpl in *;
    eexists; (* finalMH *)
    eexists; (* finalMetricsH *)
    repeat split;
    simpl_word_exprs (@word_ok (@W (@def_params p)));
    first
      [ solve [eauto]
      | solve_MetricLog
      | solve_word_eq (@word_ok (@W (@def_params p)))
      | solve [wcancel_assumption]
      | eapply rearrange_footpr_subset; [ eassumption | wwcancel ]
      | solve [solve_valid_machine (@word_ok (@W (@def_params p)))]
      | idtac ].

  Ltac IH_sidecondition :=
    simpl_word_exprs (@word_ok (@W (@def_params p)));
    try solve
      [ reflexivity
      | auto
      | solve_stmt_not_too_big
      | solve_word_eq (@word_ok (@W (@def_params p)))
      | simpl; solve_divisibleBy4
      | solve_valid_machine (@word_ok (@W (@def_params p)))
      | eapply rearrange_footpr_subset; [ eassumption | wwcancel ]
      | wcancel_assumption ].

  Hypothesis no_ext_calls: forall t mGive action argvals outcome,
      ext_spec t mGive action argvals outcome -> False.

  Lemma compile_stmt_correct:
    forall (s: stmt Z) t initialMH initialRegsH postH initialMetricsH,
    FlatImp.exec map.empty s t initialMH initialRegsH initialMetricsH postH ->
    forall R Rexec (initialL: RiscvMachineL) insts pos,
    @compile_stmt def_params _ map.empty pos s = insts ->
    stmt_not_too_big s ->
    valid_FlatImp_vars s ->
    divisibleBy4 initialL.(getPc) ->
    initialL.(getRegs) = initialRegsH ->
    subset (footpr (program initialL.(getPc) insts * Rexec)%sep) (of_list initialL.(getXAddrs)) ->
    (program initialL.(getPc) insts * Rexec * eq initialMH * R)%sep initialL.(getMem) ->
    initialL.(getLog) = t ->
    initialL.(getNextPc) = add initialL.(getPc) (word.of_Z 4) ->
    valid_machine initialL ->
    runsTo initialL (fun finalL => exists finalMH finalMetricsH,
          postH finalL.(getLog) finalMH finalL.(getRegs) finalMetricsH /\
          subset (footpr (program initialL.(getPc) insts * Rexec)%sep)
                 (of_list finalL.(getXAddrs)) /\
          (program initialL.(getPc) insts * Rexec * eq finalMH * R)%sep finalL.(getMem) /\
          finalL.(getPc) = add initialL.(getPc)
                             (word.mul (word.of_Z 4) (word.of_Z (Z.of_nat (length insts)))) /\
          finalL.(getNextPc) = word.add finalL.(getPc) (word.of_Z 4) /\
          (finalL.(getMetrics) - initialL.(getMetrics) <=
           lowerMetrics (finalMetricsH - initialMetricsH))%metricsL /\
          valid_machine finalL).
  Proof.
    pose proof compile_stmt_emits_valid.
    induction 1; intros;
      repeat match goal with
             | m: _ |- _ => destruct_RiscvMachine m; simpl_MetricRiscvMachine_get_set
             end;
      simpl in *;
      subst;
      simp.

    - (* SInteract *)
      exfalso. eapply no_ext_calls. eassumption.

    - (* SCall *)
      lazymatch goal with
      | A: map.get map.empty _ = Some _ |- _ =>
        exfalso; simpl in *;
        rewrite map.get_empty in A
      end.
      discriminate.

    - (* SLoad *)
      unfold Memory.load, Memory.load_Z in *. simp. subst_load_bytes_for_eq.
      run1det. run1done.

    - (* SStore *)
      simpl_MetricRiscvMachine_get_set.
      assert ((eq m * (program initialL_pc [[compile_store sz a v 0]] * Rexec * R))%sep
        initialL_mem) as A by ecancel_assumption.
      pose proof (store_bytes_frame H2 A) as P.
      destruct P as (finalML & P1 & P2).
      move H2 at bottom.
      unfold Memory.store, Memory.store_Z, Memory.store_bytes in H2. simp.
      subst_load_bytes_for_eq.
      run1det. run1done.
      eapply preserve_subset_of_xAddrs. 1: assumption.
      ecancel_assumption.

    - (* SLit *)
      get_run1valid_for_free.
      eapply compile_lit_correct_full.
      + sidecondition.
      + sidecondition.
      + unfold compile_stmt. simpl. ecancel_assumption.
      + sidecondition.
      + assumption.
      + simpl. run1done;
        remember (updateMetricsForLiteral v initialL_metrics) as finalMetrics;
        symmetry in HeqfinalMetrics;
        pose proof update_metrics_for_literal_bounded as Hlit;
        specialize Hlit with (1 := HeqfinalMetrics);
        solve_MetricLog.

    - (* SOp *)
      match goal with
      | o: Syntax.bopname.bopname |- _ => destruct o
      end;
      simpl in *; run1det;
      rewrite ?word.sru_ignores_hibits,
              ?word.slu_ignores_hibits,
              ?word.srs_ignores_hibits,
              ?word.mulhuu_simpl,
              ?word.divu0_simpl,
              ?word.modu0_simpl in *;
      try solve [run1done].
      simpl_MetricRiscvMachine_get_set.
      run1det. run1done;
      [match goal with
      | H: ?post _ _ _ |- ?post _ _ _ => eqexact H
      end | solve_MetricLog..].
      rewrite reduce_eq_to_sub_and_lt.
      symmetry. apply map.put_put_same.

    - (* SSet *)
      run1det. run1done.

    - (* SIf/Then *)
      (* execute branch instruction, which will not jump *)
      eapply runsTo_det_step_with_valid_machine; simpl in *; subst.
      + assumption.
      + simulate'. simpl_MetricRiscvMachine_get_set.
        destruct cond; [destruct op | ];
          simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity.
      + intro V. eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
        * (* use IH for then-branch *)
          eapply IHexec; IH_sidecondition.
        * (* jump over else-branch *)
          simpl. intros. destruct_RiscvMachine middle. simp. subst.
          run1det. run1done.

    - (* SIf/Else *)
      (* execute branch instruction, which will jump over then-branch *)
      eapply runsTo_det_step_with_valid_machine; simpl in *; subst.
      + assumption.
      + simulate'.
        destruct cond; [destruct op | ];
          simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity.
      + intro V. eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
        * (* use IH for else-branch *)
          eapply IHexec; IH_sidecondition.
        * (* at end of else-branch, i.e. also at end of if-then-else, just prove that
             computed post satisfies required post *)
          simpl. intros. destruct_RiscvMachine middle. simp. subst. run1done.

    - (* SLoop/again *)
      on hyp[(stmt_not_too_big body1); runsTo] do (fun H => rename H into IH1).
      on hyp[(stmt_not_too_big body2); runsTo] do (fun H => rename H into IH2).
      on hyp[(stmt_not_too_big (SLoop body1 cond body2)); runsTo] do (fun H => rename H into IH12).
      eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
      + (* 1st application of IH: part 1 of loop body *)
        eapply IH1; IH_sidecondition.
      + simpl in *. simpl. intros. destruct_RiscvMachine middle. simp. subst.
        destruct (@eval_bcond Z (@Semantics_params p) middle_regs cond) as [condB|] eqn: E.
        2: exfalso;
           match goal with
           | H: context [_ <> None] |- _ => solve [eapply H; eauto]
           end.
        destruct condB.
        * (* true: iterate again *)
          eapply runsTo_det_step_with_valid_machine; simpl in *; subst.
          { assumption. }
          { simulate'.
            destruct cond; [destruct op | ];
              simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity. }
          { intro V. eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
            - (* 2nd application of IH: part 2 of loop body *)
              eapply IH2; IH_sidecondition; simpl_MetricRiscvMachine_get_set;
                try eassumption; IH_sidecondition.
            - simpl in *. simpl. intros. destruct_RiscvMachine middle. simp. subst.
              (* jump back to beginning of loop: *)
              run1det.
              eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
              + (* 3rd application of IH: run the whole loop again *)
                eapply IH12 with (pos := pos); IH_sidecondition; simpl_MetricRiscvMachine_get_set;
                  try eassumption; IH_sidecondition.
              + (* at end of loop, just prove that computed post satisfies required post *)
                simpl. intros. destruct_RiscvMachine middle. simp. subst.
                run1done. }
        * (* false: done, jump over body2 *)
          eapply runsTo_det_step_with_valid_machine; simpl in *; subst.
          { assumption. }
          { simulate'.
            destruct cond; [destruct op | ];
              simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity. }
          { intro V. simpl in *. run1done. }

    - (* SSeq *)
      rename IHexec into IH1, H2 into IH2.
      eapply runsTo_trans.
      + eapply IH1; IH_sidecondition.
      + simpl. intros. destruct_RiscvMachine middle. simp. subst.
        eapply runsTo_trans.
        * eapply IH2; IH_sidecondition; simpl_MetricRiscvMachine_get_set;
            try eassumption; IH_sidecondition.
        * simpl. intros. destruct_RiscvMachine middle. simp. subst. run1done.

    - (* SSkip *)
      run1done.
  Qed.

End Proofs.
