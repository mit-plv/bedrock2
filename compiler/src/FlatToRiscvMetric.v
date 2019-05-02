Require Import riscv.Spec.Decode.
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
Import compiler.FlatToRiscvCommon.FlatToRiscv.
Require Import compiler.FlatToRiscvLiterals.

Open Scope ilist_scope.

Section Proofs.
  Context {p: FlatToRiscv.parameters}.
  Context {h: FlatToRiscv.assumptions}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Notation RiscvMachineL := MetricRiscvMachine.

  Ltac apply_post :=
    match goal with
    | H: ?post _ _ _ |- ?post _ _ _ =>
      eqexact H; f_equal; symmetry;
      (apply word.sru_ignores_hibits ||
       apply word.slu_ignores_hibits ||
       apply word.srs_ignores_hibits ||
       apply word.mulhuu_simpl ||
       apply word.divu0_simpl ||
       apply word.modu0_simpl)
    end.

  Ltac run1done :=
    apply runsToDone;
    simpl_MetricRiscvMachine_get_set;
    simpl in *;
    eexists; (* finalMH *)
    eexists; (* finalMetricsH *)
    repeat split;
    simpl_word_exprs (@word_ok (@W (@def_params p)));
    first
      [ solve [eauto]
      | solve_MetricLog
      | solve_word_eq (@word_ok (@W (@def_params p)))
      | solve [pseplog]
      | prove_ext_guarantee
      | apply_post
      | idtac ].

  Ltac IH_sidecondition :=
    simpl_word_exprs (@word_ok (@W (@def_params p)));
    try solve
      [ reflexivity
      | auto
      | solve_stmt_not_too_big
      | solve_word_eq (@word_ok (@W (@def_params p)))
      | simpl; solve_divisibleBy4
      | prove_ext_guarantee
      | pseplog ].

  Lemma compile_stmt_correct:
    forall (s: stmt) t initialMH initialRegsH postH initialMetricsH,
    FlatImp.exec map.empty s t initialMH initialRegsH initialMetricsH postH ->
    forall R (initialL: RiscvMachineL) insts,
    @compile_stmt def_params s = insts ->
    stmt_not_too_big s ->
    valid_registers s ->
    divisibleBy4 initialL.(getPc) ->
    initialL.(getRegs) = initialRegsH ->
    (program initialL.(getPc) insts * eq initialMH * R)%sep initialL.(getMem) ->
    initialL.(getLog) = t ->
    initialL.(getNextPc) = add initialL.(getPc) (ZToReg 4) ->
    ext_guarantee initialL ->
    runsTo initialL (fun finalL => exists finalMH finalMetricsH,
          postH finalL.(getLog) finalMH finalL.(getRegs) finalMetricsH /\
          (program initialL.(getPc) insts * eq finalMH * R)%sep finalL.(getMem) /\
          finalL.(getPc) = add initialL.(getPc) (mul (ZToReg 4) (ZToReg (Zlength insts))) /\
          finalL.(getNextPc) = add finalL.(getPc) (ZToReg 4) /\
          (finalL.(getMetrics) - initialL.(getMetrics) <=
           lowerMetrics (finalMetricsH - initialMetricsH))%metricsL /\
          ext_guarantee finalL).
  Proof.
    pose proof compile_stmt_emits_valid.
    induction 1; intros;
      lazymatch goal with
      | H1: valid_registers ?s, H2: stmt_not_too_big ?s |- _ =>
        pose proof (compile_stmt_emits_valid iset_is_supported H1 H2)
      end;
      repeat match goal with
             | m: _ |- _ => destruct_RiscvMachine m; simpl_MetricRiscvMachine_get_set
             end;
      simpl in *;
      subst;
      simp.

    - (* SInteract *)
      eapply runsTo_weaken.
      + eapply compile_ext_call_correct with (postH := post) (action0 := action)
                                             (argvars0 := argvars) (resvars0 := resvars);
          simpl; reflexivity || eassumption || ecancel_assumption || idtac.
        eapply @exec.interact; try eassumption.
      + simpl. intros finalL A. destruct_RiscvMachine finalL.
        simpl_MetricRiscvMachine_get_set. simpl in *.
        destruct_products. subst. exists m. exists finalMetricsH.
        repeat (split; try eassumption).

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
      assert ((eq m * (program initialL_pc [[compile_store sz a v 0]] * R))%sep initialL_mem)
             as A by ecancel_assumption.
      pose proof (store_bytes_frame H2 A) as P.

      destruct P as (finalML & P1 & P2).
      run1det. run1done.

    - (* SLit *)
      eapply compile_lit_correct_full.
      + sidecondition.
      + unfold compile_stmt. unfold getPc, getMem, liftGet in *. simpl. ecancel_assumption.
      + sidecondition.
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
        simpl in *; run1det; try solve [run1done].
      + simpl_MetricRiscvMachine_get_set.
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
      eapply runsTo_det_step; simpl in *; subst.
      + simulate'. simpl_MetricRiscvMachine_get_set.
        destruct cond; [destruct op | ];
          simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity.
      + eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
        * (* use IH for then-branch *)
          eapply IHexec; IH_sidecondition.
        * (* jump over else-branch *)
          simpl. intros. destruct_RiscvMachine middle. simp. subst.
          run1det. run1done.

    - (* SIf/Else *)
      (* execute branch instruction, which will jump over then-branch *)
      eapply runsTo_det_step; simpl in *; subst.
      + simulate'.
        destruct cond; [destruct op | ];
          simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity.
      + eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
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
        destruct (@eval_bcond (@Semantics_params p) middle_regs cond) as [condB|] eqn: E.
        2: exfalso;
           match goal with
           | H: context [_ <> None] |- _ => solve [eapply H; eauto]
           end.
        destruct condB.
        * (* true: iterate again *)
          eapply runsTo_det_step; simpl in *; subst.
          { simulate'.
            destruct cond; [destruct op | ];
              simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity. }
          { eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
            - (* 2nd application of IH: part 2 of loop body *)
              eapply IH2; IH_sidecondition; simpl_MetricRiscvMachine_get_set; eassumption.
            - simpl in *. simpl. intros. destruct_RiscvMachine middle. simp. subst.
              (* jump back to beginning of loop: *)
              run1det.
              eapply runsTo_trans; simpl_MetricRiscvMachine_get_set.
              + (* 3rd application of IH: run the whole loop again *)
                eapply IH12; IH_sidecondition; simpl_MetricRiscvMachine_get_set; eassumption.
              + (* at end of loop, just prove that computed post satisfies required post *)
                simpl. intros. destruct_RiscvMachine middle. simp. subst.
                run1done. }
        * (* false: done, jump over body2 *)
          eapply runsTo_det_step; simpl in *; subst.
          { simulate'.
            destruct cond; [destruct op | ];
              simpl in *; simp; repeat (simulate'; simpl_bools; simpl); try reflexivity. }
          { simpl in *. run1done. }

    - (* SSeq *)
      rename IHexec into IH1, H2 into IH2.
      eapply runsTo_trans.
      + eapply IH1; IH_sidecondition.
      + simpl. intros. destruct_RiscvMachine middle. simp. subst.
        eapply runsTo_trans.
        * eapply IH2; IH_sidecondition; simpl_MetricRiscvMachine_get_set; eassumption.
        * simpl. intros. destruct_RiscvMachine middle. simp. subst. run1done.

    - (* SSkip *)
      run1done.
  Qed.

End Proofs.
