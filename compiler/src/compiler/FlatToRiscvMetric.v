Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.runsToNonDet.
Require Import riscv.Utility.InstructionCoercions.
Require Import compiler.util.Common.
Require Import compiler.eqexact.
Require Import coqutil.Tactics.Simp.
Require Import compiler.on_hyp_containing.
Require Import compiler.SeparationLogic.
Require Export coqutil.Word.SimplWordExpr.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.DivisibleBy4.
Require Import compiler.MetricsToRiscv.
Require Import compiler.FlatImp.
Require Import compiler.RiscvWordProperties.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvLiterals.

Open Scope ilist_scope.

Local Arguments Z.mul: simpl never.
Local Arguments Z.add: simpl never.
Local Arguments Z.of_nat: simpl never.
Local Arguments Z.modulo : simpl never.
Local Arguments Z.pow: simpl never.
Local Arguments Z.sub: simpl never.

Section Proofs.
  Context {iset: Decode.InstructionSet}.
  Context {pos_map: map.map String.string Z}.
  Context (compile_ext_call: pos_map -> Z -> Z -> stmt Z -> list Decode.Instruction).
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}.
  Context {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}.
  Context {locals: map.map Z word} {locals_ok: map.ok locals}.
  Context {mem: map.map word byte} {mem_ok: map.ok mem}.
  Context {env: map.map String.string (list Z * list Z * stmt Z)} {env_ok: map.ok env}.
  Context {M: Type -> Type}.
  Context {MM: Monads.Monad M}.
  Context {RVM: Machine.RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {ext_spec: Semantics.ExtSpec} {ext_spec_ok: Semantics.ext_spec.ok ext_spec}.
  Context {PR: MetricPrimitives.MetricPrimitives PRParams}.
  Context {BWM: bitwidth_iset width iset}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Notation RiscvMachineL := (MetricRiscvMachine (width := width)).

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
    simpl_word_exprs word_ok;
    first
      [ solve [eauto]
      | solve_MetricLog
      | solve_word_eq word_ok
      | solve [wcancel_assumption]
      | eapply rearrange_footpr_subset; [ eassumption | wwcancel ]
      | solve [solve_valid_machine word_ok]
      | idtac ].

  Ltac IH_sidecondition :=
    simpl_word_exprs word_ok;
    try solve
      [ reflexivity
      | auto
      | solve_word_eq word_ok
      | simpl; solve_divisibleBy4
      | solve_valid_machine word_ok
      | eapply rearrange_footpr_subset; [ eassumption | wwcancel ]
      | wcancel_assumption ].

  Hypothesis no_ext_calls: forall t mGive action argvals outcome,
      ext_spec t mGive action argvals outcome -> False.

  Hypothesis stackalloc_always_0: forall x n body t m (l: locals) mc post,
      FlatImp.exec map.empty (SStackalloc x n body) t m l mc post -> n = 0.

  Hypothesis sp_always_set: forall l: locals,
      map.get l RegisterNames.sp = Some (word.of_Z 42).

  (* not needed any more *)
  Definition stmt_not_too_big(s: stmt Z): Prop := True.

  Lemma compile_stmt_correct:
    forall (s: stmt Z) t initialMH initialRegsH postH initialMetricsH,
    FlatImp.exec map.empty s t initialMH initialRegsH initialMetricsH postH ->
    forall R Rexec (initialL: RiscvMachineL) insts pos,
    compile_stmt iset compile_ext_call map.empty pos 12345678 s = insts ->
    stmt_not_too_big s ->
    valid_FlatImp_vars s ->
    divisibleBy4 initialL.(getPc) ->
    initialL.(getRegs) = initialRegsH ->
    subset (footpr (program iset initialL.(getPc) insts * Rexec)%sep) (of_list initialL.(getXAddrs)) ->
    (program iset initialL.(getPc) insts * Rexec * eq initialMH * R)%sep initialL.(getMem) ->
    initialL.(getLog) = t ->
    initialL.(getNextPc) = add initialL.(getPc) (word.of_Z 4) ->
    valid_machine initialL ->
    runsTo initialL (fun finalL => exists finalMH finalMetricsH,
          postH finalL.(getLog) finalMH finalL.(getRegs) finalMetricsH /\
          subset (footpr (program iset initialL.(getPc) insts * Rexec)%sep)
                 (of_list finalL.(getXAddrs)) /\
          (program iset initialL.(getPc) insts * Rexec * eq finalMH * R)%sep finalL.(getMem) /\
          finalL.(getPc) = add initialL.(getPc)
                             (word.mul (word.of_Z 4) (word.of_Z (Z.of_nat (length insts)))) /\
          finalL.(getNextPc) = word.add finalL.(getPc) (word.of_Z 4) /\
          (finalL.(getMetrics) - initialL.(getMetrics) <=
           lowerMetrics (finalMetricsH - initialMetricsH))%metricsL /\
          valid_machine finalL).
  Proof.
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
      assert ((eq m * (program iset initialL_pc [[compile_store iset sz a v o]] * Rexec * R))%sep
        initialL_mem) as A by ecancel_assumption.
      match goal with
      | H: _ |- _ => pose proof (store_bytes_frame H A) as P; move H at bottom;
                       unfold Memory.store, Memory.store_Z, Memory.store_bytes in H
      end.
      destruct P as (finalML & P1 & P2).
      simp.
      destruct (eq_sym (LittleEndianList.length_le_split (Memory.bytes_per(width:=width) sz) (word.unsigned val))) in t0, E.
      subst_load_bytes_for_eq.
      run1det. run1done.
      eapply preserve_subset_of_xAddrs. 1: assumption.
      ecancel_assumption.

    - (* SInlinetable *)
      run1det.
      assert (map.get (map.put l x (word.add initialL_pc (word.of_Z 4))) i = Some index). {
        rewrite map.get_put_diff by congruence. assumption.
      }
      run1det.
      assert (Memory.load sz initialL_mem
                          (word.add (word.add (word.add initialL_pc (word.of_Z 4)) index) (word.of_Z 0))
              = Some v). {
        rewrite add_0_r.
        eapply load_from_compile_byte_list. 1: eassumption.
        wcancel_assumption.
      }
      run1det.
      rewrite !map.put_put_same in *.
      run1done.

    - (* SStackalloc *)
      assert (valid_register RegisterNames.sp) by (cbv; auto).
      specialize (stackalloc_always_0 x n body t mSmall l mc post). move stackalloc_always_0 at bottom.
      assert (n = 0). {
        eapply stackalloc_always_0. econstructor; eauto.
      }
      subst n.
      run1det.
      eapply runsTo_weaken. {
        eapply H1 with (mStack := map.empty) (mCombined := mSmall).
        { unfold Memory.anybytes. exists nil. reflexivity. }
        { rewrite map.split_empty_r. reflexivity. }
        all: IH_sidecondition.
      }
      simpl.
      intros.
      unfold Memory.anybytes, Memory.ftprint, map.of_disjoint_list_zip in *. simpl in *.
      simp.
      rewrite map.split_empty_r in H6p0p1. subst mSmall'.
      repeat match goal with
             | m: _ |- _ => destruct_RiscvMachine m; simpl_MetricRiscvMachine_get_set
             end.
      eexists. eexists.
      split; [eassumption|].
      split; [solve [sidecondition]|].
      split; [solve [sidecondition]|].
      split. {
        subst. solve_word_eq word_ok.
      }
      split; [solve [sidecondition]|].
      split. {
        solve_MetricLog.
      }
      assumption.

    - (* SLit *)
      RunInstruction.get_runsTo_valid_for_free.
      eapply compile_lit_correct_full.
      + sidecondition.
      + use_sep_assumption. cbn.
        (* ecancel. (*  The term  "Tree.Leaf (subset (footpr (program iset initialL_pc (compile_lit x v) * Rexec)%sep))" has type "Tree.Tree (set word -> Prop)" while it is expected to have type "Tree.Tree (?map -> Prop)". *) *)
        eapply RelationClasses.reflexivity.
      + unfold compile_stmt. simpl. ecancel_assumption.
      + sidecondition.
      + assumption.
      + simpl. run1done;
        remember (updateMetricsForLiteral v initialL_metrics) as finalMetrics;
        symmetry in HeqfinalMetrics;
        pose proof update_metrics_for_literal_bounded (width := width) as Hlit;
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
        destruct (eval_bcond middle_regs cond) as [condB|] eqn: E.
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
      on hyp[(stmt_not_too_big s1); runsTo] do (fun H => rename H into IH1).
      on hyp[(stmt_not_too_big s2); runsTo] do (fun H => rename H into IH2).
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
