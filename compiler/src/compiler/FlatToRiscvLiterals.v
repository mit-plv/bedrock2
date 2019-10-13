Require Import riscv.Spec.Decode.
Require Import riscv.Platform.MetricLogging.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Utility.Utility.
Require Import riscv.Utility.runsToNonDet.
Require Import riscv.Utility.prove_Zeq_bitwise.
Require Import compiler.util.Common.
Require Import compiler.SeparationLogic.
Require Import compiler.SimplWordExpr.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.EmitsValid.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvCommon.
Require Import coqutil.Tactics.autoforward.
Import Utility.

Section FlatToRiscvLiterals.
  Context {p: FlatToRiscv.parameters}.
  Context {h: FlatToRiscv.assumptions}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Notation RiscvMachineL := MetricRiscvMachine.

  Definition updateMetricsForLiteral v initialMetrics : MetricLog :=
    let cost :=
        if ((- 2 ^ 11 <=? v)%Z && (v <? 2 ^ 11)%Z)%bool
        then 1
        else
          if ((width =? 32)%Z || (- 2 ^ 31 <=? v)%Z && (v <? 2 ^ 31)%Z)%bool
          then 2
          else 8 in
    addMetricInstructions cost (addMetricLoads cost initialMetrics).

  Lemma update_metrics_for_literal_bounded: forall v initialMetrics finalMetrics,
      updateMetricsForLiteral v initialMetrics = finalMetrics ->
      finalMetrics.(instructions) <= initialMetrics.(instructions) + 8 /\
      finalMetrics.(loads) <= initialMetrics.(loads) + 8 /\
      finalMetrics.(stores) <= initialMetrics.(stores) /\
      finalMetrics.(jumps) <= initialMetrics.(jumps).
  Proof.
    intros. subst.
    unfold updateMetricsForLiteral.
    destruct initialMetrics.
    simpl.
    repeat (destruct_one_match; try blia).
  Qed.

  Ltac match_apply_runsTo :=
    match goal with
    | R: runsTo ?m ?post |- runsToNonDet.runsTo _ ?m' ?post =>
      replace m' with m; [exact R|]
    end.

  Ltac substs :=
    repeat match goal with
           | x := _ |- _ => subst x
           | _: ?x = _ |- _ => subst x
           | _: _ = ?x |- _ => subst x
           end.

  Ltac post_destr db :=
    repeat match goal with
           | E: (_ && _)%bool = true |- _ =>
             let E1 := fresh E in let E2 := fresh E in
             apply andb_prop in E; destruct E as [E1 E2];
             autoforward_in db E1;
             autoforward_in db E2
           end.

  (* mark as Instance? *)
  Lemma andb_spec: forall b1 b2,
      BoolSpec (b1 = true /\ b2 = true) (b1 = false \/ b2 = false) (b1 && b2)%bool.
  Proof.
    intros. destruct b1; destruct b2; constructor; auto.
  Qed.

  Lemma compile_lit_correct_full: forall (initialL: RiscvMachineL) post x v R,
      initialL.(getNextPc) = add initialL.(getPc) (word.of_Z 4) ->
      let insts := compile_stmt (FlatImp.SLit x v) in
      let d := mul (word.of_Z 4) (word.of_Z (Z.of_nat (List.length insts))) in
      (program initialL.(getPc) insts * R)%sep initialL.(getMem) ->
      valid_FlatImp_vars (FlatImp.SLit x v) ->
      runsTo (withRegs (map.put initialL.(getRegs) x (word.of_Z v))
             (withPc     (add initialL.(getPc) d)
             (withNextPc (add initialL.(getNextPc) d)
             (withMetrics (updateMetricsForLiteral v initialL.(getMetrics)) initialL))))
             post ->
      runsTo initialL post.
  Proof.
    intros *. intros E1 insts d P V N. substs.
    lazymatch goal with
    | H1: valid_FlatImp_vars ?s |- _ =>
      pose proof (compile_stmt_emits_valid iset_is_supported H1 eq_refl) as EV
    end.
    simpl in *.
    destruct_RiscvMachine initialL.
    subst.
    unfold compile_lit, updateMetricsForLiteral in *.
    destruct_one_match_hyp; [|destruct_one_match_hyp]; post_destr typeclass_instances.
    - unfold compile_lit_12bit in *.
      run1det.
      simpl_word_exprs word_ok.
      match_apply_runsTo.
      erewrite signExtend_nop; eauto; try blia.
    - (* TODO this step should be automatic *)
      assert (width = 32 \/ - 2 ^ 31 <= v < 2 ^ 31). {
        clear -E0 h.
        apply Bool.orb_true_iff in E0. destruct E0 as [E0 | E0].
        - autoforward_in typeclass_instances E0. auto.
        - post_destr typeclass_instances. auto.
      }
      unfold compile_lit_32bit in *.
      simpl in P.
      run1det. run1det.
      match_apply_runsTo.
      f_equal; [|solve_MetricLog].
      f_equal.
      + rewrite map.put_put_same. f_equal.
        apply word.signed_inj.
        rewrite word.signed_of_Z.
        rewrite word.signed_xor.
        rewrite! word.signed_of_Z.
        change word.swrap with (signExtend width).
        assert (0 < width) as Wpos. {
          clear. destruct width_cases; rewrite H; reflexivity.
        }
        rewrite! signExtend_alt_bitwise by (reflexivity || assumption).
        clear -Wpos H.
        destruct H as [E | B ].
        * rewrite E. unfold signExtend_bitwise. Zbitwise.
        * unfold signExtend_bitwise. Zbitwise.
          (* TODO these should also be solved by Zbitwise *)
          {
            assert (32 <= i < width) by bomega. (* PARAMRECORDS? blia fails *)
            destruct B.
            assert (31 < i) by blia.
            assert (0 < 31) by reflexivity.
            erewrite testbit_above_signed' with (i := i); try eassumption.
            change (Z.log2_up (2 ^ 31)) with (32 - 1).
            Btauto.btauto.
          }
          {
            destruct B.
            assert (0 < 31) by reflexivity.
            assert (31 < width - 1) by blia.
            erewrite testbit_above_signed' with (i := width - 1); try eassumption.
            change (Z.log2_up (2 ^ 31)) with (32 - 1).
            Btauto.btauto.
          }
      + solve_word_eq word_ok.
      + solve_word_eq word_ok.
    - unfold compile_lit_64bit, compile_lit_32bit in *.
      match type of EV with
      | context [ Xori _ _ ?a ] => remember a as mid
      end.
      match type of EV with
      | context [ Z.lxor ?a mid ] => remember a as hi
      end.
      cbv [List.app program array] in P.
      simpl in *. (* if you don't remember enough values, this might take forever *)
      repeat match type of X with
             | _ /\ _ => destruct X as [? X]
             end.
      run1det. repeat unfold_MetricLog.
      run1det. repeat unfold_MetricLog.
      run1det. repeat unfold_MetricLog.
      run1det. repeat unfold_MetricLog.
      run1det. repeat unfold_MetricLog.
      run1det. repeat unfold_MetricLog.
      run1det. repeat unfold_MetricLog.
      run1det. repeat unfold_MetricLog.
      match_apply_runsTo.
      f_equal; [|simpl; solve_MetricLog].
      f_equal.
      + rewrite! map.put_put_same. f_equal. subst.
        apply word.unsigned_inj.
        assert (width = 64) as W64. {
          clear -E0.
          destruct width_cases as [E | E]; rewrite E in *; try reflexivity.
          exfalso. simpl in E0. discriminate E0.
        }
        (repeat rewrite ?word.unsigned_of_Z, ?word.unsigned_xor, ?word.unsigned_slu);
        unfold word.wrap;
        rewrite W64; try reflexivity.
        clear.
        change (10 mod 2 ^ 64) with 10.
        change (11 mod 2 ^ 64) with 11.
        rewrite <-! Z.land_ones by blia.
        rewrite! signExtend_alt_bitwise by reflexivity.
        unfold bitSlice, signExtend_bitwise.
        Zbitwise.
        (* TODO this should be done by Zbitwise, but not too eagerly because it's very
           expensive on large goals *)
        all: replace (i - 11 - 11 - 10 + 32) with i by blia.
        all: Btauto.btauto.
      + solve_word_eq word_ok.
      + solve_word_eq word_ok.
  Qed.

End FlatToRiscvLiterals.
