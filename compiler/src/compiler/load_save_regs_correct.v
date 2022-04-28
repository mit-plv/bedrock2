Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Utility.Utility.
Require Import coqutil.Tactics.Simp.
Require Import compiler.SeparationLogic.
Require Export coqutil.Word.SimplWordExpr.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvCommon.

Section Proofs.
  Context {iset: Decode.InstructionSet}.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {word_ok: word.ok word}.
  Context {locals: map.map Z word}.
  Context {mem: map.map word byte}.
  Context {M: Type -> Type}.
  Context {MM: Monads.Monad M}.
  Context {RVM: Machine.RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {ext_spec: Semantics.ExtSpec}.
  Context {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}.
  Context {locals_ok: map.ok locals}.
  Context {mem_ok: map.ok mem}.
  Context {PR: MetricPrimitives.MetricPrimitives PRParams}.
  Context {BWM: bitwidth_iset width iset}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Notation RiscvMachineL := MetricRiscvMachine.

  Local Arguments Z.add : simpl never.
  Local Arguments Z.of_nat : simpl never.

  Lemma save_regs_correct: forall vars offset Exec R Rexec (initial: RiscvMachineL)
                                  p_sp oldvalues newvalues addr,
      Forall valid_register vars ->
      map.getmany_of_list initial.(getRegs) vars = Some newvalues ->
      map.get initial.(getRegs) RegisterNames.sp = Some p_sp ->
      List.length oldvalues = List.length vars ->
      subset (footpr Exec) (of_list (initial.(getXAddrs))) ->
      iff1 Exec (program iset initial.(getPc) (save_regs iset vars offset) * Rexec)%sep ->
      (Exec * word_array addr oldvalues * R)%sep initial.(getMem) ->
      addr = word.add p_sp (word.of_Z offset) ->
      initial.(getNextPc) = word.add initial.(getPc) (word.of_Z 4) ->
      valid_machine initial ->
      runsTo initial (fun final =>
          final.(getRegs) = initial.(getRegs) /\
          subset (footpr Exec) (of_list (final.(getXAddrs))) /\
          (Exec * word_array addr newvalues * R)%sep final.(getMem) /\
          final.(getPc) = word.add initial.(getPc) (word.mul (word.of_Z 4)
                                                   (word.of_Z (Z.of_nat (List.length vars)))) /\
          final.(getNextPc) = word.add final.(getPc) (word.of_Z 4) /\
          final.(getLog) = initial.(getLog) /\
          final.(getMetrics) =
              Platform.MetricLogging.addMetricInstructions (Z.of_nat (List.length vars))
                (Platform.MetricLogging.addMetricStores (Z.of_nat (List.length vars))
                   (Platform.MetricLogging.addMetricLoads (Z.of_nat (List.length vars)) initial.(getMetrics))) /\   
          valid_machine final).
  Proof.
    unfold map.getmany_of_list.
    induction vars; intros; subst addr.
    - simpl in *. simp. destruct oldvalues; simpl in *; [|discriminate].
      apply runsToNonDet.runsToDone. repeat split; try assumption; try solve_word_eq word_ok.
      destruct_RiscvMachine initial. destruct initial_metrics. MetricsToRiscv.solve_MetricLog. 
    - simpl in *. simp.
      assert (valid_register RegisterNames.sp) by (cbv; auto).
      destruct oldvalues as [|oldvalue oldvalues]; simpl in *; [discriminate|].
      replace (Memory.bytes_per_word (Decode.bitwidth iset)) with bytes_per_word in *. 2: {
        rewrite bitwidth_matches. reflexivity.
      }
      eapply runsToNonDet.runsToStep. {
        eapply run_store_word.
        7: eassumption.
        7: {
          etransitivity. 1: eassumption. cbn. ecancel.
        }
        all: try eassumption.
        1: reflexivity.
        use_sep_assumption; cbn; ecancel.
      }
      simpl. intros.
      destruct_RiscvMachine initial.
      destruct_RiscvMachine mid.
      simp. subst.
      eapply runsToNonDet.runsTo_weaken; cycle 1;
        [|eapply IHvars with (p_sp := p_sp) (offset := (offset + bytes_per_word))
             (newvalues := l) (R := (ptsto_word (word.add p_sp (word.of_Z offset)) r * R)%sep)]. {
        simpl. intros. simp. destruct_RiscvMachine final.
        repeat split; try solve [sidecondition].
        - replace (Z.of_nat (S (List.length oldvalues)))
            with (1 + Z.of_nat (List.length oldvalues)) by blia.
          etransitivity; [eassumption|].
          replace (List.length vars) with (List.length oldvalues) by blia.
          solve_word_eq word_ok.
        - rewrite H0p7. MetricsToRiscv.solve_MetricLog. 
      }
      all: try eassumption.
      + simpl in *. etransitivity. 1: eassumption. ecancel.
      + simpl. use_sep_assumption. wcancel.
      + solve_word_eq word_ok.
      + reflexivity.
  Qed.

  Lemma length_save_regs: forall vars offset,
      List.length (save_regs iset vars offset) = List.length vars.
  Proof using BWM.
    induction vars; intros; simpl; rewrite? IHvars; reflexivity.
  Qed.

  Lemma load_regs_correct: forall p_sp vars offset Exec R Rexec (initial: RiscvMachineL) values,
      Forall valid_FlatImp_var vars ->
      map.get initial.(getRegs) RegisterNames.sp = Some p_sp ->
      List.length values = List.length vars ->
      subset (footpr Exec) (of_list initial.(getXAddrs)) ->
      iff1 Exec (program iset initial.(getPc) (load_regs iset vars offset) * Rexec)%sep ->
      (Exec * word_array (word.add p_sp (word.of_Z offset)) values * R)%sep initial.(getMem) ->
      initial.(getNextPc) = word.add initial.(getPc) (word.of_Z 4) ->
      valid_machine initial ->
      runsTo initial (fun final =>
          map.putmany_of_list_zip vars values initial.(getRegs) = Some final.(getRegs) /\
          final.(getMem) = initial.(getMem) /\
          final.(getPc) = word.add initial.(getPc) (mul (word.of_Z 4)
                                                   (word.of_Z (Z.of_nat (List.length vars)))) /\
          final.(getNextPc) = word.add final.(getPc) (word.of_Z 4) /\
          final.(getLog) = initial.(getLog) /\
          final.(getXAddrs) = initial.(getXAddrs) /\
          final.(getMetrics) =
              Platform.MetricLogging.addMetricInstructions (Z.of_nat (List.length vars))
                (Platform.MetricLogging.addMetricLoads (Z.of_nat (2 * (List.length vars)))
                   initial.(getMetrics)) /\
          valid_machine final).
  Proof.
    induction vars; intros.
    - simpl in *. simp. destruct values; simpl in *; [|discriminate].
      apply runsToNonDet.runsToDone. repeat split; try assumption; try solve_word_eq word_ok.
      destruct_RiscvMachine initial. destruct initial_metrics. MetricsToRiscv.solve_MetricLog. 
    - simpl in *. simp.
      assert (valid_register RegisterNames.sp) by (cbv; auto).
      assert (valid_register a). {
        unfold valid_register, valid_FlatImp_var in *. blia.
      }
      destruct values as [|value values]; simpl in *; [discriminate|].
      eapply runsToNonDet.runsToStep. {
        eapply run_load_word; cycle -4; try solve [sidecondition]; sidecondition.
      }
      simpl. intros.
      destruct_RiscvMachine initial.
      destruct_RiscvMachine mid.
      replace (Memory.bytes_per_word (Decode.bitwidth iset)) with bytes_per_word in *. 2: {
        rewrite bitwidth_matches. reflexivity.
      }
      simp. subst.
      eapply runsToNonDet.runsTo_weaken.
      + eapply IHvars; simpl; cycle -3; auto.
        * use_sep_assumption.
          match goal with
          | |- iff1 ?LHS ?RHS =>
            match LHS with
            | context [word_array ?i] =>
              match RHS with
              | context [word_array ?i'] =>
                replace i with i'; cycle 1
              end
            end
          end.
          { rewrite <- word.add_assoc. rewrite <- word.ring_morph_add. reflexivity. }
          ecancel.
        * rewrite map.get_put_diff. 1: assumption.
          unfold RegisterNames.sp, valid_FlatImp_var in *. blia.
        * blia.
        * eassumption.
        * etransitivity. 1: eassumption. ecancel.
      + simpl. intros. simp.
        ssplit; try first [assumption|reflexivity].
        * etransitivity; [eassumption|].
          rewrite Znat.Nat2Z.inj_succ. rewrite <- Z.add_1_r.
          replace (List.length values) with (List.length vars) by congruence.
          solve_word_eq word_ok.
        * rewrite H1p3. MetricsToRiscv.solve_MetricLog. 
  Qed.

  Lemma length_load_regs: forall vars offset,
      List.length (load_regs iset vars offset) = List.length vars.
  Proof using BWM.
    induction vars; intros; simpl; rewrite? IHvars; reflexivity.
  Qed.

End Proofs.
