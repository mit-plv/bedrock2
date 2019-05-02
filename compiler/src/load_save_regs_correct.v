Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.Tactics.
Require Import riscv.Spec.Decode.
Require Import riscv.Spec.Primitives.
Require Import riscv.Platform.RiscvMachine.
Require Import riscv.Platform.MetricRiscvMachine.
Require Import riscv.Utility.Utility.
Require Import compiler.Simp.
Require Import compiler.SeparationLogic.
Require Import compiler.SimplWordExpr.
Require Import compiler.GoFlatToRiscv.
Require Import compiler.DivisibleBy4.
Require Import compiler.EmitsValid.
Require Import compiler.FlatToRiscvDef.
Require Import compiler.FlatToRiscvCommon.


Section Proofs.
  Context {p: FlatToRiscv.parameters}.
  Context {h: FlatToRiscv.assumptions}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Notation RiscvMachineL := MetricRiscvMachine.

  (* x0 is the constant 0, x1 is ra, x2 is sp, the others are usable *)
  Definition valid_FlatImp_var(x: Register): Prop := 3 <= x < 32.

  Lemma save_regs_correct: forall vars offset R (initial: RiscvMachineL) p_sp oldvalues newvalues,
      Forall valid_register vars ->
      - 2 ^ 11 <= offset < 2 ^ 11 - bytes_per_word * Z.of_nat (List.length vars) ->
      divisibleBy4 initial.(getPc) ->
      map.getmany_of_list initial.(getRegs) vars = Some newvalues ->
      map.get initial.(getRegs) RegisterNames.sp = Some p_sp ->
      List.length oldvalues = List.length vars ->
      (program initial.(getPc) (save_regs vars offset) *
       word_array (word.add p_sp (word.of_Z offset)) oldvalues * R)%sep initial.(getMem) ->
      initial.(getNextPc) = word.add initial.(getPc) (word.of_Z 4) ->
      runsTo initial (fun final =>
          final.(getRegs) = initial.(getRegs) /\
          (program initial.(getPc) (save_regs vars offset) *
           word_array (word.add p_sp (word.of_Z offset)) newvalues * R)%sep
              final.(getMem) /\
          final.(getPc) = word.add initial.(getPc) (word.mul (word.of_Z 4)
                                                   (word.of_Z (Z.of_nat (List.length vars)))) /\
          final.(getNextPc) = word.add final.(getPc) (word.of_Z 4)).
  Proof.
    unfold map.getmany_of_list.
    induction vars; intros.
    - simpl in *. simp. destruct oldvalues; simpl in *; [|discriminate].
      apply runsToNonDet.runsToDone. repeat split; try assumption; try solve_word_eq word_ok.
    - simpl in *. simp.
      assert (valid_register RegisterNames.sp) by (cbv; auto).
      assert (valid_instructions EmitsValid.iset
                [(compile_store Syntax.access_size.word RegisterNames.sp a offset)]). {
        eapply compile_store_emits_valid; try eassumption.
        assert (bytes_per_word * Z.of_nat (S (List.length vars)) > 0). {
          unfold Z.of_nat.
          unfold bytes_per_word, Memory.bytes_per in *.
          destruct width_cases as [E1 | E1]; rewrite E1; reflexivity.
        }
        simpl. bomega.
      }
      destruct oldvalues as [|oldvalue oldvalues]; simpl in *; [discriminate|].
      eapply runsToNonDet.runsToStep. {
        eapply run_store_word; try solve [sidecondition].
      }
      simpl. intros.
      destruct_RiscvMachine initial.
      destruct_RiscvMachine mid.
      simp. subst.
      eapply runsToNonDet.runsTo_weaken; cycle 1; [|eapply IHvars]. {
        simpl. intros. simp.
        repeat split; try solve [sidecondition].
        - (* TODO all of this should be one more powerful cancel tactic
             with matching of addresses using ring *)
          use_sep_assumption.
          cancel.
          unfold program.
          symmetry.
          cancel_seps_at_indices 1%nat 0%nat; [reflexivity|].
          rewrite word.ring_morph_add.
          rewrite word.add_assoc.
          ecancel_step.
          ecancel.
        - replace (Z.of_nat (S (List.length oldvalues)))
            with (1 + Z.of_nat (List.length oldvalues)) by blia.
          etransitivity; [eassumption|].
          replace (List.length vars) with (List.length oldvalues) by blia.
          solve_word_eq word_ok.
      }
      all: try eassumption.
      + rewrite Znat.Nat2Z.inj_succ in *. rewrite <- Z.add_1_r in *.
        rewrite Z.mul_add_distr_l in *.
        remember (bytes_per_word * BinInt.Z.of_nat (List.length vars)) as K.
        assert (bytes_per_word > 0). {
          unfold bytes_per_word, Memory.bytes_per in *.
          destruct width_cases as [E1 | E1]; rewrite E1; reflexivity.
        }
        bomega.
      + simpl. solve_divisibleBy4.
      + simpl. pseplog.
        rewrite word.ring_morph_add.
        rewrite word.add_assoc.
        ecancel.
      + reflexivity.
  Qed.

  Lemma length_save_regs: forall vars offset,
      List.length (save_regs vars offset) = List.length vars.
  Proof.
    induction vars; intros; simpl; rewrite? IHvars; reflexivity.
  Qed.

  Lemma load_regs_correct: forall p_sp vars offset R (initial: RiscvMachineL) values,
      Forall valid_FlatImp_var vars ->
      NoDup vars ->
      - 2 ^ 11 <= offset < 2 ^ 11 - bytes_per_word * Z.of_nat (List.length vars) ->
      divisibleBy4 initial.(getPc) ->
      map.get initial.(getRegs) RegisterNames.sp = Some p_sp ->
      List.length values = List.length vars ->
      (program initial.(getPc) (load_regs vars offset) *
       word_array (word.add p_sp (word.of_Z offset)) values * R)%sep initial.(getMem) ->
      initial.(getNextPc) = word.add initial.(getPc) (word.of_Z 4) ->
      runsTo initial (fun final =>
          map.only_differ initial.(getRegs) (PropSet.of_list vars) final.(getRegs) /\
          map.getmany_of_list final.(getRegs) vars = Some values /\
          (program initial.(getPc) (load_regs vars offset) *
           word_array (word.add p_sp (word.of_Z offset)) values * R)%sep
              final.(getMem) /\
          final.(getPc) = word.add initial.(getPc) (mul (word.of_Z 4)
                                                   (word.of_Z (Z.of_nat (List.length vars)))) /\
          final.(getNextPc) = word.add final.(getPc) (word.of_Z 4)).
  Proof.
    induction vars; intros.
    - simpl in *. simp. destruct values; simpl in *; [|discriminate].
      apply runsToNonDet.runsToDone. repeat split; try assumption; try solve_word_eq word_ok.
      unfold map.only_differ. auto.
    - simpl in *. simp.
      assert (valid_register RegisterNames.sp) by (cbv; auto).
      assert (valid_register a). {
        unfold valid_register, valid_FlatImp_var in *. blia.
      }
      assert (valid_instructions EmitsValid.iset
                [(compile_load Syntax.access_size.word a RegisterNames.sp offset)]). {
        eapply compile_load_emits_valid; try eassumption.
        assert (bytes_per_word * Z.of_nat (S (List.length vars)) > 0). {
          unfold Z.of_nat.
          unfold bytes_per_word, Memory.bytes_per in *.
          destruct width_cases as [E1 | E1]; rewrite E1; reflexivity.
        }
        simpl. bomega.
      }
      destruct values as [|value values]; simpl in *; [discriminate|].
      eapply runsToNonDet.runsToStep. {
        eapply run_load_word; try solve [sidecondition].
      }
      simpl. intros.
      destruct_RiscvMachine initial.
      destruct_RiscvMachine mid.
      simp. subst.
      eapply runsToNonDet.runsTo_weaken.
      + eapply IHvars; simpl; cycle -2; auto.
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
        * unfold bytes_per_word, Memory.bytes_per in *.
          rewrite Znat.Nat2Z.inj_succ in *. rewrite <- Z.add_1_r in *.
          rewrite Z.mul_add_distr_l in *.
          assert (bytes_per_word > 0). {
            unfold bytes_per_word, Memory.bytes_per in *.
            destruct width_cases as [E1 | E1]; rewrite E1; reflexivity.
          }
          bomega.
        * solve_divisibleBy4.
        * rewrite map.get_put_diff. 1: assumption.
          unfold RegisterNames.sp, valid_FlatImp_var in *. blia.
        * blia.
      + simpl. intros. simp.
        repeat split.
        * unfold map.only_differ, PropSet.elem_of, PropSet.of_list in *.
          intros x. rename H6 into HO.
          specialize (HO x).
          destruct (Z.eqb_spec x a).
          -- subst x. left. constructor. reflexivity.
          -- destruct HO as [HO | HO].
             ++ simpl. auto.
             ++ right. rewrite <- HO. rewrite map.get_put_diff; congruence.
        * unfold map.getmany_of_list in *. simpl. rewrite_match.
          rename H6 into HO.
          specialize (HO a). destruct HO as [HO | HO].
          -- unfold PropSet.elem_of, PropSet.of_list in HO. contradiction.
          -- unfold Register, MachineInt in *. rewrite <- HO.
             rewrite map.get_put_same. reflexivity.
        * pseplog.
          match goal with
          | |- iff1 ?LHS ?RHS =>
            match LHS with
            | context [word_array ?i] =>
              match RHS with
              | context [word_array ?i'] =>
                replace i with i' by solve_word_eq word_ok
              end
            end
          end.
          ecancel.
        * etransitivity; [eassumption|].
          rewrite Znat.Nat2Z.inj_succ. rewrite <- Z.add_1_r.
          replace (List.length values) with (List.length vars) by congruence.
          solve_word_eq word_ok.
        * assumption.
  Qed.

  Lemma length_load_regs: forall vars offset,
      List.length (load_regs vars offset) = List.length vars.
  Proof.
    induction vars; intros; simpl; rewrite? IHvars; reflexivity.
  Qed.

End Proofs.
