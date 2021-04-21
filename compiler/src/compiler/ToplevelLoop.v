Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Export coqutil.Decidable.
Require Import Coq.Program.Tactics.
Require Import coqutil.Tactics.rewr.
Require        compiler.ExprImp.
Require Export compiler.FlattenExprDef.
Require Export compiler.FlattenExpr.
Require        compiler.FlatImp.
Require Export riscv.Spec.Decode.
Require Export riscv.Spec.Machine.
Require Export riscv.Platform.Run.
Require Export riscv.Platform.RiscvMachine.
Require Export riscv.Platform.MetricLogging.
Require Export riscv.Utility.Monads.
Require Import riscv.Utility.runsToNonDet.
Require Export riscv.Platform.MetricRiscvMachine.
Require Import coqutil.Z.Lia.
Require Import compiler.NameGen.
Require Import compiler.StringNameGen.
Require Export compiler.util.Common.
Require Export coqutil.Decidable.
Require Export riscv.Utility.Encode.
Require Export riscv.Spec.Primitives.
Require Export riscv.Spec.MetricPrimitives.
Require Import compiler.GoFlatToRiscv.
Require Import riscv.Utility.MkMachineWidth.
Require Export riscv.Proofs.DecodeEncode.
Require Export riscv.Proofs.EncodeBound.
Require coqutil.Map.SortedList.
Require Import riscv.Utility.Utility.
Require Export riscv.Platform.Memory.
Require Export riscv.Utility.InstructionCoercions.
Require Import compiler.SeparationLogic.
Require Import coqutil.Tactics.Simp.
Require Import compiler.FlattenExprSimulation.
Require Import compiler.RegRename.
Require Import compiler.FlatToRiscvSimulation.
Require Import compiler.Simulation.
Require Import compiler.RiscvEventLoop.
Require Import bedrock2.MetricLogging.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import compiler.DivisibleBy4.
Require Export coqutil.Word.SimplWordExpr.
Require Import compiler.ForeverSafe.
Require Export compiler.MemoryLayout.
Require Import FunctionalExtensionality.
Require Import coqutil.Tactics.autoforward.
Require Import compiler.FitsStack.
Require Import compiler.PipelineWithRename.
Require Import compiler.ExprImpEventLoopSpec.

Existing Instance riscv.Spec.Machine.DefaultRiscvState.

Local Hint Mode word.word - : typeclass_instances.

Open Scope Z_scope.

Local Open Scope ilist_scope.

Local Notation "' x <- a ; f" :=
  (match (a: option _) with
   | x => f
   | _ => None
   end)
  (right associativity, at level 70, x pattern).

Section Pipeline1.

  Context {p: Pipeline.parameters}.
  Context {h: Pipeline.assumptions}.

  Context (ml: MemoryLayout)
          (mlOk: MemoryLayoutOk ml).

  Let init_sp := word.unsigned ml.(stack_pastend).

  Local Notation source_env := (@Pipeline.string_keyed_map p (list string * list string * Syntax.cmd)).

  (* All riscv machine code, layed out from low to high addresses: *)
  (* 1) Initialize stack pointer *)
  Let init_sp_insts := FlatToRiscvDef.compile_lit RegisterNames.sp init_sp.
  Let init_sp_pos := ml.(code_start).
  (* 2) Call init function *)
  Let init_insts init_fun_pos := [[Jal RegisterNames.ra (3 * 4 + init_fun_pos)]].
  Let init_pos := word.add ml.(code_start)
         (word.of_Z (4 * (Z.of_nat (List.length (FlatToRiscvDef.compile_lit RegisterNames.sp init_sp))))).
  (* 3) Call loop function *)
  Let loop_insts loop_fun_pos := [[Jal RegisterNames.ra (2 * 4 + loop_fun_pos)]].
  Let loop_pos := word.add init_pos (word.of_Z 4).
  (* 4) Jump back to 3) *)
  Let backjump_insts := [[Jal Register0 (-4)]].
  Let backjump_pos := word.add loop_pos (word.of_Z 4).
  (* 5) Code of the compiled functions *)
  Let functions_pos := word.add backjump_pos (word.of_Z 4).

  Definition compile_prog(prog: source_env): option (list Instruction * funname_env Z) :=
    'Some (functions_insts, positions) <- @compile p ml prog;
    'Some init_fun_pos <- map.get positions "init"%string;
    'Some loop_fun_pos <- map.get positions "loop"%string;
    let to_prepend := init_sp_insts ++ init_insts init_fun_pos ++ loop_insts loop_fun_pos ++ backjump_insts in
    Some (to_prepend ++ functions_insts, positions).

  Context (spec: @ProgramSpec (FlattenExpr.mk_Semantics_params _)).

  (* Holds each time before executing the loop body *)
  Definition ll_good(done: bool)(mach: MetricRiscvMachine): Prop :=
    exists (prog: source_env) (functions_instrs: list Instruction) (positions: funname_env Z)
           (init_fun_pos loop_fun_pos: Z) (R: mem -> Prop),
      compile ml prog = Some (functions_instrs, positions) /\
      ProgramSatisfiesSpec "init"%string "loop"%string prog spec /\
      map.get positions "init"%string = Some init_fun_pos /\
      map.get positions "loop"%string = Some loop_fun_pos /\
      exists mH,
        isReady spec mach.(getLog) mH /\ goodTrace spec mach.(getLog) /\
        machine_ok functions_pos loop_fun_pos ml.(stack_start) ml.(stack_pastend) functions_instrs
                   loop_pos (word.add loop_pos (word.of_Z (if done then 4 else 0))) mH R
                   (* all instructions which are not part of the loop body (jump to loop body function)
                      or the compiled functions: *)
                   (program iset init_sp_pos init_sp_insts *
                    program iset init_pos (init_insts init_fun_pos) *
                    program iset backjump_pos backjump_insts)%sep
                   mach.

  Definition ll_inv: MetricRiscvMachine -> Prop := runsToGood_Invariant ll_good iset.

  Add Ring wring : (word.ring_theory (word := Utility.word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := Utility.word)),
       constants [word_cst]).

  Hint Extern 1 (map.ok _) => refine mem_ok : typeclass_instances.

  Lemma machine_ok_change_call: forall functions_pos f_entry_rel_pos_1 f_entry_rel_pos_2
                                       p_stack_start p_stack_pastend instrs
                                       p_call_1 p_call_2 pc mH Rdata Rexec Rexec1 mach,
      iff1 Rexec1 (Rexec * ptsto_instr iset p_call_2 (Jal RegisterNames.ra
                    (f_entry_rel_pos_2 + word.signed (word.sub functions_pos p_call_2))))%sep ->
      machine_ok functions_pos
                 f_entry_rel_pos_2
                 p_stack_start p_stack_pastend instrs
                 p_call_2
                 pc mH Rdata
                 (Rexec * ptsto_instr iset p_call_1 (Jal RegisterNames.ra
                            (f_entry_rel_pos_1 + word.signed (word.sub functions_pos p_call_1))))%sep
                 mach ->
      machine_ok functions_pos
                 f_entry_rel_pos_1
                 p_stack_start p_stack_pastend instrs
                 p_call_1
                 pc mH Rdata Rexec1
                 mach.
  Proof.
    (* PARAMRECORDS: only works because of Hint Extern refine for compiler.FlatToRiscvCommon.mem_ok *)
    unfold machine_ok, program.
    intros. simp; ssplit; eauto.
    - seprewrite H. wcancel_assumption.
    - eapply shrink_footpr_subset. 1: eassumption.
      rewrite H.
      wwcancel.
  Qed.

  Definition initial_conditions(initial: MetricRiscvMachine): Prop :=
    exists (srcprog: source_env) (instrs: list Instruction) (positions: funname_env Z) (R: mem -> Prop),
      ProgramSatisfiesSpec "init"%string "loop"%string srcprog spec /\
      spec.(datamem_start) = ml.(heap_start) /\
      spec.(datamem_pastend) = ml.(heap_pastend) /\
      compile_prog srcprog = Some (instrs, positions) /\
      word.unsigned ml.(code_start) + Z.of_nat (List.length (instrencode instrs)) <=
        word.unsigned ml.(code_pastend) /\
      subset (footpr (program iset ml.(code_start) instrs)) (of_list initial.(getXAddrs)) /\
      (program iset ml.(code_start) instrs * R *
       mem_available ml.(heap_start) ml.(heap_pastend) *
       mem_available ml.(stack_start) ml.(stack_pastend))%sep initial.(getMem) /\
      initial.(getPc) = ml.(code_start) /\
      initial.(getNextPc) = word.add initial.(getPc) (word.of_Z 4) /\
      regs_initialized initial.(getRegs) /\
      initial.(getLog) = nil /\
      valid_machine initial.

  Lemma signed_of_Z_small: forall c,
      - 2 ^ 31 <= c < 2 ^ 31 ->
      word.signed (word.of_Z c) = c.
  Proof.
    clear -h.
    simpl.
    intros.
    eapply word.signed_of_Z_nowrap.
    case width_cases as [E | E]; rewrite E; Lia.lia.
  Qed.

  Lemma establish_ll_inv: forall (initial: MetricRiscvMachine),
      initial_conditions initial ->
      ll_inv initial.
  Proof.
    unfold initial_conditions.
    intros. simp.
    unfold ll_inv, runsToGood_Invariant. split; [|assumption].
    destruct_RiscvMachine initial.
    match goal with
    | H: context[ProgramSatisfiesSpec] |- _ => rename H into sat
    end.
    pose proof sat.
    destruct sat.
    match goal with
    | H: compile_prog srcprog = Some _ |- _ => pose proof H as CP; unfold compile_prog in H
    end.
    remember instrs as instrs0.
    simp.
    assert (map.ok mem) by exact mem_ok.
    assert (word.ok Semantics.word) by exact word_ok.
    eassert ((mem_available ml.(heap_start) ml.(heap_pastend) * _)%sep initial_mem) as SplitImem. {
      ecancel_assumption.
    }
    destruct SplitImem as [heap_mem [other_mem [SplitHmem [HMem OtherMem] ] ] ].
    evar (after_init_sp: MetricRiscvMachine).
    eapply runsTo_trans with (P := fun mach => valid_machine mach /\ mach = after_init_sp);
      subst after_init_sp.
    {
      get_run1valid_for_free.
      (* first, run init_sp_code: *)
      pose proof FlatToRiscvLiterals.compile_lit_correct_full_raw as P.
      cbv zeta in P. (* needed for COQBUG https://github.com/coq/coq/issues/11253 *)
      specialize P with (x := RegisterNames.sp) (v := init_sp).
      unfold runsTo in P. eapply P; clear P; simpl.
      - assumption.
      - eapply rearrange_footpr_subset. 1: eassumption.
        wwcancel.
      - wcancel_assumption.
      - cbv. auto.
      - assumption.
      - eapply runsToDone. split; [exact I|reflexivity].
    }
    specialize init_code_correct with (mc0 := (bedrock2.MetricLogging.mkMetricLog 0 0 0 0)).
    match goal with
    | H: map.get positions "init"%string = Some ?pos |- _ =>
      rename H into GetPos, pos into f_entry_rel_pos
    end.
    subst.
    intros. simp.
    (* then, run init_code (using compiler simulation and correctness of init_code) *)
    eapply runsTo_weaken.
    - pose proof compiler_correct as P. unfold runsTo in P.
      specialize P with (p_functions := word.add loop_pos (word.of_Z 8)) (Rdata := R).
      unfold ll_good.
      eapply P; clear P.
      6: {
        unfold hl_inv in init_code_correct.
        simpl.
        move init_code_correct at bottom.
        subst.
        refine (init_code_correct _ _).
        replace (datamem_start spec) with (heap_start ml) by congruence.
        replace (datamem_pastend spec) with (heap_pastend ml) by congruence.
        exact HMem.
      }
      all: try eassumption.
      unfold machine_ok.
      unfold_RiscvMachine_get_set.
      repeat match goal with
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             | |- _ => progress cbv beta iota
             | |- _ => eassumption
             | |- _ => reflexivity
             end.
      2: {
        eapply rearrange_footpr_subset. 1: eassumption.
        wseplog_pre.
        simpl_addrs.
        subst loop_pos init_pos.
        match goal with
        | |- iff1 ?LL ?RR =>
          match LL with
          | context[ptsto_instr _ ?A1 (IInstruction (Jal RegisterNames.ra ?J1))] =>
            match RR with
            | context[ptsto_instr _ ?A2 (IInstruction (Jal RegisterNames.ra ?J2))] =>
              unify A1 A2;
              replace J2 with J1
            end
          end
        end.
        2: {
          match goal with
          | |- context[word.signed ?x] => ring_simplify x
          end.
          rewrite signed_of_Z_small.
          - ring.
          - clear. cbv. intuition discriminate.
        }
        wcancel.
        cancel_seps_at_indices 3%nat 0%nat. {
          f_equal.
          solve_word_eq word_ok.
          clear backjump_insts.
          subst init_sp_insts.
          solve_word_eq word_ok.
        }
        cbn[seps].
        reflexivity.
      }
      {
        (* need to deal with "eq heap_mem" separately *)
        exists other_mem, heap_mem. ssplit.
        3: reflexivity.
        1: exact (proj1 (map.split_comm _ _ _) SplitHmem).
        unfold program in *.
        use_sep_assumption.
        wseplog_pre.
        simpl_addrs.
        subst loop_pos init_pos.
        match goal with
        | |- iff1 ?LL ?RR =>
          match LL with
          | context[ptsto_instr _ ?A1 (IInstruction (Jal RegisterNames.ra ?J1))] =>
            match RR with
            | context[ptsto_instr _ ?A2 (IInstruction (Jal RegisterNames.ra ?J2))] =>
              unify A1 A2;
              replace J2 with J1
            end
          end
        end.
        2: {
          match goal with
          | |- context[word.signed ?x] => ring_simplify x
          end.
          rewrite signed_of_Z_small.
          - ring.
          - clear. cbv. intuition discriminate.
        }
        wcancel.
        cancel_seps_at_indices 0%nat 0%nat. {
          f_equal.
          solve_word_eq word_ok.
          subst init_sp_insts.
          solve_word_eq word_ok.
        }
        cbn [seps].
        reflexivity.
      }
      + destruct mlOk. solve_divisibleBy4.
      + solve_word_eq word_ok.
      + rapply regs_initialized_put. eassumption.
      + rewrite map.get_put_same. unfold init_sp. rewrite word.of_Z_unsigned. reflexivity.
    - cbv beta. unfold ll_good. intros. simp.
      rename z0 into f_loop_rel_pos.
      repeat match goal with
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             | |- _ => progress cbv beta iota
             | |- _ => eassumption
             | |- _ => reflexivity
             end.
      + move CP at bottom.
        (* prove that machine_ok of ll_inv (i.e. all instructions, and just before jumping calling
           loop body function) is implied by the state proven by the compiler correctness lemma for
           the init function *)
        eapply machine_ok_change_call with (p_call_2 := init_pos)
                                           (f_entry_rel_pos_2 := f_entry_rel_pos).
        { unfold init_insts, functions_pos, backjump_pos, loop_pos, init_pos.
          wseplog_pre.
          cancel.
          cancel_seps_at_indices 1%nat 1%nat. {
            f_equal. f_equal. f_equal.
            match goal with
            | |- context[word.signed ?x] => ring_simplify x
            end.
            rewrite signed_of_Z_small.
            - ring.
            - clear. cbv. intuition discriminate.
          }
          cbn [seps].
          reflexivity.
        }
        lazymatch goal with
        | H: context[machine_ok] |- ?G => let G' := type of H in replace G with G'; [exact H|clear H]
        end.
        f_equal.
        * unfold functions_pos, backjump_pos. solve_word_eq word_ok.
        * unfold init_pos. solve_word_eq word_ok.
        * unfold loop_pos, init_pos. solve_word_eq word_ok.
        * eapply iff1ToEq.
          wwcancel.
          cancel_seps_at_indices 1%nat 0%nat. {
            f_equal. unfold init_sp_insts.
            solve_word_eq word_ok.
          }
          cancel_seps_at_indices 0%nat 0%nat. {
            f_equal.
            - unfold loop_pos, init_pos, init_sp_insts. solve_word_eq word_ok.
            - do 2 f_equal.
              unfold init_insts, functions_pos, backjump_pos, loop_pos, init_pos.
              match goal with
              | |- context[word.signed ?x] => ring_simplify x
              end.
              rewrite signed_of_Z_small.
              + ring.
              + clear. cbv. intuition discriminate.
          }
          cbn [seps].
          reflexivity.
  Qed.

  Lemma ll_inv_is_invariant: forall (st: MetricRiscvMachine),
      ll_inv st -> GoFlatToRiscv.mcomp_sat (run1 iset) st ll_inv.
  Proof.
    (* PARAMRECORDS: only works because of Hint Extern refine for compiler.FlatToRiscvCommon.mem_ok *)
    intros st. unfold ll_inv.
    eapply runsToGood_is_Invariant with (jump := - 4) (pc_start := loop_pos)
                                        (pc_end := word.add loop_pos (word.of_Z 4)).
    - intro D.
      apply (f_equal word.unsigned) in D.
      rewrite word.unsigned_add in D.
      rewrite word.unsigned_of_Z in D.
      unfold word.wrap in D.
      rewrite (Z.mod_small 4) in D; cycle 1. {
        simpl. pose proof four_fits. blia.
      }
      rewrite Z.mod_eq in D by apply pow2width_nonzero.
      let ww := lazymatch type of D with context [(2 ^ ?ww)] => ww end in set (w := ww) in *.
      progress replace w with (w - 2 + 2) in D at 3 by blia.
      rewrite Z.pow_add_r in D by (subst w; destruct width_cases as [E | E]; simpl in *; blia).
      change (2 ^ 2) with 4 in D.
      match type of D with
      | ?x = ?x + 4 - ?A * 4 * ?B => assert (A * B = 1) as C by blia
      end.
      apply Z.eq_mul_1 in C.
      destruct C as [C | C];
        subst w; destruct width_cases as [E | E]; simpl in *; rewrite E in C; cbv in C; discriminate C.
    - intros.
      unfold ll_good, machine_ok in *.
      simp.
      etransitivity. 1: eassumption.
      destruct done; solve_word_eq word_ok.
    - (* Show that ll_ready (almost) ignores pc, nextPc, and metrics *)
      intros.
      unfold ll_good, machine_ok in *.
      simp.
      destr_RiscvMachine state.
      repeat match goal with
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             | |- _ => progress cbv beta iota
             | |- _ => eassumption
             | |- _ => reflexivity
             end.
      + destruct mlOk. subst. simpl in *. subst loop_pos init_pos. solve_divisibleBy4.
      + solve_word_eq word_ok.
    - unfold ll_good, machine_ok.
      intros. simp. assumption.
    - cbv. intuition discriminate.
    - solve_divisibleBy4.
    - solve_word_eq word_ok.
    - unfold ll_good, machine_ok.
      intros. simp. split.
      + eexists. subst backjump_pos backjump_insts. wcancel_assumption.
      + eapply shrink_footpr_subset. 1: eassumption.
        subst backjump_pos backjump_insts.
        wwcancel.
    - (* use compiler correctness for loop body *)
      intros.
      unfold ll_good in *. simp.
      match goal with
      | H: ProgramSatisfiesSpec _ _ _ _ |- _ => pose proof H as sat; destruct H
      end.
      unfold hl_inv in loop_body_correct.
      specialize loop_body_correct with (l := map.empty) (mc := bedrock2.MetricLogging.mkMetricLog 0 0 0 0).
      lazymatch goal with
      | H: context[@word.add ?w ?wo ?x (word.of_Z 0)] |- _ =>
        replace (@word.add w wo x (word.of_Z 0)) with x in H
      end.
      2: solve_word_eq word_ok.
      subst.
      eapply runsTo_weaken.
      + pose proof compiler_correct as P. unfold runsTo in P.
        eapply P; clear P. 6: {
          eapply loop_body_correct; eauto.
        }
        all: try eassumption.
      + cbv beta.
        intros. simp. eauto 15.
  Qed.

  Lemma ll_inv_implies_prefix_of_good: forall st,
      ll_inv st -> exists suff, spec.(goodTrace) (suff ++ st.(getLog)).
  Proof.
    unfold ll_inv, runsToGood_Invariant. intros. simp.
    eapply extend_runsTo_to_good_trace. 2,3: eassumption.
    simpl. unfold ll_good, compile_inv, related, hl_inv,
           compose_relation, FlattenExprSimulation.related,
           RegRename.related, FlatToRiscvSimulation.related, FlatToRiscvCommon.goodMachine.
    intros. simp. eassumption.
  Qed.

End Pipeline1.
