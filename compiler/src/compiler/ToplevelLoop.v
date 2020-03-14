Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Export coqutil.Decidable.
Require Import coqutil.Tactics.rewr.
Require        compiler.ExprImp.
Require Export compiler.FlattenExprDef.
Require Export compiler.FlattenExpr.
Require        compiler.FlatImp.
Require Export riscv.Spec.Decode.
Require Export riscv.Spec.Machine.
Require Export riscv.Platform.Run.
Require Export riscv.Platform.Minimal.
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
Require Export compiler.EmitsValid.
Require coqutil.Map.SortedList.
Require Import riscv.Utility.Utility.
Require Export riscv.Platform.Memory.
Require Export riscv.Utility.InstructionCoercions.
Require Import compiler.SeparationLogic.
Require Import compiler.Simp.
Require Import compiler.FlattenExprSimulation.
Require Import compiler.RegRename.
Require Import compiler.FlatToRiscvSimulation.
Require Import compiler.Simulation.
Require Import compiler.RiscvEventLoop.
Require Import bedrock2.MetricLogging.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import compiler.DivisibleBy4.
Require Import compiler.SimplWordExpr.
Require Import compiler.ForeverSafe.
Require Export compiler.MemoryLayout.
Require Import FunctionalExtensionality.
Require Import coqutil.Tactics.autoforward.
Require Import compiler.FitsStack.
Require Import compiler.PipelineWithRename.
Require Import compiler.ExprImpEventLoopSpec.

Existing Instance riscv.Spec.Machine.DefaultRiscvState.

Open Scope Z_scope.

Local Open Scope ilist_scope.

Local Notation "' x <- a ; f" :=
  (match (a: option _) with
   | x => f
   | _ => None
   end)
  (right associativity, at level 70, x pattern).

Local Axiom TODO_sam: False.

(* TODO move to coqutil *)
Ltac rewr_hyp_step getEq :=
  match goal with
  | H: ?A |- _  => let E := getEq A in
                   lazymatch type of E with
                   | ?LHS = _ => progress (pattern LHS in H;
                                           apply (rew_zoom_fw E) in H)
                   end
  end.

Ltac rewr_goal_step getEq :=
  lazymatch goal with
  | |- ?A => let E := getEq A in
             lazymatch type of E with
             | ?LHS = _ => progress (pattern LHS;
                                     apply (rew_zoom_bw E))
             end
  end.

Tactic Notation "rewr" tactic(getEq) "in" "*|-" := repeat (idtac; rewr_hyp_step ltac:(getEq)).
Tactic Notation "rewr" tactic(getEq) "in" "|-*" := repeat (idtac; rewr_goal_step ltac:(getEq)).
Tactic Notation "rewr" tactic(getEq) "in" "*" := rewr getEq in *|-; rewr getEq in |-*.

(* TODO move to compiler.SeparationLogic and dedup *)
Ltac get_array_rewr_eq t :=
  lazymatch t with
  | context [ array ?PT ?SZ ?start (?xs ++ ?ys) ] =>
    constr:(iff1ToEq (array_append' PT SZ xs ys start))
  | context [ array ?PT ?SZ ?start (?x :: ?xs) ] =>
    constr:(iff1ToEq (array_cons PT SZ x xs start))
  | context [ array ?PT ?SZ ?start nil ] =>
    constr:(iff1ToEq (array_nil PT SZ start))
  end.

Ltac array_app_cons_sep := rewr get_array_rewr_eq in *.

Section Pipeline1.

  Context {p: Pipeline.parameters}.
  Context {h: Pipeline.assumptions}.

  Context (ml: MemoryLayout)
          (mlOk: MemoryLayoutOk ml).

  Let init_sp := word.unsigned ml.(stack_pastend).

  Local Notation source_env := (@Pipeline.string_keyed_map p (list string * list string * Syntax.cmd)).


  (* All riscv machine code, layed out from low to high addresses:
     - init_sp_insts: initializes stack pointer
     - init_insts: calls init function
     - loop_insts: calls loop function
     - backjump_insts: jumps back to calling loop function
     - fun_insts: code of compiled functions *)
  Definition compile_prog(prog: source_env): option (list Instruction * funname_env Z) :=
    'Some (fun_insts, positions) <- @compile p ml prog;
    let init_sp_insts := FlatToRiscvDef.compile_lit RegisterNames.sp init_sp in
    'Some init_fun_pos <- map.get positions "init"%string;
    'Some loop_fun_pos <- map.get positions "loop"%string;
    let init_insts := [[Jal RegisterNames.ra (3 * 4 + init_fun_pos)]] in
    let loop_insts := [[Jal RegisterNames.ra (2 * 4 + loop_fun_pos)]] in
    let backjump_insts := [[Jal Register0 (-4*Z.of_nat (List.length loop_insts))]] in
    let to_prepend := init_sp_insts ++ init_insts ++ loop_insts ++ backjump_insts in
    Some (to_prepend ++ fun_insts, positions).

  Context (spec: @ProgramSpec (FlattenExpr.mk_Semantics_params _)).

  Let init_pos := word.add ml.(code_start)
         (word.of_Z (4 * (Z.of_nat (List.length (FlatToRiscvDef.compile_lit RegisterNames.sp init_sp))))).
  Let loop_pos := word.add init_pos (word.of_Z 4).
  Let functions_pos := word.add loop_pos (word.of_Z 8).

  Definition ll_good(done: bool)(mach: MetricRiscvMachine): Prop :=
    exists (prog: source_env) (instrs: list Instruction) (positions: funname_env Z)
           (loop_fun_pos: Z) (R Rexec: mem -> Prop),
      compile_prog prog = Some (instrs, positions) /\
      ProgramSatisfiesSpec "init"%string "loop"%string prog spec /\
      map.get positions "loop"%string = Some loop_fun_pos /\
      exists mH,
        isReady spec mach.(getLog) mH /\ goodTrace spec mach.(getLog) /\
        machine_ok ml.(code_start) functions_pos loop_fun_pos ml.(stack_start) ml.(stack_pastend) instrs
                   loop_pos (word.add loop_pos (word.of_Z (if done then 4 else 0))) mH R Rexec mach.

  Definition ll_inv: MetricRiscvMachine -> Prop := runsToGood_Invariant ll_good.

  Add Ring wring : (word.ring_theory (word := Utility.word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := Utility.word)),
       constants [word_cst]).

  Lemma compile_prog_to_compile: forall prog instrs positions,
      compile_prog prog = Some (instrs, positions) ->
      exists before main,
        compile ml prog = Some (main, positions) /\
        instrs = before ++ main.
  Proof.
    intros. unfold compile_prog in *. simp. do 2 eexists.
    split; reflexivity.
  Qed.

  Lemma machine_ok_frame_instrs_app_l: forall p_code functions_pos f_entry_rel_pos
                                              p_stack_start p_stack_pastend i1 i2
                                              p_call pc mH Rdata Rexec mach,
      machine_ok (word.add p_code (word.of_Z (4 * Z.of_nat (List.length i1))))
                 functions_pos f_entry_rel_pos p_stack_start p_stack_pastend
                 i2
                 p_call pc mH Rdata
                 (Rexec * program p_code i1)%sep
                 mach <->
      machine_ok p_code
                 functions_pos f_entry_rel_pos p_stack_start p_stack_pastend
                 (i1 ++ i2)
                 p_call pc mH Rdata
                 Rexec
                 mach.
  Proof.
    (* PARAMRECORDS *)
    assert (Ok: map.ok Pipeline.mem) by exact mem_ok.
    unfold machine_ok, program.
    intros. split; intros; simp; ssplit; eauto.
    - wcancel_assumption.
    - eapply shrink_footpr_subset. 1: eassumption.
      wwcancel.
    - wcancel_assumption.
    - eapply shrink_footpr_subset. 1: eassumption.
      wwcancel.
  Qed.

  Lemma machine_ok_change_call: forall p_code functions_pos f_entry_rel_pos_1 f_entry_rel_pos_2
                                       p_stack_start p_stack_pastend instrs
                                       p_call_1 p_call_2 pc mH Rdata Rexec Rexec1 mach,
      iff1 Rexec1 (Rexec * ptsto_instr p_call_2 (Jal RegisterNames.ra
                    (f_entry_rel_pos_2 + word.unsigned functions_pos - word.unsigned p_call_2)))%sep ->
      machine_ok p_code functions_pos
                 f_entry_rel_pos_2
                 p_stack_start p_stack_pastend instrs
                 p_call_2
                 pc mH Rdata
                 (Rexec * ptsto_instr p_call_1 (Jal RegisterNames.ra
                            (f_entry_rel_pos_1 + word.unsigned functions_pos - word.unsigned p_call_1)))%sep
                 mach ->
      machine_ok p_code functions_pos
                 f_entry_rel_pos_1
                 p_stack_start p_stack_pastend instrs
                 p_call_1
                 pc mH Rdata Rexec1
                 mach.
  Proof.
    (* PARAMRECORDS *)
    assert (Ok: map.ok Pipeline.mem) by exact mem_ok.
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
      subset (footpr (program ml.(code_start) instrs)) (of_list initial.(getXAddrs)) /\
      (program ml.(code_start) instrs * R *
       mem_available ml.(heap_start) ml.(heap_pastend) *
       mem_available ml.(stack_start) ml.(stack_pastend))%sep initial.(getMem) /\
      initial.(getPc) = ml.(code_start) /\
      initial.(getNextPc) = word.add initial.(getPc) (word.of_Z 4) /\
      regs_initialized initial.(getRegs) /\
      initial.(getLog) = nil /\
      valid_machine initial.

  Lemma establish_ll_inv: forall (initial: MetricRiscvMachine),
      initial_conditions initial ->
      ll_inv initial.
  Proof.
    unfold initial_conditions.
    intros. simp.
    unfold ll_inv, runsToGood_Invariant.
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
          | context[ptsto_instr ?A1 (IInstruction (Jal RegisterNames.ra ?J1))] =>
            match RR with
            | context[ptsto_instr ?A2 (IInstruction (Jal RegisterNames.ra ?J2))] =>
              unify A1 A2;
              replace J2 with J1
            end
          end
        end.
        2: {
          match goal with
          | |- context[word.unsigned ?x] => ring_simplify x
          end.
          match goal with
          | |- _ = _ + word.unsigned (word.add ?A _) - _ => remember A as a
          end.
          rewrite word.unsigned_add.
          rewrite word.unsigned_of_Z.
          unfold word.wrap.
          rewrite Zplus_mod_idemp_r.
          rewrite Z.mod_small. 1: blia.
          subst a.
          (* holds by transitivity over ml.(code_pastend) *)
          case TODO_sam.
        }
        wcancel.
        cancel_seps_at_indices 3%nat 0%nat. {
          f_equal.
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
          | context[ptsto_instr ?A1 (IInstruction (Jal RegisterNames.ra ?J1))] =>
            match RR with
            | context[ptsto_instr ?A2 (IInstruction (Jal RegisterNames.ra ?J2))] =>
              unify A1 A2;
              replace J2 with J1
            end
          end
        end.
        2: {
          match goal with
          | |- context[word.unsigned ?x] => ring_simplify x
          end.
          match goal with
          | |- _ = _ + word.unsigned (word.add ?A _) - _ => remember A as a
          end.
          rewrite word.unsigned_add.
          rewrite word.unsigned_of_Z.
          unfold word.wrap.
          rewrite Zplus_mod_idemp_r.
          rewrite Z.mod_small. 1: blia.
          subst a.
          (* holds by transitivity over ml.(code_pastend) *)
          case TODO_sam.
        }
        wcancel.
        cancel_seps_at_indices 0%nat 0%nat. {
          f_equal.
          solve_word_eq word_ok.
        }
        cbn [seps].
        reflexivity.
      }
      + destruct mlOk. solve_divisibleBy4.
      + solve_word_eq word_ok.
      + eapply @regs_initialized_put; try typeclasses eauto. (* PARAMRECORDS? *)
        eassumption.
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
        rewrite <- machine_ok_frame_instrs_app_l.
        eapply machine_ok_change_call with (p_call_2 := init_pos)
                                           (f_entry_rel_pos_2 := f_entry_rel_pos).
        1: {
          subst functions_pos loop_pos init_pos; wwcancel.
          cancel_seps_at_indices 2%nat 1%nat. {
            f_equal.
            - solve_word_eq word_ok.
            - f_equal. f_equal.
              repeat match goal with
              | |- context[word.unsigned ?x] => progress ring_simplify x
              end.
              match goal with
              | |- _ = _ + word.unsigned (word.add ?A _) - _ => remember A as a
              end.
              rewrite word.unsigned_add.
              rewrite word.unsigned_of_Z.
              unfold word.wrap.
              rewrite Zplus_mod_idemp_r.
              rewrite Z.mod_small. 1: blia.
              subst a.
              (* holds by transitivity over ml.(code_pastend) *)
              case TODO_sam.
          }
          cbn [seps].
          reflexivity.
        }
        lazymatch goal with
        | H: context[machine_ok] |- ?G => let G' := type of H in replace G with G'; [exact H|clear H]
        end.
        subst functions_pos loop_pos init_pos.
        simple apply (f_equal2); [|
          match goal with
              | |- ?G => assert_fails (has_evar G); reflexivity
              end].
        simple apply (f_equal2). 2: {
          eapply iff1ToEq.
          cancel.
          case TODO_sam. (* something's wrong here! *)
        }
        case TODO_sam.
    Unshelve.
    all: intros; try exact True; try exact 0; try exact mem_ok; try apply @nil; try exact (word.of_Z 0).
  Qed.

  Lemma ll_inv_is_invariant: forall (st: MetricRiscvMachine),
      ll_inv st -> GoFlatToRiscv.mcomp_sat (run1 iset) st ll_inv.
  Proof.
    intros st. unfold ll_inv.
    eapply runsToGood_is_Invariant with (jump := - 4) (pc_start := loop_pos)
                                        (pc_end := word.add loop_pos (word.of_Z 4)).
    - intro D.
      apply (f_equal word.unsigned) in D.
      rewrite word.unsigned_add in D.
      unshelve erewrite @word.unsigned_of_Z in D. 1: exact word_ok. (* PARAMRECORDS? *)
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
      + subst. case TODO_sam. (* show that backjump preserves valid_machine *)
    - unfold ll_good, machine_ok.
      intros. simp. assumption.
    - cbv. intuition discriminate.
    - solve_divisibleBy4.
    - solve_word_eq word_ok.
    - unfold ll_good, machine_ok.
      intros. simp. split.
      + eexists. case TODO_sam.
      + case TODO_sam. (* TODO the jump back Jal has to be in xframe *)
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
      2: {
        (* PARAMRECORDS *)
        symmetry. unshelve eapply SimplWordExpr.add_0_r.
      }
      subst.
      match goal with
      | H: _ |- _ => pose proof H; apply compile_prog_to_compile in H;
                     destruct H as [ before [ finstrs [ ? ? ] ] ]
      end.
      subst.
      eapply runsTo_weaken.
      + pose proof compiler_correct as P. unfold runsTo in P.
        eapply P; clear P. 6: {
          eapply loop_body_correct; eauto.
        }
        all: try eassumption.
        rewrite -> machine_ok_frame_instrs_app_l. Fail exact Hrrrrr. case TODO_sam.
      + cbv beta.
        intros. simp. do 6 eexists.
        ssplit; try eassumption.
        eexists.
        split; [eassumption|].
        split; [eassumption|].
        case TODO_sam. (* similar to machine_ok_frame_instrs_app_l *)
    Unshelve. all: case TODO_sam.
  Qed.

  Lemma ll_inv_implies_prefix_of_good: forall st,
      ll_inv st -> exists suff, spec.(goodTrace) (suff ++ st.(getLog)).
  Proof.
    unfold ll_inv, runsToGood_Invariant. intros. simp.
    eapply extend_runsTo_to_good_trace. 2: case TODO_sam. 2: eassumption.
    simpl. unfold ll_good, compile_inv, related, hl_inv,
           compose_relation, FlattenExprSimulation.related,
           RegRename.related, FlatToRiscvSimulation.related, FlatToRiscvFunctions.goodMachine.
    intros. simp. eassumption.
  Qed.

End Pipeline1.
