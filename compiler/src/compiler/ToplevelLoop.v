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
Require Import coqutil.Tactics.fwd.
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
Require Import compiler.Pipeline.
Require Import compiler.LowerPipeline.
Require Import compiler.ExprImpEventLoopSpec.

Global Existing Instance riscv.Spec.Machine.DefaultRiscvState.

Local Hint Mode word.word - : typeclass_instances.

Local Arguments Z.mul: simpl never.
Local Arguments Z.add: simpl never.
Local Arguments Z.of_nat: simpl never.
Local Arguments Z.modulo : simpl never.
Local Arguments Z.pow: simpl never.
Local Arguments Z.sub: simpl never.

Open Scope Z_scope.

Local Open Scope ilist_scope.

Section Pipeline1.
  Context {width: Z}.
  Context {BW: Bitwidth width}.
  Context {word: word.word width}.
  Context {word_ok: word.ok word}.
  Context {mem: map.map word byte}.
  Context {Registers: map.map Z word}.
  Context {string_keyed_map: forall T: Type, map.map string T}. (* abstract T for better reusability *)
  Context {ext_spec: Semantics.ExtSpec}.
  Context {M: Type -> Type}.
  Context {MM: Monad M}.
  Context {RVM: RiscvProgram M word}.
  Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
  Context {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}.
  Context {string_keyed_map_ok: forall T, map.ok (string_keyed_map T)}.
  Context {Registers_ok: map.ok Registers}.
  Context {PR: MetricPrimitives PRParams}.
  Context {iset: InstructionSet}.
  Context {BWM: bitwidth_iset width iset}.
  Context {mem_ok: map.ok mem}.
  Context {ext_spec_ok: Semantics.ext_spec.ok ext_spec}.
  Context (compile_ext_call : string_keyed_map Z -> Z -> Z -> FlatImp.stmt Z -> list Instruction).
  Context (compile_ext_call_correct: forall resvars extcall argvars,
              compiles_FlatToRiscv_correctly compile_ext_call compile_ext_call
                                             (FlatImp.SInteract resvars extcall argvars)).
  Context (compile_ext_call_length_ignores_positions: forall stackoffset posmap1 posmap2 c pos1 pos2,
              List.length (compile_ext_call posmap1 pos1 stackoffset c) =
              List.length (compile_ext_call posmap2 pos2 stackoffset c)).
  Context (ml: MemoryLayout)
          (mlOk: MemoryLayoutOk ml).

  Let init_sp := word.unsigned ml.(stack_pastend).

  Local Notation source_env := (string_keyed_map (list string * list string * Syntax.cmd)).

  (* All riscv machine code, layed out from low to high addresses: *)
  (* 1) Initialize stack pointer *)
  Let init_sp_insts := FlatToRiscvDef.compile_lit iset RegisterNames.sp init_sp.
  Let init_sp_pos := ml.(code_start).
  (* 2) Call init function *)
  Let init_insts init_fun_pos := [[Jal RegisterNames.ra (3 * 4 + init_fun_pos)]].
  Let init_pos := word.add ml.(code_start)
         (word.of_Z (4 * (Z.of_nat (List.length (FlatToRiscvDef.compile_lit iset RegisterNames.sp init_sp))))).
  (* 3) Call loop function *)
  Let loop_insts loop_fun_pos := [[Jal RegisterNames.ra (2 * 4 + loop_fun_pos)]].
  Let loop_pos := word.add init_pos (word.of_Z 4).
  (* 4) Jump back to 3) *)
  Let backjump_insts := [[Jal Register0 (-4)]].
  Let backjump_pos := word.add loop_pos (word.of_Z 4).
  (* 5) Code of the compiled functions *)
  Let functions_pos := word.add backjump_pos (word.of_Z 4).

  Definition compile_prog(prog: source_env): result (list Instruction * string_keyed_map Z * Z) :=
    '(functions_insts, positions, required_stack_space) <- compile compile_ext_call prog;;
    'init_fun_pos <- match map.get positions "init" with
                     | Some p => Success p
                     | None => error:("No function named" "init" "found")
                     end;;
    'loop_fun_pos <- match map.get positions "loop" with
                     | Some p => Success p
                     | None => error:("No function named" "loop" "found")
                     end;;
    let to_prepend := init_sp_insts ++ init_insts init_fun_pos ++ loop_insts loop_fun_pos ++ backjump_insts in
    Success (to_prepend ++ functions_insts, positions, required_stack_space).

  Context (spec: ProgramSpec).

  (* Holds each time before executing the loop body *)
  Definition ll_good(done: bool)(mach: MetricRiscvMachine): Prop :=
    exists (prog: source_env)
           (functions_instrs: list Instruction) (positions: string_keyed_map Z)
           (required_stack_space: Z)
           (init_fun_pos loop_fun_pos: Z) (R: mem -> Prop),
      compile compile_ext_call prog = Success (functions_instrs, positions, required_stack_space) /\
      required_stack_space <= word.unsigned (word.sub (stack_pastend ml) (stack_start ml)) / bytes_per_word /\
      ProgramSatisfiesSpec "init"%string "loop"%string prog spec /\
      map.get positions "init"%string = Some init_fun_pos /\
      map.get positions "loop"%string = Some loop_fun_pos /\
      exists mH,
        isReady spec mach.(getLog) mH /\ goodTrace spec mach.(getLog) /\
        mach.(getPc) = word.add loop_pos (word.of_Z (if done then 4 else 0)) /\
        machine_ok functions_pos ml.(stack_start) ml.(stack_pastend) functions_instrs mH R
                   (program iset init_sp_pos (init_sp_insts ++
                                              init_insts init_fun_pos ++
                                              loop_insts loop_fun_pos ++
                                              backjump_insts))
                   mach.

  Definition ll_inv: MetricRiscvMachine -> Prop := runsToGood_Invariant ll_good iset.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Definition initial_conditions(initial: MetricRiscvMachine): Prop :=
    exists (srcprog: source_env)
           (instrs: list Instruction) positions (required_stack_space: Z) (R: mem -> Prop),
      ProgramSatisfiesSpec "init"%string "loop"%string srcprog spec /\
      spec.(datamem_start) = ml.(heap_start) /\
      spec.(datamem_pastend) = ml.(heap_pastend) /\
      compile_prog srcprog = Success (instrs, positions, required_stack_space) /\
      required_stack_space <= word.unsigned (word.sub (stack_pastend ml) (stack_start ml)) / bytes_per_word /\
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
    clear -word_ok BW.
    simpl.
    intros.
    eapply word.signed_of_Z_nowrap.
    case width_cases as [E | E]; rewrite E; Lia.lia.
  Qed.

  Lemma mod_2width_mod_bytes_per_word: forall x,
      (x mod 2 ^ width) mod bytes_per_word = x mod bytes_per_word.
  Proof.
    intros.
    rewrite <- Znumtheory.Zmod_div_mod.
    - reflexivity.
    - unfold bytes_per_word. destruct width_cases as [E | E]; rewrite E; reflexivity.
    - destruct width_cases as [E | E]; simpl in *; rewrite E; reflexivity.
    - unfold Z.divide.
      exists (2 ^ width / bytes_per_word).
      unfold bytes_per_word, Memory.bytes_per_word.
      destruct width_cases as [E | E]; simpl; rewrite E; reflexivity.
  Qed.

  Lemma stack_length_divisible:
    word.unsigned (word.sub (stack_pastend ml) (stack_start ml)) mod bytes_per_word = 0.
  Proof.
    intros.
    destruct mlOk.
    rewrite word.unsigned_sub. unfold word.wrap.
    rewrite mod_2width_mod_bytes_per_word.
    rewrite Zminus_mod.
    rewrite stack_start_aligned.
    rewrite stack_pastend_aligned.
    rewrite Z.sub_diag.
    apply Zmod_0_l.
  Qed.

  Lemma establish_ll_inv: forall (initial: MetricRiscvMachine),
      initial_conditions initial ->
      ll_inv initial.
  Proof.
    unfold initial_conditions.
    intros. fwd.
    unfold ll_inv, runsToGood_Invariant. split; [|assumption].
    destruct_RiscvMachine initial.
    match goal with
    | H: context[ProgramSatisfiesSpec] |- _ => rename H into sat
    end.
    pose proof sat.
    destruct sat.
    match goal with
    | H: compile_prog srcprog = Success _ |- _ => pose proof H as CP; unfold compile_prog in H
    end.
    remember instrs as instrs0.
    Simp.simp.
    eassert ((mem_available ml.(heap_start) ml.(heap_pastend) * _)%sep initial_mem) as SplitImem. {
      ecancel_assumption.
    }
    destruct SplitImem as [heap_mem [other_mem [SplitHmem [HMem OtherMem] ] ] ].
    evar (after_init_sp: MetricRiscvMachine).
    eapply runsTo_trans with (P := fun mach => valid_machine mach /\ mach = after_init_sp);
      subst after_init_sp.
    {
      RunInstruction.get_runsTo_valid_for_free.
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
    match goal with
    | H: map.get positions "init"%string = Some ?pos |- _ =>
      rename H into GetPos, pos into f_entry_rel_pos
    end.
    subst.
    intros. fwd.
    (* then, call init function (execute the Jal that jumps there) *)
    eapply runsToStep. {
      eapply RunInstruction.run_Jal; cbn.
      3: solve_word_eq word_ok.
      3: eassumption.
      3: wwcancel.
      { unfold compile, compose_phases, riscvPhase in E. fwd.
        eapply fun_pos_div4 in GetPos. solve_divisibleBy4. }
      { cbv. auto. }
      { wcancel_assumption. }
      { assumption. }
    }
    cbn.
    repeat match goal with
           | H: valid_machine _ |- _ => clear H
           end.
    intros. destruct_RiscvMachine mid. fwd.
    (* then, run body of init function (using compiler simulation and correctness of init) *)
    eapply runsTo_weaken.
    - pose proof compiler_correct compile_ext_call compile_ext_call_correct
                                  compile_ext_call_length_ignores_positions as P.
      unfold runsTo in P.
      specialize P with (argvals := [])
                        (post := fun t' m' retvals => isReady spec t' m' /\ goodTrace spec t')
                        (fname := "init"%string).
      edestruct P as (init_rel_pos & G & P'); clear P; cycle -1.
      1: eapply P' with (p_funcs := word.add loop_pos (word.of_Z 8)) (Rdata := R).
      all: simpl_MetricRiscvMachine_get_set.
      11: {
        unfold hl_inv in init_code_correct.
        move init_code_correct at bottom.
        do 4 eexists. split. 1: eassumption. split. 1: reflexivity.
        intros mc.
        eapply ExprImp.weaken_exec.
        - refine (init_code_correct _ _ _).
          replace (datamem_start spec) with (heap_start ml) by congruence.
          replace (datamem_pastend spec) with (heap_pastend ml) by congruence.
          exact HMem.
        - cbv beta. intros * _ HP. exists []. split. 1: reflexivity. exact HP.
      }
      all: try eassumption.
      { apply stack_length_divisible. }
      { cbn. clear CP.
        rewrite GetPos in G. fwd.
        subst loop_pos init_pos init_sp. solve_word_eq word_ok. }
      { cbn. apply map.get_put_same. }
      { destruct mlOk. solve_divisibleBy4. }
      { reflexivity. }
      { reflexivity. }
      unfold machine_ok.
      clear P'.
      rewrite GetPos in G. fwd.
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
        wcancel.
        cancel_seps_at_indices 4%nat 0%nat. {
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
      + unfold compile, compose_phases, riscvPhase in E. fwd.
        eapply fun_pos_div4 in GetPos.
        destruct mlOk. solve_divisibleBy4.
      + do 2 rapply regs_initialized_put. eassumption.
      + rewrite map.get_put_diff by (cbv; discriminate).
        rewrite map.get_put_same. unfold init_sp. rewrite word.of_Z_unsigned. reflexivity.
    - cbv beta. unfold ll_good. intros. fwd.
      match goal with
      | _: map.get positions "loop"%string = Some ?z |- _ => rename z into f_loop_rel_pos
      end.
      unfold compile_prog in CP. fwd.
      repeat match goal with
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             | |- _ => progress cbv beta iota
             | |- _ => eassumption
             | |- _ => reflexivity
             end.
      + destruct_RiscvMachine final. subst.
        subst loop_pos init_pos.
        solve_word_eq word_ok.
      + (* prove that machine_ok of ll_inv (i.e. all instructions, and just before jumping calling
           loop body function) is implied by the state proven by the compiler correctness lemma for
           the init function *)
        lazymatch goal with
        | H: context[machine_ok] |- ?G =>
          let G' := type of H in replace G with G'; [exact H|clear H]
        end.
        f_equal.
        * unfold functions_pos, backjump_pos. solve_word_eq word_ok.
        * eapply iff1ToEq.
          unfold init_sp_insts, init_insts, loop_insts, backjump_insts.
          wwcancel.
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
      fwd.
      etransitivity. 1: eassumption.
      destruct done; solve_word_eq word_ok.
    - (* Show that ll_ready (almost) ignores pc, nextPc, and metrics *)
      intros.
      unfold ll_good, machine_ok in *.
      fwd.
      destr_RiscvMachine state.
      repeat match goal with
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             | |- _ => progress cbv beta iota
             | |- _ => eassumption
             | |- _ => reflexivity
             end.
      + cbn. solve_word_eq word_ok.
      + cbn. destruct mlOk. subst. simpl in *. subst loop_pos init_pos. solve_divisibleBy4.
    - unfold ll_good, machine_ok.
      intros. fwd. assumption.
    - cbv. intuition discriminate.
    - solve_word_eq word_ok.
    - unfold ll_good, machine_ok.
      intros. fwd. split.
      + eexists. subst loop_pos init_sp_pos init_sp_insts init_pos backjump_pos backjump_insts.
        wcancel_assumption.
      + eapply shrink_footpr_subset. 1: eassumption.
        subst loop_pos init_sp_pos init_sp_insts init_pos backjump_pos backjump_insts.
        wwcancel.
    - intros. destruct_RiscvMachine initial. unfold ll_good, machine_ok in H. cbn in *. fwd.
      (* call loop function (execute the Jal that jumps there) *)
      eapply runsToStep. {
        eapply RunInstruction.run_Jal; cbn.
        3: reflexivity.
        3: eassumption.
        3: { subst loop_pos init_pos init_sp_pos init_sp_insts. wwcancel. }
        { unfold compile, compose_phases, riscvPhase in *. fwd.
          match goal with
          | H: map.get _ "loop"%string = Some _ |- _ => rename H into GetPos
          end.
          eapply fun_pos_div4 in GetPos. solve_divisibleBy4. }
        { cbv. auto. }
        { subst loop_pos init_pos init_sp_pos init_sp_insts.
          wcancel_assumption. }
        { assumption. }
      }
      cbn.
      intros. destruct_RiscvMachine mid. fwd.
      (* use compiler correctness for loop body *)
      unfold ll_good in *. fwd.
      match goal with
      | H: ProgramSatisfiesSpec _ _ _ _ |- _ => pose proof H as sat; destruct H
      end.
      unfold hl_inv in loop_body_correct.
      specialize loop_body_correct with (l := map.empty).
      lazymatch goal with
      | H: context[@word.add ?w ?wo ?x (word.of_Z 0)] |- _ =>
        replace (@word.add w wo x (word.of_Z 0)) with x in H
      end.
      2: solve_word_eq word_ok.
      subst.
      eapply runsTo_weaken.
      + pose proof compiler_correct compile_ext_call compile_ext_call_correct
                                    compile_ext_call_length_ignores_positions as P.
        unfold runsTo in P.
        specialize P with (argvals := [])
                          (fname := "loop"%string)
                          (post := fun t' m' retvals => isReady spec t' m' /\ goodTrace spec t').
        edestruct P as (loop_rel_pos & G & P'); clear P; cycle -1.
        1: eapply P' with (p_funcs := word.add loop_pos (word.of_Z 8)) (Rdata := R)
                          (ret_addr := word.add loop_pos (word.of_Z 4)).
        11: {
          move loop_body_correct at bottom.
          do 4 eexists. split. 1: eassumption. split. 1: reflexivity.
          intros mc.
          eapply ExprImp.weaken_exec.
          - eapply loop_body_correct; eauto.
          - cbv beta. intros * _ HP. exists []. split. 1: reflexivity. exact HP.
        }
        all: try eassumption.
        all: simpl_MetricRiscvMachine_get_set.
        { apply stack_length_divisible. }
        { replace loop_rel_pos with loop_fun_pos by congruence.
          solve_word_eq word_ok. }
        { cbn. rewrite map.get_put_same. f_equal. solve_word_eq word_ok. }
        { subst loop_pos init_pos. destruct mlOk. solve_divisibleBy4. }
        { reflexivity. }
        { reflexivity. }
        unfold loop_pos, init_pos.
        unfold machine_ok.
        unfold_RiscvMachine_get_set.
        repeat match goal with
               | x := _ |- _ => subst x
               end.
        repeat match goal with
               | |- exists _, _  => eexists
               | |- _ /\ _ => split
               | |- _ => progress cbv beta iota
               | |- _ => eassumption
               | |- _ => reflexivity
               end.
        * wcancel_assumption.
        * eapply rearrange_footpr_subset. 1: eassumption.
          wwcancel.
        * match goal with
          | H: map.get positions "loop"%string = Some _ |- _ => rename H into GetPos
          end.
          unfold compile, compose_phases, riscvPhase in *. fwd.
          apply_in_hyps (fun_pos_div4 (iset := iset)).
          remember (word.add
               (word.add
                  (word.add (code_start ml)
                     (word.of_Z
                        (4 *
                         Z.of_nat
                           (Datatypes.length
                              (FlatToRiscvDef.compile_lit iset RegisterNames.sp
                                 (word.unsigned (stack_pastend ml)))))))
                  (word.of_Z 4)) (word.of_Z 0)) as X.
          solve_divisibleBy4.
        * eapply regs_initialized_put. eassumption.
        * rewrite map.get_put_diff by (cbv; discriminate). assumption.
        * match goal with
          | H: valid_machine {| getMetrics := ?M |} |- valid_machine {| getMetrics := ?M |} =>
            eqexact.eqexact H; f_equal; f_equal
          end.
          { f_equal. solve_word_eq word_ok. }
          { solve_word_eq word_ok. }
          { solve_word_eq word_ok. }
      + cbv beta.
        intros.
        destruct_RiscvMachine final.
        repeat match goal with
               | x := _ |- _ => subst x
               end.
        unfold machine_ok in *. simpl_MetricRiscvMachine_get_set. fwd.
        simpl_MetricRiscvMachine_get_set.
        repeat match goal with
               | |- exists _, _  => eexists
               | |- _ /\ _ => split
               | |- _ => progress cbv beta iota
               | |- _ => eassumption
               | |- _ => reflexivity
               end.
        * wcancel_assumption.
        * eapply rearrange_footpr_subset. 1: eassumption.
          wwcancel.
  Qed.

  Lemma ll_inv_implies_prefix_of_good: forall st,
      ll_inv st -> exists suff, spec.(goodTrace) (suff ++ st.(getLog)).
  Proof.
    unfold ll_inv, runsToGood_Invariant. intros. fwd.
    eapply extend_runsTo_to_good_trace. 2,3: eassumption.
    simpl. unfold ll_good, hl_inv, FlatToRiscvCommon.goodMachine.
    intros. fwd. eassumption.
  Qed.

End Pipeline1.
