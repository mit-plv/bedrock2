Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Strings.String. Local Open Scope string_scope.
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
Require Import coqutil.Semantics.OmniSmallstepCombinators.

Lemma runsTo_is_eventually[State: Type](step: State -> (State -> Prop) -> Prop):
  forall initial P, runsToNonDet.runsTo step initial P <-> eventually step P initial.
Proof. intros. split; induction 1; try (econstructor; solve [eauto]). Qed.

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
  Context (init_f : string).
  Context (loop_f : string).
  Context
    (ml: MemoryLayout)
    (prog : (list (string * (list string * list string * Syntax.cmd)))).
  Let init_sp := word.unsigned ml.(stack_pastend).
  
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

  Definition compile_prog: result (list Instruction * list (string * Z) * Z) :=
    '(functions_insts, positions, required_stack_space) <- compile compile_ext_call prog;;
    'init_fun_pos <- match map.get (map.of_list positions) init_f with
                     | Some p => Success p
                     | None => error:("No function named" init_f "found")
                     end;;
    'loop_fun_pos <- match map.get (map.of_list positions) loop_f with
                     | Some p => Success p
                     | None => error:("No function named" loop_f "found")
                     end;;
    let to_prepend := init_sp_insts ++ init_insts init_fun_pos ++ loop_insts loop_fun_pos ++ backjump_insts in
    let adjust := Z.add (4 * Z.of_nat (length  to_prepend)) in
    let positions := List.map (fun '(name, p) => (name, (adjust p))) positions in
    Success (to_prepend ++ functions_insts, positions, required_stack_space).

  Definition loop_overhead := MetricLogging.mkMetricLog 197 195 197 197.
  Definition run1 st post := (mcomp_sat (run1 iset) st (fun _ => post)).
  Local Notation always := (always run1).
  Local Notation eventually := (eventually run1).
  Local Notation successively := (successively run1).

  Context
    (mlOk: MemoryLayoutOk ml)
    (loop_progress : Semantics.trace -> Semantics.trace -> MetricLog -> Prop)
    (* state invariant which holds at the beginning (and end) of each loop iteration *)
    (bedrock2_invariant : Semantics.trace -> mem -> Prop)
    (funs_valid: valid_src_funs prog = true)
    (init_code: Syntax.cmd.cmd)
    (get_init_code: map.get (map.of_list prog : Semantics.env) init_f = Some (nil, nil, init_code))
    (init_code_correct: forall m0 mc0,
      mem_available (heap_start ml) (heap_pastend ml)m0 ->
      MetricSemantics.exec (map.of_list prog) init_code nil m0 map.empty mc0 (fun t m l mc => bedrock2_invariant t m))
    (loop_body: Syntax.cmd.cmd)
    (get_loop_body: map.get (map.of_list prog : Semantics.env) loop_f = Some (nil, nil, loop_body))
    (loop_body_correct: forall t m mc,
      bedrock2_invariant t m ->
      MetricSemantics.exec (map.of_list prog) loop_body t m map.empty mc (fun t' m l mc' =>
        (* match compiler correctness theorem:*)
        exists retvals : list word, map.getmany_of_list l [] = Some retvals /\
        bedrock2_invariant t' m /\
        forall dmc, metricsLeq dmc (metricsSub (MetricsToRiscv.lowerMetrics (metricsAdd loop_overhead mc')) (MetricsToRiscv.lowerMetrics mc)) ->
        loop_progress t  t' dmc
        (*
        (*actual postcondition*)
        exists dt, t' = dt ++ t /\ loop_trace dt /\
        (metricsLeq (MetricsToRiscv.lowerMetrics (MetricLogging.metricsSub  mc)) (loop_cost dt))%metricsL
         *)
        ))
    (instrs: list Instruction)
    (positions : list (string * Z))
    (required_stack_space: Z)
    (R: mem -> Prop).

  Definition initial_conditions (initial : MetricRiscvMachine) :=
      compile_prog = Success (instrs, positions, required_stack_space) /\
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

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

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

  Local Arguments map.get : simpl never.

  (* Holds each time before executing the loop body *)
  Definition riscv_loop_invariant (mach: MetricRiscvMachine): Prop :=
    exists (functions_instrs: list Instruction) (positions: list (string * Z))
           (init_fun_pos loop_fun_pos: Z),
      compile compile_ext_call prog = Success (functions_instrs, positions, required_stack_space) /\
      required_stack_space <= word.unsigned (word.sub (stack_pastend ml) (stack_start ml)) / bytes_per_word /\
      map.get (map.of_list positions) init_f = Some init_fun_pos /\
      map.get (map.of_list positions) loop_f = Some loop_fun_pos /\
      exists mH,
        bedrock2_invariant mach.(getLog) mH /\
        mach.(getPc) = loop_pos /\
        machine_ok functions_pos ml.(stack_start) ml.(stack_pastend) functions_instrs mH R
                   (program iset init_sp_pos (init_sp_insts ++
                                              init_insts init_fun_pos ++
                                              loop_insts loop_fun_pos ++
                                              backjump_insts))
                   mach.

  Lemma successively_execute_bedrock2_loop : forall initial,
      initial_conditions initial ->
      eventually (successively (fun s s' =>
        loop_progress s.(getLog) s'.(getLog) (metricsSub s'.(getMetrics) s.(getMetrics))
      )) initial.
  Proof.
    intros * IC.
    eapply eventually_trans. { instantiate (1:=riscv_loop_invariant ).
    unfold initial_conditions in *.
    fwd.
    eapply runsTo_is_eventually.
    destruct_RiscvMachine initial.
    match goal with
    | H: compile_prog = Success _ |- _ =>
        pose proof H as CP; unfold compile_prog, compile in H
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
    | H: map.get ?positions init_f = Some ?pos |- _ =>
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
      { match goal with
        | H: composed_compile _ _ = Success _ |- _ => rename H into CE
        end.
        unfold composed_compile, compose_phases, riscvPhase in CE. fwd.
        rewrite map.of_list_tuples in GetPos.
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
                        (post := fun t' m' retvals mc' => bedrock2_invariant t' m')
                        (fname := init_f).
      match goal with |- runsToNonDet.runsTo run1 (mkMetricRiscvMachine _ ?mc_now) _  =>
        specialize P with (mc:=MetricsToRiscv.raiseMetrics mc_now) end.
      edestruct P as (init_rel_pos & G & P'); clear P; cycle -1.
      1: eapply P' with (p_funcs := word.add loop_pos (word.of_Z 8)) (Rdata := R).
      all: simpl_MetricRiscvMachine_get_set.
      12: {
        move init_code_correct at bottom.
        do 4 eexists. split. 1: eassumption. split. 1: reflexivity.
        eapply ExprImp.weaken_exec.
        - refine (init_code_correct _ _ _).
          exact HMem.
        - cbv beta. intros * HP. exists []. split. 1: reflexivity. trivial.
      }
      11: { unfold compile. rewrite_match. reflexivity. }
      all: try eassumption.
      { apply stack_length_divisible. }
      { cbn. clear CP.
        rewrite GetPos in G. fwd.
        subst loop_pos init_pos init_sp. solve_word_eq word_ok. }
      { cbn. apply map.get_put_same. }
      { destruct mlOk. solve_divisibleBy4. }
      { reflexivity. }
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
      + match goal with
        | H: composed_compile _ _ = Success _ |- _ => rename H into CE
        end.
        unfold composed_compile, compose_phases, riscvPhase in CE. fwd.
        rewrite map.of_list_tuples in GetPos.
        eapply fun_pos_div4 in GetPos.
        destruct mlOk. solve_divisibleBy4.
      + do 2 rapply regs_initialized_put. eassumption.
      + rewrite map.get_put_diff by (cbv; discriminate).
        rewrite map.get_put_same. unfold init_sp. rewrite word.of_Z_unsigned. reflexivity.
    - cbv beta. unfold riscv_loop_invariant . intros. fwd.
      match goal with
      | _: map.get ?positions loop_f = Some ?z |- _ => rename z into f_loop_rel_pos
      end.
      unfold compile_prog, compile in CP. fwd.
      repeat match goal with
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             | |- _ => progress cbv beta iota
             | |- _ => eassumption
             | |- _ => reflexivity
             end.
      + unfold compile. rewrite_match. reflexivity.
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
  } {
    clear dependent initial.
    intros initial; intros.
    eapply eventually_done, mk_successively with (invariant:=riscv_loop_invariant); trivial.
    clear dependent initial.
    intros initial; intros.
    eapply runsTo_is_eventually.
    - intros. destruct_RiscvMachine initial. unfold riscv_loop_invariant, machine_ok in H. cbn in *. fwd.
      (* call loop function (execute the Jal that jumps there) *)
      eapply runsToStep.
       {
        eapply RunInstruction.run_Jal; cbn.
        3: reflexivity.
        3: eassumption.
        3: { subst loop_pos init_pos init_sp_pos init_sp_insts. wwcancel. }
        { unfold compile, composed_compile, compose_phases, riscvPhase in *. fwd.
          match goal with
          | H: map.get _ loop_f = Some _ |- _ => rename H into GetPos
          end.
          rewrite map.of_list_tuples in GetPos.
          eapply fun_pos_div4 in GetPos. solve_divisibleBy4. }
        { cbv. auto. }
        { subst loop_pos init_pos init_sp_pos init_sp_insts.
          wcancel_assumption. }
        { assumption. }
      }
      cbn.
      intros mid; intros. destruct_RiscvMachine mid. fwd.
      (* use compiler correctness for loop body *)
      unfold riscv_loop_invariant in *. fwd.
      subst.
      eapply runsTo_trans_cps. {
      eapply runsTo_weaken.
      + pose proof compiler_correct compile_ext_call compile_ext_call_correct
                                    compile_ext_call_length_ignores_positions as P.
        specialize P with (fname := loop_f) (argvals := []) .
        match goal with |- runsToNonDet.runsTo run1 (mkMetricRiscvMachine _ ?mc_now) _  =>
          specialize P with (mc:=MetricsToRiscv.raiseMetrics mc_now) end.

        edestruct P as (loop_rel_pos & G & P'); clear P; cycle -2.
        2: eapply P' with (p_funcs := word.add loop_pos (word.of_Z 8)) (Rdata := R)
                          (ret_addr := word.add loop_pos (word.of_Z 4)); cycle 1.
        all: try eassumption.
        all: simpl_MetricRiscvMachine_get_set.
        { do 4 eexists. split. 1: eassumption. split. 1: reflexivity. eapply loop_body_correct. eauto. }
        { apply stack_length_divisible. }
        { replace loop_rel_pos with loop_fun_pos by congruence.
          solve_word_eq word_ok. }
        { cbn. rewrite map.get_put_same. trivial. }
        { subst loop_pos init_pos. destruct mlOk. solve_divisibleBy4. }
        { reflexivity. }
        { reflexivity. }
        { reflexivity. }
        unfold machine_ok.
        unfold_RiscvMachine_get_set.
        repeat match goal with
               | |- exists _, _  => eexists
               | |- _ /\ _ => split
               | |- _ => progress cbv beta iota
               | |- _ => eassumption
               | |- _ => reflexivity
               end.
        * repeat match goal with x := _ |- _ => subst x end.
          wcancel_assumption.
        * repeat match goal with x := _ |- _ => subst x end.
          eapply rearrange_footpr_subset. 1: eassumption.
          wwcancel.
        * repeat match goal with x := _ |- _ => subst x end.
          match goal with
          | H: map.get _ loop_f = Some _ |- _ => rename H into GetPos
          end.
          unfold compile, composed_compile, compose_phases, riscvPhase in *. fwd.
          repeat match goal with
                 | H: _ |- _ => rewrite map.of_list_tuples in H; move H at bottom
                 end.
          apply_in_hyps (fun_pos_div4 (iset := iset)).
          progress remember (
               (word.add
                  (word.add (code_start ml)
                     (word.of_Z
                        (4 *
                         Z.of_nat
                           (Datatypes.length
                              (FlatToRiscvDef.compile_lit iset RegisterNames.sp
                                 (word.unsigned (stack_pastend ml)))))))
                  (word.of_Z 4))) as X.
          solve_divisibleBy4.
        * eapply regs_initialized_put. eassumption.
        * rewrite map.get_put_diff by (cbv; discriminate). assumption.
      + cbv beta.
        intros.
        destruct_RiscvMachine final.
        unfold machine_ok in *.
        simpl_MetricRiscvMachine_get_set.
        fwd.
        simpl_MetricRiscvMachine_get_set.
        eapply runsToStep. {
          eapply RunInstruction.run_Jal0 with (jimm20:=-4); simpl_MetricRiscvMachine_get_set; trivial; try reflexivity.

          { eapply rearrange_footpr_subset. 1: eassumption.
            subst loop_pos init_sp_pos init_sp_insts init_pos backjump_pos backjump_insts.
            set (Datatypes.length _).
            wwcancel. }
          { subst loop_pos init_sp_pos init_sp_insts init_pos backjump_pos backjump_insts.
            use_sep_assumption.
            set (Datatypes.length _).
            wwcancel. } }

      simpl. intros. Simp.simp.
      destruct_RiscvMachine mid.
      subst.
      apply runsToDone.
      ssplit; try assumption; cbn;
      repeat match goal with
             |- context [ {| getPc := ?pc |} ] => progress ring_simplify pc
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             | |- _ => progress cbv beta iota
             | |- _ => eassumption
             | |- _ => reflexivity
             end; cycle 1.
      { subst loop_pos init_sp_pos init_sp_insts init_pos backjump_pos backjump_insts functions_pos.
        wcancel_assumption. }
      { subst loop_pos init_sp_pos init_sp_insts init_pos backjump_pos backjump_insts functions_pos.
        eapply rearrange_footpr_subset. 1: eassumption.
        wwcancel. }
      { match goal with
        | H: valid_machine ?m1 |- valid_machine ?m2 => replace m2 with m1; [exact H|]
        end.
        f_equal. f_equal; solve_word_eq word_ok. }
      { eapply Hp5p2.
        repeat match goal with H : MetricLogging.metricsLeq _ _ |- _ => revert H end.
        repeat match goal with H :               metricsLeq _ _ |- _ => revert H end.
        pose I; intros.
        repeat (
          cbv [MetricsToRiscv.raiseMetrics MetricsToRiscv.lowerMetrics] in *;
          cbv [Spilling.cost_spill_spec cost_compile_spec loop_overhead ] in *;
           MetricLogging.unfold_MetricLog;  MetricLogging.simpl_MetricLog;
                         unfold_MetricLog;                simpl_MetricLog);
          intuition try blia.
        }
      }
    }
  Qed.
End Pipeline1.
