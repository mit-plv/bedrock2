Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Export coqutil.Decidable.
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

Section Pipeline1.

  Context {p: Pipeline.parameters}.
  Context {h: Pipeline.assumptions}.

  Context (ml: MemoryLayout Semantics.width)
          (mlOk: MemoryLayoutOk ml).

  Let init_sp := word.unsigned ml.(stack_pastend).

(*
  Lemma get_flatten_functions: forall fname argvars resvars body flattened,
      map.get srcprog.(funimpls) fname = Some (argvars, resvars, body) ->
      flatten_functions (2^10) (funimpls srcprog) = Some flattened ->
      exists body', map.get flattened fname = Some (argvars, resvars, body') /\
                    flatten_function (2^10) (argvars, resvars, body) = Some (argvars, resvars, body').
  Proof.
    unfold flatten_functions.
    destruct srcprog. destruct sat as [_ _ M0 _ _]. cbn -[flatten_function] in *. clear sat.
    intros.
    pose proof (map.map_all_values_fw _ _ _ _ H0 _ _ H) as P.
    unfold flatten_function in *.
    simp. eauto.
  Qed.

  Definition putProgram(prog: ExprImpProgram)(preInitial: MetricRiscvMachine):
    option MetricRiscvMachine :=
    bind_opt insts <- (compile ml prog);
    Some (MetricRiscvMachine.putProgram (List.map encode insts) ml.(code_start) preInitial).

  Definition related(g: GhostConsts)(relative_code_pos: Z) :=
    (compose_relation (FlattenExprSimulation.related (2^10))
    (compose_relation (RegRename.related eqb Z.eqb eqb eqb available_registers ext_spec)
                      (FlatToRiscvSimulation.related g relative_code_pos))).

  Section Riscv.
    Context (prog: RenamedProgram).

    (* pc at beginning of loop *)
    Definition pc_start: word :=
      word.add ml.(code_start)
               (word.of_Z (4 * Z.of_nat (List.length (FlatToRiscvDef.init_sp_insts init_sp) +
                                         List.length (FlatToRiscvDef.init_insts prog)))).

    Definition TODO_frame: mem -> Prop. case TODO_sam. Qed.
    (* don't unfold and count many times *)

    Definition program_base :=
      word.add ml.(code_start)
               (word.of_Z (4 * Z.of_nat (List.length (FlatToRiscvDef.init_sp_insts init_sp) +
                                         List.length (FlatToRiscvDef.init_insts prog) +
                                         List.length (FlatToRiscvDef.loop_insts prog) +
                                         List.length (FlatToRiscvDef.backjump_insts prog)))).

    Definition initCodeGhostConsts: GhostConsts := Build_GhostConsts
      ml.(stack_pastend)
      num_stackwords
      (word.add ml.(code_start)
                (word.of_Z (4 * Z.of_nat (List.length (FlatToRiscvDef.init_sp_insts init_sp)))))
      (FlatToRiscvDef.init_insts prog)
      program_base
      (FlatToRiscvDef.function_positions prog)
      prog.(funimpls)
      prog.(funnames)
      TODO_frame
      TODO_frame.

    Definition loopBodyGhostConsts: GhostConsts := Build_GhostConsts
      ml.(stack_pastend)
      num_stackwords
      pc_start
      (FlatToRiscvDef.loop_insts prog)
      program_base
      (FlatToRiscvDef.function_positions prog)
      prog.(funimpls)
      prog.(funnames)
      TODO_frame
      TODO_frame.

    Lemma main_size_correct:
      FlatToRiscvDef.main_size prog = (Datatypes.length (FlatToRiscvDef.init_insts prog) +
                                       Datatypes.length (FlatToRiscvDef.loop_insts prog) + 1)%nat.
    Proof.
      unfold FlatToRiscvDef.main_size, FlatToRiscvDef.init_insts, FlatToRiscvDef.loop_insts,
             FlatToRiscvDef.compile_main.
      rewrite !app_length. simpl.
      repeat lazymatch goal with
             | |- ?L = ?R =>
               match L with
               | context[?LL] =>
                 lazymatch LL with
                 | Datatypes.length (FlatToRiscvDef.compile_stmt _ ?pos1 ?C) =>
                   match R with
                   | context[?RR] =>
                     lazymatch RR with
                     | Datatypes.length (FlatToRiscvDef.compile_stmt _ ?pos2 C) =>
                       progress replace LL with RR by
                           refine (compile_stmt_length_position_indep _ _ _ _ _)
                     end
                   end
                 end
               end
             end.
      blia.
    Qed.

  End Riscv.
*)

  Local Notation source_env :=
    (@funname_env _ (list string * list string * (@Syntax.cmd (FlattenExpr.mk_Syntax_params _)))).

  (* All riscv machine code, layed out from low to high addresses:
     - init_sp_insts: initializes stack pointer
     - init_insts: calls init function
     - loop_insts: calls loop function
     - backjump_insts: jumps back to calling loop function
     - fun_insts: code of compiled functions *)
  Definition compile_prog(prog: source_env): option (list Instruction) :=
    'Some (fun_insts, positions) <- @compile p ml prog;
    let init_sp_insts := FlatToRiscvDef.compile_lit RegisterNames.sp init_sp in
    'Some init_pos <- map.get positions "init"%string;
    'Some loop_pos <- map.get positions "loop"%string;
    let init_insts := [[Jal RegisterNames.ra (3 * 4 + init_pos)]] in
    let loop_insts := [[Jal RegisterNames.ra (2 * 4 + loop_pos)]] in
    let backjump_insts := [[Jal Register0 (-4*Z.of_nat (List.length loop_insts))]] in
    Some (init_sp_insts ++ init_insts ++ loop_insts ++ backjump_insts ++ fun_insts).

  related ml

  Definition ll_good(sprog: ExprImpProgram)(rprog: RenamedProgram)(done: bool):
    MetricRiscvMachine -> Prop :=
    compile_inv (related (loopBodyGhostConsts rprog) (FlatToRiscvDef.loop_pos rprog) done)
                (@hl_inv (FlattenExpr.mk_Semantics_params _) _ sprog.(funimpls) sprog.(loop_body) spec).

  (* all "related" relations are parametrized (we don't hide parames behind existentials),
     but at the very end, we have ll_inv, where we do use existentials, because the "API"
     for ll_inv is just establish/preserve/use *)
  Definition ll_inv(m: MetricRiscvMachine): Prop :=
    exists source_prog renamed_prog,
      (* technical detail: "pc at beginning of loop" and "pc at end of loop" needs to be
         different so that we can have two disjoint states between which the system goes
         back and forth. If we had only one state, we could not prevent "runsTo" from
         always being runsToDone and not making progress, see compiler.ForeverSafe *)
      0 < 4 * Z.of_nat (List.length (FlatToRiscvDef.loop_insts renamed_prog)) < 2 ^ width /\
      runsToGood_Invariant (ll_good source_prog renamed_prog) m.

  Lemma sim(renamed_prog: RenamedProgram)(g: GhostConsts)
        (relative_code_pos: Z):
    FlatToRiscvFunctions.funnames g = funnames srcprog ->
    FlatToRiscvFunctions.program_base g = program_base renamed_prog ->
    simulation ExprImp.SimExec runsTo (related g relative_code_pos).
  Proof.
    intros E1 E2.
    refine (compose_sim (FlattenExprSimulation.flattenExprSim (2^10))
           (compose_sim _
                        (FlatToRiscvSimulation.flatToRiscvSim g relative_code_pos _ _))).
    1: eapply renameSim; try typeclasses eauto.
    - repeat constructor; simpl; blia.
    - rewrite E1.
      eapply (funnames_NoDup sat).
    - simpl. destruct mlOk. rewrite E2. unfold program_base. solve_divisibleBy4.
  Qed.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Definition layout: mem -> Prop :=
    (mem_available  ml.(code_start)  ml.(code_pastend) *
     mem_available  ml.(heap_start)  ml.(heap_pastend) *
     mem_available ml.(stack_start) ml.(stack_pastend))%sep.

  Lemma rename_fun_valid: forall argnames retnames body impl',
      rename_fun available_registers (argnames, retnames, body) = Some impl' ->
      NoDup argnames ->
      NoDup retnames ->
      FlatImp.stmt_size body < 2 ^ 10 ->
      FlatToRiscvDef.valid_FlatImp_fun impl'.
  Proof.
    unfold rename_fun, FlatToRiscvDef.valid_FlatImp_fun.
    intros.
    simp.
    eapply rename_binds_props in E; cycle 1.
    { exact String.eqb_spec. }
    { typeclasses eauto. }
    { eapply map.empty_injective. }
    { eapply map.not_in_range_empty. }
    { apply NoDup_available_registers. }
    simp.
    eapply rename_binds_props in E0; cycle 1.
    { exact String.eqb_spec. }
    { typeclasses eauto. }
    { assumption. }
    { assumption. }
    { pose proof NoDup_available_registers as P.
      replace available_registers with (used ++ l) in P by assumption.
      apply invert_NoDup_app in P. tauto. }
    simp.
    pose proof E1 as E1'.
    eapply rename_props in E1; cycle 1.
    { exact String.eqb_spec. }
    { typeclasses eauto. }
    { assumption. }
    { assumption. }
    { pose proof NoDup_available_registers as P.
      replace available_registers with (used ++ used0 ++ l1) in P by assumption.
      apply invert_NoDup_app in P. simp. apply invert_NoDup_app in Prl. simp. assumption. }
    simp.
    ssplit.
    - eapply Forall_impl. 2: {
        eapply map.getmany_of_list_in_map. eassumption.
      }
      simpl.
      intros. simp.
      match goal with
      | X: _ |- _ => specialize X with (1 := H); rename X into A
      end.
      destruct A as [A | A].
      + pose proof valid_FlatImp_vars_available_registers as V.
        eapply (proj1 (Forall_forall _ _) V).
        replace available_registers with (used ++ used0 ++ used1 ++ l3) by assumption.
        rewrite ?in_app_iff. auto.
      + rewrite map.get_empty in A. discriminate A.
    - eapply Forall_impl. 2: {
        eapply map.getmany_of_list_in_map. eassumption.
      }
      simpl.
      intros. simp.
      match goal with
      | X: _ |- _ => specialize X with (1 := H); rename X into A
      end.
      destruct A as [A | A].
      + pose proof valid_FlatImp_vars_available_registers as V.
        eapply (proj1 (Forall_forall _ _) V).
        replace available_registers with (used ++ used0 ++ used1 ++ l3) by assumption.
        rewrite ?in_app_iff. auto.
      + match goal with
        | X: _ |- _ => specialize X with (1 := A); rename X into B
        end.
        destruct B as [B | B].
        * pose proof valid_FlatImp_vars_available_registers as V.
          eapply (proj1 (Forall_forall _ _) V).
          replace available_registers with (used ++ used0 ++ used1 ++ l3) by assumption.
          rewrite ?in_app_iff. auto.
        * rewrite map.get_empty in B. discriminate B.
    - eapply FlatImp.ForallVars_stmt_impl; [|eassumption].
      simpl. intros. simp.
      match goal with
      | X: _ |- _ => specialize X with (1 := H); rename X into A
      end.
      destruct A as [A | A].
      + pose proof valid_FlatImp_vars_available_registers as V.
        eapply (proj1 (Forall_forall _ _) V).
        replace available_registers with (used ++ used0 ++ used1 ++ l3) by assumption.
        rewrite ?in_app_iff. auto.
      + match goal with
        | X: _ |- _ => specialize X with (1 := A); rename X into B
        end.
        destruct B as [B | B].
        * pose proof valid_FlatImp_vars_available_registers as V.
          eapply (proj1 (Forall_forall _ _) V).
          replace available_registers with (used ++ used0 ++ used1 ++ l3) by assumption.
          rewrite ?in_app_iff. auto.
        * match goal with
          | X: _ |- _ => specialize X with (1 := B); rename X into C
          end.
          destruct C as [C | C].
          -- pose proof valid_FlatImp_vars_available_registers as V.
             eapply (proj1 (Forall_forall _ _) V).
             replace available_registers with (used ++ used0 ++ used1 ++ l3) by assumption.
             rewrite ?in_app_iff. auto.
          -- rewrite map.get_empty in C. discriminate C.
    - eapply map.getmany_of_list_injective_NoDup. 3: eassumption. all: eassumption.
    - eapply map.getmany_of_list_injective_NoDup. 3: eassumption. all: eassumption.
    - unfold FlatToRiscvDef.stmt_not_too_big.
      pose proof (rename_preserves_stmt_size _ _ _ _ _ _ E1') as M.
      Fail rewrite <- M. (* PARAMRECORDS *)
      clear -H2 M.
      match goal with
      | _: _ = ?x |- ?x' < _ => change x' with x
      end.
      rewrite <- M.
      assumption.
  Qed.

  Lemma get_build_fun_pos_env: forall fnames r f pos0,
      In f fnames ->
      (forall f, In f fnames -> map.get r f <> None) ->
      pos0 mod 4 = 0 ->
      exists pos1, map.get (FlatToRiscvDef.build_fun_pos_env r pos0 fnames) f = Some pos1 /\ pos1 mod 4 = 0.
  Proof.
    induction fnames; intros.
    - simpl in *. contradiction.
    - simpl in *.
      pose proof (H0 a (or_introl eq_refl)) as P.
      destr (map.get r a). 2: contradiction. clear P.
      destruct H.
      + subst f. rewrite map.get_put_same. eauto.
      + rewrite map.get_put_dec.
        destruct_one_match.
        * subst. eauto.
        * eapply IHfnames.
          -- eassumption.
          -- intros. eapply H0. right. assumption.
          -- solve_divisibleBy4.
  Qed.

  Lemma init_code_to_loop_body_transition: forall ren m,
      compile_inv (related (initCodeGhostConsts ren) (FlatToRiscvDef.main_pos ren) true)
           (@hl_inv (FlattenExpr.mk_Semantics_params _) _ (funimpls srcprog) (init_code srcprog) spec) m ->
      compile_inv (related (loopBodyGhostConsts ren) (FlatToRiscvDef.loop_pos ren) false)
           (@hl_inv (FlattenExpr.mk_Semantics_params _) _ (funimpls srcprog) (loop_body srcprog) spec) m.
  Proof.
    intros.
    unfold hl_inv, compile_inv in *.
    destruct H as ((((((e & c) & t) & me) & l) & mc) & R). simp.
    refine (ex_intro _ (_, _, _, _, _, _) _); ssplit; try reflexivity; try eassumption.
    unfold related in *.
    case TODO_sam.
    Unshelve. assumption.
  Qed.

  Lemma putProgram_establishes_ll_inv: forall preInitial initial,
      putProgram srcprog preInitial = Some initial ->
      layout preInitial.(getMem) ->
      (* the registers must have some (unspecified) value, ie reading a register must not
         be undefined behavior: *)
      regs_initialized preInitial.(getRegs) ->
      preInitial.(getLog) = [] ->
      valid_machine initial -> (* or valid_machine preInitial and putProgram_preserves_sane condition? *)
      ll_inv initial.
  Proof.
    intros.
    unfold putProgram, MetricRiscvMachine.putProgram, RiscvMachine.putProgram.
    unfold ll_inv, runsToGood_Invariant.
    destruct_RiscvMachine preInitial.
    unfold putProgram, compile, composePhases, renamePhase, flattenPhase in *. simp. simpl in *.
    match goal with
    | _: riscvPhase ml ?R = Some _ |- _ => set (ren := R : RenamedProgram)
    end.
    exists srcprog, ren.
    split. {
      unfold riscvPhase in E. simp.
      (* TODO starting from here, this should be solved completely automatically *)
      repeat match goal with
             | H: @eq bool _ _ |- _ => autoforward with typeclass_instances in H
             end.
      rewrite ?app_length in *.
      subst ren.
      pose proof (word.unsigned_range (code_pastend ml)).
      pose proof (word.unsigned_range (code_start ml)).
      rewrite ?Nat2Z.inj_add in *.
      match goal with
      | |- _ < 4 * Z.of_nat ?L < _ => remember L as l
      end.
      simpl in *. (* PARAMRECORDS *)
      rewrite <- Heql in *.
      blia.
    }
    (* first, run init_sp_code: *)
    pose proof FlatToRiscvLiterals.compile_lit_correct_full_raw as P.
    cbv zeta in P. (* needed for COQBUG https://github.com/coq/coq/issues/11253 *)
    specialize P with (x := RegisterNames.sp) (v := init_sp).
    unfold runsTo in P. eapply P; clear P; simpl.
    { reflexivity. }
    2: {
      case TODO_sam. (* store program establisheds "program"/instruction memory related *)
    }
    { case TODO_sam. (* subset footpr XAddrs *) }
    { cbv. auto. }
    { assumption. }
    (* then, run init_code (using compiler simulation and correctness of init_code) *)
    pose proof
         (sim ren (initCodeGhostConsts ren) (FlatToRiscvDef.main_pos ren) eq_refl eq_refl) as P.
    unfold simulation, runsTo in P.
    rename H0 into Q. unfold layout in Q.
    unfold sep, map.split in Q.
    destruct Q as [ cdmem [ smem [ [ ? ? ] [ Q ? ] ] ] ].
    destruct Q as [ cmem  [ dmem [ [ ? ? ] [ ? ? ] ] ] ].
    subst.
    specialize P with
     (s1 := (srcprog.(funimpls), srcprog.(init_code), nil, dmem, map.empty, mkMetricLog 0 0 0 0)).
    eapply runsTo_weaken.
    - eapply P; clear P.
      + (* prove that the initial state (putProgram preInitial) is related ot the high-level
           initial state *)
        unfold related, compose_relation.
        unfold compiler.FlatToRiscvSimulation.related,
               compiler.FlattenExprSimulation.related,
               compiler.RegRename.related.
        refine (ex_intro _ (_, _, _, _, _, _) _).
        ssplit; try reflexivity.
        { eassumption. }
        { eassumption. }
        { unfold map.undef_on, map.agree_on. intros. reflexivity. }
        refine (ex_intro _ (_, _, _, _, _, _) _).
        unfold goodMachine.
        ssplit.
        { unfold envs_related.
          intros f [ [argnames resnames] body1 ] G.
          unfold initCodeGhostConsts, ren. cbn [e_impl funimpls].
          unfold rename_functions in E2.
          eapply map.map_all_values_fw.
          5: exact G. 4: exact E2.
          - eapply String.eqb_spec.
          - (* PARAMRECORDS *)
            unfold FlatImp.env, Semantics.funname_env. simpl. typeclasses eauto.
          - (* PARAMRECORDS *)
            unfold FlatImp.env, Semantics.funname_env. simpl. typeclasses eauto.
        }
        { reflexivity. }
        { reflexivity. }
        { intros. ssplit; reflexivity. }
        { unfold rename_stmt in E3. simp.
          do 2 eexists. eassumption. }
        { reflexivity. }
        { simpl. unfold riscvPhase in *. simpl in *. simp.
          edestruct stack_usage_correct as [P _]. 1: eassumption.
          simpl in P.
          eapply fits_stack_monotone. 1: exact P.
          subst num_stackwords.
          repeat match goal with
                 | H: @eq bool _ _ |- _ => autoforward with typeclass_instances in H
                 end.
          assumption.
        }
        { unfold good_e_impl.
          intros.
          simpl in H|-*.
          rename E2 into RenameEq.
          unfold rename_functions in RenameEq.
          unshelve epose proof (map.map_all_values_bw _ _ _ _ RenameEq _ _ H).
          { (* PARAMRECORDS *) unfold FlatImp.env, Semantics.funname_env. simpl. typeclasses eauto. }
          simp. destruct v1 as [ [argnames' retnames'] body' ].
          unfold flatten_functions in E5.
          rename E5 into FlattenEq.
          unshelve epose proof (map.map_all_values_bw _ _ _ _ FlattenEq _ _ H2r) as P.
          { (* PARAMRECORDS *) unfold env, FlatImp.env, Semantics.funname_env. simpl. typeclasses eauto. }
          { (* PARAMRECORDS *) unfold FlatImp.env, Semantics.funname_env. simpl. typeclasses eauto. }
          unfold flatten_function in P.
          simp.
          pose proof (funs_valid sat) as V.
          unfold ExprImp.valid_funs in V.
          specialize V with (1 := Pr).
          unfold ExprImp.valid_fun in V.
          destruct V.
          ssplit.
          - eapply rename_fun_valid; try eassumption.
            unfold ExprImp2FlatImp in *.
            simp.
            repeat match goal with
                   | H: @eq bool _ _ |- _ => autoforward with typeclass_instances in H
                   end.
            assumption.
          - case TODO_sam. (* remove "In funnames" condition *)
          - unfold FlatToRiscvDef.function_positions.
            simpl.
            eapply get_build_fun_pos_env.
            + case TODO_sam. (* remove "In funnames" condition *)
            + intros f' A C.
              apply (proj2 (sat.(funnames_matches_dom) f') A).
              match goal with
              | |- ?x = None => destr x; [exfalso|reflexivity]
              end.
              destruct p0 as [ [args res] body ].
              pose proof get_flatten_functions as P.
              specialize P with (1 := E1) (2 := FlattenEq). simp.
              unshelve epose proof (map.map_all_values_fw _ _ _ _ RenameEq _ _ Pl) as P'.
              { (* PARAMRECORDS *) unfold FlatImp.env, Semantics.funname_env. simpl. typeclasses eauto. }
              { (* PARAMRECORDS *) unfold FlatImp.env, Semantics.funname_env. simpl. typeclasses eauto. }
              simp.
              (* PARAMRECORDS *)
              match type of C with
              | ?x = None => match type of P'r with
                             | ?y = Some _ => change x with y in C
                             end
              end.
              congruence.
            + reflexivity.
        }
        { unfold FlatToRiscvDef.stmt_not_too_big.
          match goal with
          | H: rename_stmt _ _ _ = Some s |- _ => unfold rename_stmt in H; simp
          end.
          match goal with
          | H: rename _ _ _ = Some (_, s, _) |- _ => apply rename_preserves_stmt_size in H; rename H into B
          end.
          (* PARAMRECORDS *)
          match goal with
          | |- ?x < _ => replace x with (FlatImp.stmt_size s1)
          end.
          unfold ExprImp2FlatImp in *.
          simp.
          repeat match goal with
                 | H: @eq bool _ _ |- _ => autoforward with typeclass_instances in H
                 end.
          assumption.
        }
        { unfold rename_stmt in E3. simp. eapply rename_props in E0; cycle 1.
          { exact String.eqb_spec. }
          { typeclasses eauto. }
          { apply map.empty_injective. }
          { eapply map.not_in_range_empty. }
          { eapply NoDup_available_registers. }
          simp.
          unfold FlatToRiscvDef.valid_FlatImp_vars.
          eapply FlatImp.ForallVars_stmt_impl; [|eassumption].
          simpl. intros. simp.
          match goal with
          | X: _ |- _ => specialize X with (1 := H); rename X into A
          end.
          destruct A as [A | A].
          + pose proof valid_FlatImp_vars_available_registers as V.
            eapply (proj1 (Forall_forall _ _) V).
            replace available_registers with (used ++ l0) by assumption.
            rewrite ?in_app_iff. auto.
          + rewrite map.get_empty in A. discriminate A. }
        { reflexivity. }
        { unfold FlatToRiscvDef.main_pos. solve_divisibleBy4. }
        { simpl. eapply regs_initialized_put in H1. exact H1. }
        { simpl.
          unfold program_base, FlatToRiscvDef.main_pos,
                 FlatToRiscvDef.init_sp_insts, FlatToRiscvDef.backjump_insts.
          rewrite main_size_correct.
          solve_word_eq word_ok. }
        { simpl.
          unfold program_base, FlatToRiscvDef.main_pos,
                 FlatToRiscvDef.init_sp_insts, FlatToRiscvDef.backjump_insts.
          rewrite main_size_correct.
          solve_word_eq word_ok. }
        { simpl. unfold map.extends. intros. rewrite map.get_empty in H. discriminate. }
        { intros. rewrite map.get_empty in H. discriminate. }
        { simpl. rewrite map.get_put_same. unfold init_sp.
          f_equal.
          rewrite word.of_Z_unsigned.
          reflexivity. }
        { simpl. eapply @regs_initialized_put.
          - typeclasses eauto.
          - assumption. }
        { simpl. solve_word_eq word_ok. }
        { simpl. case TODO_sam. (* subset footpr xaddrs *) }
        { simpl. case TODO_sam. (* separation logic descrption of initial memory *) }
        { reflexivity. }
        { case TODO_sam. (* valid_machine *) }
      + (* prove correctness of ExprImp init code: *)
        eapply sat.(init_code_correct).
        rewrite heap_start_agree, heap_pastend_agree.
        assumption.
    - simpl. clear P.
      unfold ll_good.
      eapply init_code_to_loop_body_transition.
    Unshelve.
    all: intros; try exact True.
    all: try exact (mkMetricLog 0 0 0 0).
    all: try exact true.
    all: repeat apply pair.
    all: try apply nil.
    all: try apply FlatImp.SSkip.
  Qed.

  Lemma ll_inv_is_invariant: forall (st: MetricRiscvMachine),
      ll_inv st -> mcomp_sat (run1 iset) st ll_inv.
  Proof.
    intro st. unfold ll_inv. intros [ src [ ren [? ?] ] ].
    eapply mcomp_sat_weaken with (post1 := runsToGood_Invariant (ll_good src ren)). {
      intros. eauto.
    }
    eapply runsToGood_is_Invariant with
        (jump := - 4 * Z.of_nat (List.length (FlatToRiscvDef.loop_insts ren)))
        (pc_start := pc_start ren)
        (pc_end := word.add (pc_start ren) (word.of_Z (4 * Z.of_nat
                            (List.length (FlatToRiscvDef.loop_insts ren))))).
    - intro C.
      assert (word.of_Z (4 * Z.of_nat (Datatypes.length (FlatToRiscvDef.loop_insts ren))) =
              word.of_Z 0) as D. {
        transitivity (word.sub (pc_start ren) (pc_start ren)).
        - rewrite C at 1. simpl. (* PARAMRECORDS *) ring.
        - simpl. (* PARAMRECORDS *) ring.
      }
      apply (f_equal word.unsigned) in D.
      unshelve erewrite @word.unsigned_of_Z in D. 1: exact word_ok. (* PARAMRECORDS? *)
      unshelve erewrite word.unsigned_of_Z_0 in D. 1: exact word_ok. (* PARAMRECORDS? *)
      unfold word.wrap in D.
      rewrite Z.mod_small in D by (simpl in * (* PARAMRECORDS *); blia).
      destr (FlatToRiscvDef.loop_insts ren).
      + simpl in H. blia.
      + simpl in D. blia.
    - intros.
      unfold ll_good, compile_inv, related, compose_relation,
        FlatToRiscvSimulation.related in *.
      simp.
      etransitivity. 1: eassumption.
      destruct done.
      + simpl.
        unfold pc_start, program_base, FlatToRiscvDef.loop_pos, FlatToRiscvDef.main_pos.
        simpl.
        rewrite main_size_correct.
        solve_word_eq word_ok.
      + simpl.
        unfold pc_start, program_base, FlatToRiscvDef.loop_pos, FlatToRiscvDef.main_pos.
        simpl.
        rewrite main_size_correct.
        solve_word_eq word_ok.
    - (* Show that ll_ready (almost) ignores pc, nextPc, and metrics *)
      intros.
      unfold ll_good, compile_inv in *.
      unfold ll_good, compile_inv, related, compose_relation,
        FlatToRiscvSimulation.related in *.
      simp.
      destruct s1 as [ [ [ [ [ e1 c1 ] t1 ] m1 ] l1 ] mc1 ].
      assert (l1 = map.empty). {
        unfold hl_inv in *. simp. reflexivity.
      }
      subst.
      destruct s2 as [ [ [ [ [ e2 c2 ] t2 ] m2 ] l2 ] mc2 ].
      assert (l2 = map.empty). {
        unfold FlattenExprSimulation.related in *. simp. reflexivity.
      }
      subst.
      (* destruct_RiscvMachine state. TODO remove "simpl in *" from that? *)
      let r := fresh m "_regs" in
      let p := fresh m "_pc" in
      let n := fresh m "_npc" in
      let me := fresh m "_mem" in
      let x := fresh m "_xaddrs" in
      let l := fresh m "_log" in
      let mc := fresh m "_metrics" in
      destruct state as [ [r p n me x l] mc ].
      eexists. split; [|eassumption].
      refine (ex_intro _ (_, _, _, _, _, _) _). split; [eassumption|].
      refine (ex_intro _ (_, _, _, _, map.empty, mc2) _).
      repeat match goal with
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             | |- _ => progress cbv beta iota
             | |- _ => eassumption
             | |- _ => reflexivity
             end.
      + move H1lrl at bottom.
        unfold RegRename.related in *. simp.
        ssplit. all: try eassumption || reflexivity.
        * intros. ssplit; reflexivity.
        * do 2 eexists. eassumption.
      + simpl. unfold pc_start, program_base, FlatToRiscvDef.loop_pos, FlatToRiscvDef.main_pos.
        rewrite main_size_correct.
        solve_word_eq word_ok.
      + unfold goodMachine in *. simpl in *. simp.
        repeat match goal with
               | |- exists _, _  => eexists
               | |- _ /\ _ => split
               | |- _ => progress cbv beta iota
               | |- _ => eassumption
               | |- _ => reflexivity
               end.
        * intro x. intros v H. rewrite map.get_empty in H. discriminate.
        * intro x. intros v H. rewrite map.get_empty in H. discriminate.
        * case TODO_sam. (* show that backjump preserves valid_machine *)
    - unfold ll_good, compile_inv, related, compose_relation, FlatToRiscvSimulation.related,
             goodMachine.
      intros. simp. assumption.
    - case TODO_sam.
      (* needs stronger conditions
      destruct width_cases as [C | C]; rewrite C in *; split.
      all: let r := eval cbv in (2 ^ 20) in change (2 ^ 20) with r.
      all: let r := eval cbv in (2 ^ 32) in change (2 ^ 32) with r.
      all: let r := eval cbv in (2 ^ 64) in change (2 ^ 64) with r. *)
    - solve_divisibleBy4.
    - solve_word_eq word_ok.
    - unfold ll_good, compile_inv, related, compose_relation, FlatToRiscvSimulation.related,
             goodMachine.
      intros. simp. split.
      + eexists. (* TODO the jump back Jal has to be in xframe *) case TODO_sam.
      + case TODO_sam.
    - (* use compiler correctness for loop_body *)
      intros.
      pose proof (sim ren (loopBodyGhostConsts ren) (FlatToRiscvDef.loop_pos ren)) as P.
      unfold simulation, ExprImp.SimExec, runsTo in P.
      unfold ll_good in H1|-*. unfold compile_inv in H1. simp.
      eapply P; clear P.
      { case TODO_sam. (* funnames equal *) }
      { reflexivity. }
      { eassumption. }
      pose proof @loop_body_correct as P.
      simpl.
      destruct s1 as (((((e & c) & t) & m) & l) & mc).
      specialize (P (FlattenExpr.mk_Semantics_params _)).
      specialize P with (exec := ExprImp.SimExec).
      unfold ExprImp.SimExec in P.
      specialize P with (2 := H1r).
      cbn -[hl_inv] in *.
      eapply P; clear P.
      match goal with
      | |- ?G => let T := type of sat in replace G with T; [exact sat|]
      end.
      simpl.
      apply f_equal2; try reflexivity.
      apply f_equal2; try reflexivity.
      apply f_equal2; try reflexivity.
      apply f_equal2; try reflexivity.
      case TODO_sam. (* src from existential vs srcprog from Context *)
    - assumption.
    Unshelve.
    all: try (intros; exact True).
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

  Lemma pipeline_proofs:
    (forall preInitial initial,
        putProgram srcprog preInitial = Some initial ->
        ll_inv initial) /\
    (forall st, ll_inv st -> mcomp_sat (run1 iset) st ll_inv) /\
    (forall st, ll_inv st -> exists suff, spec.(goodTrace) (suff ++ st.(getLog))).
  Proof.
    split; [|split].
    - intros.
      eapply putProgram_establishes_ll_inv.
      + eassumption.
      + case TODO_sam.
      + case TODO_sam.
      + case TODO_sam.
      + case TODO_sam.
    - apply ll_inv_is_invariant.
    - exact ll_inv_implies_prefix_of_good.
  Qed.

End Pipeline1.
