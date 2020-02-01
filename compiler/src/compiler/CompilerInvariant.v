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

  Local Notation source_env := (@Pipeline.string_keyed_map p (list string * list string * Syntax.cmd)).

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

  Definition putProgram(prog: source_env)(preInitial: MetricRiscvMachine): option MetricRiscvMachine :=
    'Some insts <- compile_prog prog;
    Some (MetricRiscvMachine.putProgram (List.map encode insts) ml.(code_start) preInitial).

  Context (spec: @ProgramSpec (FlattenExpr.mk_Semantics_params _)).

  Let loop_pos := word.add ml.(code_start)
         (word.of_Z (4 * (Z.of_nat (List.length (FlatToRiscvDef.compile_lit RegisterNames.sp init_sp))) + 4)).

  Axiom Rdata: mem -> Prop. (* maybe (emp True) will be fine *)
  Axiom Rexec: mem -> Prop. (* maybe (emp True) will be fine *)

  Definition ll_good(done: bool)(mach: MetricRiscvMachine): Prop :=
    exists (prog: source_env) (instrs: list Instruction),
      compile_prog prog = Some instrs /\
      ProgramSatisfiesSpec "init"%string "loop"%string prog spec /\
      exists mH lH mcH,
        hl_inv spec mach.(getLog) mH lH mcH /\
        machine_ok ml.(code_start) ml.(stack_pastend) instrs
                   loop_pos (word.add loop_pos (word.of_Z (if done then 4 else 0))) mH Rdata Rexec mach.

  Definition ll_inv: MetricRiscvMachine -> Prop := runsToGood_Invariant ll_good.

  Add Ring wring : (word.ring_theory (word := Utility.word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := Utility.word)),
       constants [word_cst]).

  Definition layout: mem -> Prop :=
    (mem_available  ml.(code_start)  ml.(code_pastend) *
     mem_available  ml.(heap_start)  ml.(heap_pastend) *
     mem_available ml.(stack_start) ml.(stack_pastend))%sep.

  (*
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
  *)

  Lemma compile_prog_to_compile: forall prog instrs,
      compile_prog prog = Some instrs ->
      exists before main positions,
        compile ml prog = Some (main, positions) /\
        instrs = before ++ main.
  Proof.
    intros. unfold compile_prog in *. simp. do 3 eexists.
    split; [reflexivity|].
    match goal with
    | |- ?A ++ ?i1 :: ?i2 :: ?i3 :: ?B = ?R => change (A ++ [i1; i2; i3] ++ B = R)
    end.
    rewrite app_assoc.
    reflexivity.
  Qed.

  Definition mem_contains_bytes(m: mem)(a: Utility.word)(bytes: list Byte.byte): Prop :=
    forall (i: nat) (b: Byte.byte),
      nth_error bytes i = Some b ->
      map.get m (word.add a (word.of_Z (Z.of_nat i))) = Some (word.of_Z (Z.of_N (Byte.to_N b))).

  Lemma establish_ll_inv: forall (srcprog: source_env)
                                 (sat: ProgramSatisfiesSpec "init"%string "loop"%string srcprog spec)
                                 (initial: MetricRiscvMachine) instrs,
      compile_prog srcprog = Some instrs ->
      mem_contains_bytes initial.(getMem) ml.(code_start) (instrencode instrs) ->
      initial.(getNextPc) = word.add initial.(getPc) (word.of_Z 4) ->
      regs_initialized initial.(getRegs) ->
      map.get initial.(getRegs) RegisterNames.sp = Some ml.(stack_pastend) ->
      valid_machine initial ->
      ll_inv initial.
  Proof.
    intros.
    unfold ll_inv, runsToGood_Invariant.
    destruct_RiscvMachine initial.
(*
    exists instrs, ml.(code_start)
    exists Rdata, Rexec.
    lazymatch goal with
    | _: riscvPhase ml ?R = Some _ |- _ => set (ren := R)
    end.
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
    pose proof (sim ml init_fun_pos "init"%string
                    (word.add ml.(code_start) (word.of_Z (4 * Z.of_nat
                            (List.length (FlatToRiscvDef.compile_lit RegisterNames.sp init_sp)))))
                    Rdata Rexec) as P.
    unfold simulation, runsTo in P.
    rename H0 into Q. unfold layout in Q.
    unfold sep, map.split in Q.
    destruct Q as [ cdmem [ smem [ [ ? ? ] [ Q ? ] ] ] ].
    destruct Q as [ cmem  [ dmem [ [ ? ? ] [ ? ? ] ] ] ].
    subst.
*)
    case TODO_sam.
  Qed.

  Lemma putProgram_establishes_ll_inv: forall srcprog
      (sat: ProgramSatisfiesSpec "init"%string "loop"%string srcprog spec)
      preInitial initial,
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
    unfold putProgram, compile_prog, compile, composePhases, renamePhase, flattenPhase in *. simp. simpl in *.
    case TODO_sam.
  Qed.
(*
    exists srcprog.
    match goal with
    | _: map.get _ "init"%string = Some ?pos |- _ => rename pos into init_fun_pos
    end.
    match goal with
    | _: map.get _ "loop"%string = Some ?pos |- _ => rename pos into loop_fun_pos
    end.
    exists init_fun_pos, "init"%string.
    exists (word.add ml.(code_start) (word.of_Z (4 * Z.of_nat
                            (List.length (FlatToRiscvDef.compile_lit RegisterNames.sp init_sp))))).
    assert (Rdata: mem -> Prop) by case TODO_sam. (* will probably need to go outside existential *)
    assert (Rexec: mem -> Prop) by case TODO_sam. (* will probably need to go outside existential *)
    exists Rdata, Rexec.
    lazymatch goal with
    | _: riscvPhase ml ?R = Some _ |- _ => set (ren := R)
    end.
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
    pose proof (sim ml init_fun_pos "init"%string
                    (word.add ml.(code_start) (word.of_Z (4 * Z.of_nat
                            (List.length (FlatToRiscvDef.compile_lit RegisterNames.sp init_sp)))))
                    Rdata Rexec) as P.
    unfold simulation, runsTo in P.
    rename H0 into Q. unfold layout in Q.
    unfold sep, map.split in Q.
    destruct Q as [ cdmem [ smem [ [ ? ? ] [ Q ? ] ] ] ].
    destruct Q as [ cmem  [ dmem [ [ ? ? ] [ ? ? ] ] ] ].
    subst.
    specialize P with
        (s1 := (srcprog, (Syntax.cmd.call nil "init"%string nil), nil,
                dmem, map.empty, bedrock2.MetricLogging.mkMetricLog 0 0 0 0)).
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
        { unfold map.undef_on, map.agree_on. intros. reflexivity. }
        refine (ex_intro _ (_, _, _, _, _, _) _).
        unfold goodMachine.
        ssplit.
        { unfold envs_related.
          intros f [ [argnames resnames] body1 ] G.
          unfold rename_functions in E4.
          eapply map.map_all_values_fw.
          5: exact G. 4: exact E4.
          - eapply String.eqb_spec.
          - typeclasses eauto.
          - typeclasses eauto.
        }
        { reflexivity. }
        { reflexivity. }
        { intros. ssplit; reflexivity. }
        { simpl. do 2 eexists. reflexivity. }
        { case TODO_sam. (* how to get rid of SSkip? *) }
        { case TODO_sam. (* divisible by 4 *) }
        { case TODO_sam. (* divisible by 4 *) }
        { case TODO_sam. (* get in fun_pus_env *) }
        { simpl. unfold riscvPhase in *. simpl in *. simp.
          case TODO_sam.
          (*
          edestruct stack_usage_correct as [P _]. 1: eassumption.
          simpl in P.
          eapply fits_stack_monotone. 1: exact P.
          subst num_stackwords.
          repeat match goal with
                 | H: @eq bool _ _ |- _ => autoforward with typeclass_instances in H
                 end.
          assumption.
          *)
        }
        { unfold good_e_impl.
          intros.
          simpl in H|-*.
          rename E4 into RenameEq.
          unfold rename_functions in RenameEq.
          unshelve epose proof (map.map_all_values_bw _ _ _ _ RenameEq _ _ H).
          simp. destruct v1 as [ [argnames' retnames'] body' ].
          unfold flatten_functions in E3.
          rename E3 into FlattenEq.
          unshelve epose proof (map.map_all_values_bw _ _ _ _ FlattenEq _ _ H2r) as P.
          { (* PARAMRECORDS *) unfold FlattenExpr.ExprImp_env. simpl. typeclasses eauto. }
          { (* PARAMRECORDS *) unfold FlattenExpr.FlatImp_env. simpl. typeclasses eauto. }
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
            case TODO_sam.
            (*
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
            *)
        }
        { simpl. eapply regs_initialized_put in H1. exact H1. }
        { simpl. solve_word_eq word_ok. }

(*
        { progress unfold FlatToRiscvDef.stmt_not_too_big.
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
        *)
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
        pose proof sat.(init_code_correct) as P.
        destruct P as [ init_code [? P] ].
        (* evar envs? *) case TODO_sam.
    - simpl. clear P.
      unfold ll_good.
      (* eapply init_code_to_loop_body_transition. *) case TODO_sam.
    Unshelve.
    all: intros; try exact True.
    all: try exact (bedrock2.MetricLogging.mkMetricLog 0 0 0 0).
    all: try exact true.
    all: repeat apply pair.
    all: try apply nil.
    all: try apply FlatImp.SSkip.
  Qed.
*)

  Lemma machine_ok_frame_instrs_app_l: forall p_code p_stack_pastend i1 i2 p_call pc mH Rdata Rexec mach,
      machine_ok p_code p_stack_pastend (i1 ++ i2) p_call pc mH Rdata Rexec mach ->
      machine_ok p_code p_stack_pastend i2 p_call pc mH Rdata
                 (Rexec * ptsto_bytes (word.add p_code (word.of_Z (4 * Z.of_nat (List.length i1))))
                                      (instrencode i2))%sep
                 mach.
  Proof.
    unfold machine_ok.
    intros. simp.
    ssplit; eauto.
    case TODO_sam.
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
      (* destruct_RiscvMachine state. TODO remove "simpl in *" from that? *)
      let r := fresh m "_regs" in
      let p := fresh m "_pc" in
      let n := fresh m "_npc" in
      let me := fresh m "_mem" in
      let x := fresh m "_xaddrs" in
      let l := fresh m "_log" in
      let mc := fresh m "_metrics" in
      destruct state as [ [r p n me x l] mc ].
      unfold getRegs, getMachine, getPc, getNextPc, getMem, getLog, withPc, RiscvMachine.withPc, withNextPc,
             RiscvMachine.withNextPc,
             withMetrics in *.
      repeat match goal with
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             | |- _ => progress cbv beta iota
             | |- _ => eassumption
             | |- _ => reflexivity
             end.
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
      match goal with
      | H: _ |- _ => specialize loop_body_correct
                       with (1 := H) (mc := bedrock2.MetricLogging.mkMetricLog 0 0 0 0)
      end.
      match goal with
      | H: hl_inv _ _ _ _ _ |- _ => destruct H as [ ? [? ? ] ]
      end.
      lazymatch goal with
      | H: context[@word.add ?w ?wo ?x (word.of_Z 0)] |- _ =>
        replace (@word.add w wo x (word.of_Z 0)) with x in H
      end.
      2: {
        (* PARAMRECORDS *)
        symmetry. unshelve eapply SimplWordExpr.add_0_r. unfold Semantics.word. simpl. typeclasses eauto.
      }
      subst.
      match goal with
      | H: _ |- _ => pose proof H; apply compile_prog_to_compile in H;
                     destruct H as [ before [ finstrs [ positions [ ? ? ] ] ] ]
      end.
      subst.
      eapply runsTo_weaken.
      + pose proof compiler_correct as P. unfold runsTo in P.
        eapply P; clear P; try eassumption.
        eapply machine_ok_frame_instrs_app_l. eassumption.
      + cbv beta.
        intros. simp. do 2 eexists.
        ssplit; try eassumption.
        do 3 eexists.
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

  Lemma pipeline_proofs srcprog (sat: ProgramSatisfiesSpec "init"%string "loop"%string srcprog spec):
    (forall preInitial initial,
        putProgram srcprog preInitial = Some initial ->
        ll_inv initial) /\
    (forall st, ll_inv st -> GoFlatToRiscv.mcomp_sat (run1 iset) st ll_inv) /\
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
      + case TODO_sam.
    - apply ll_inv_is_invariant.
    - exact ll_inv_implies_prefix_of_good.
    Unshelve. all: case TODO_sam.
  Qed.

End Pipeline1.
