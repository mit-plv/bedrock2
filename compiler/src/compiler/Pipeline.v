Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Export coqutil.Decidable.
Require        compiler.ExprImp.
Require Export compiler.FlattenExprDef.
Require Export compiler.FlattenExpr.
Require        compiler.FlatImp.
Require Export riscv.Spec.Machine.
Require Export riscv.Platform.Run.
Require Export riscv.Platform.RiscvMachine.
Require Export riscv.Platform.MetricLogging.
Require Export riscv.Utility.Monads.
Require Import riscv.Utility.runsToNonDet.
Require Export riscv.Platform.MetricRiscvMachine.
Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.MetricLogging.
Require Import compiler.ExprImp.
Require Import compiler.FlattenExprDef.
Require Import compiler.FlattenExpr.
Require Import compiler.FlatImp.
Require Import compiler.NameGen.
Require Import compiler.StringNameGen.
Require Export compiler.util.Common.
Require Export coqutil.Decidable.
Require Export riscv.Utility.Encode.
Require Import riscv.Spec.Decode.
Require Export riscv.Spec.Primitives.
Require Export riscv.Spec.MetricPrimitives.
Require Import compiler.GoFlatToRiscv.
Require Import riscv.Utility.MkMachineWidth.
Require Export riscv.Proofs.DecodeEncode.
Require Export riscv.Proofs.EncodeBound.
Require Import riscv.Utility.Utility.
Require Export riscv.Platform.Memory.
Require Export riscv.Utility.InstructionCoercions.
Require Import compiler.SeparationLogic.
Require Import compiler.Spilling.
Require Import compiler.RegAlloc.
Require Import compiler.Simulation.
Require Import compiler.RiscvEventLoop.
Require Import bedrock2.MetricLogging.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import compiler.DivisibleBy4.
Require Export coqutil.Word.SimplWordExpr.
Require Export compiler.Registers.
Require Import compiler.ForeverSafe.
Require Import FunctionalExtensionality.
Require Import coqutil.Tactics.autoforward.
Require Import compiler.FitsStack.
Require Import compiler.LowerPipeline.
Require Import bedrock2.WeakestPreconditionProperties.
Import Utility.

Section WithWordAndMem.
  Context {width: Z} {BW: Bitwidth width} {word: Interface.word width} {mem : map.map word byte}.

  Record Lang := {
    Program: Type;
    GetArgCount(p: Program)(funcname: string): option nat;
    GetRetCount(p: Program)(funcname: string): option nat;
    Valid: Program -> Prop;
    Call(p: Program)(funcname: string)(t: trace)(m: mem)(argvals: list word)
        (post: trace -> mem -> list word -> Prop): Prop;
  }.

  Record phase_correct{L1 L2: Lang}{compile: L1.(Program) -> result L2.(Program)}: Prop := {
    phase_preserves_argcount: forall p1 p2,
        compile p1 = Success p2 ->
        forall fname, L1.(GetArgCount) p1 fname = L2.(GetArgCount) p2 fname;
    phase_preserves_retcount: forall p1 p2,
        compile p1 = Success p2 ->
        forall fname, L1.(GetRetCount) p1 fname = L2.(GetRetCount) p2 fname;
    phase_preserves_valid: forall p1 p2,
        compile p1 = Success p2 ->
        L1.(Valid) p1 ->
        L2.(Valid) p2;
    phase_preserves_post: forall p1 p2,
        L1.(Valid) p1 ->
        compile p1 = Success p2 ->
        forall fname t m argvals post,
        L1.(Call) p1 fname t m argvals post ->
        L2.(Call) p2 fname t m argvals post;
  }.

  Arguments phase_correct : clear implicits.

  Definition compose_phases{A B C: Type}(phase1: A -> result B)(phase2: B -> result C)(a: A) :=
    b <- phase1 a;; phase2 b.

  Lemma compose_phases_correct{L1 L2 L3: Lang}
        {compile12: L1.(Program) -> result L2.(Program)}
        {compile23: L2.(Program) -> result L3.(Program)}:
    phase_correct L1 L2 compile12 ->
    phase_correct L2 L3 compile23 ->
    phase_correct L1 L3 (compose_phases compile12 compile23).
  Proof.
    unfold compose_phases.
    intros [A12 R12 V12 C12] [A23 R23 V23 C23].
    split; intros; fwd; eauto.
    - etransitivity.
      + eapply A12. eassumption.
      + eapply A23. eassumption.
    - etransitivity.
      + eapply R12. eassumption.
      + eapply R23. eassumption.
  Qed.

  Section WithMoreParams.
    Context {Zlocals: map.map Z word}
            {string_keyed_map: forall T: Type, map.map string T} (* abstract T for better reusability *)
            {ext_spec: ExtSpec}
            {word_ok : word.ok word}
            {mem_ok: map.ok mem}
            {string_keyed_map_ok: forall T, map.ok (string_keyed_map T)}
            {Zlocals_ok: map.ok Zlocals}.

    Context {ext_spec_ok : Semantics.ext_spec.ok ext_spec}.

    (* for riscv phase: *)
    Context {Registers: map.map Z word}.
    Context {M: Type -> Type}.
    Context {MM: Monad M}.
    Context {RVM: RiscvProgram M word}.
    Context {PRParams: PrimitivesParams M MetricRiscvMachine}.
    Context {word_riscv_ok: RiscvWordProperties.word.riscv_ok word}.
    Context {Registers_ok: map.ok Registers}.
    Context {PR: MetricPrimitives PRParams}.
    Context {iset: InstructionSet}.
    Context {BWM: bitwidth_iset width iset}.
    Context (compile_ext_call : string_keyed_map (nat * nat * Z) -> Z -> Z -> FlatImp.stmt Z ->
                                list Instruction).
    Context (compile_ext_call_correct: forall resvars extcall argvars,
                compiles_FlatToRiscv_correctly compile_ext_call compile_ext_call
                                               (FlatImp.SInteract resvars extcall argvars)).
    Context (compile_ext_call_length_ignores_positions:
               forall stackoffset posmap1 posmap2 c pos1 pos2,
                List.length (compile_ext_call posmap1 pos1 stackoffset c) =
                List.length (compile_ext_call posmap2 pos2 stackoffset c)).

    Definition locals_based_call_spec{Var Cmd: Type}{locals: map.map Var word}
               (Exec: string_keyed_map (list Var * list Var * Cmd) ->
                      Cmd -> trace -> mem -> locals -> MetricLog ->
                      (trace -> mem -> locals -> MetricLog -> Prop) -> Prop)
               (e: string_keyed_map (list Var * list Var * Cmd))(f: string)
               (t: trace)(m: mem)(argvals: list word)
               (post: trace -> mem -> list word -> Prop): Prop :=
      exists argnames retnames fbody,
        map.get e f = Some (argnames, retnames, fbody) /\
        forall l mc, map.of_list_zip argnames argvals = Some l ->
                     Exec e fbody t m l mc (fun t' m' l' mc' =>
                       exists retvals, map.getmany_of_list l' retnames = Some retvals /\
                                       post t' m' retvals).

    Definition ParamsNoDup{Var: Type}: (list Var * list Var * FlatImp.stmt Var) -> Prop :=
      fun '(argnames, retnames, body) => NoDup argnames /\ NoDup retnames.

    Definition SrcLang: Lang := {|
      Program := string_keyed_map (list string * list string * Syntax.cmd);
      GetArgCount := get_argcount;
      GetRetCount := get_retcount;
      Valid := map.forall_values ExprImp.valid_fun;
      Call := locals_based_call_spec Semantics.exec;
    |}.
    (* |                 *)
    (* | FlattenExpr     *)
    (* V                 *)
    Definition FlatWithStrVars: Lang := {|
      Program := string_keyed_map (list string * list string * FlatImp.stmt string);
      GetArgCount := get_argcount;
      GetRetCount := get_retcount;
      Valid := map.forall_values ParamsNoDup;
      Call := locals_based_call_spec FlatImp.exec;
    |}.
    (* |                 *)
    (* | RegAlloc        *)
    (* V                 *)
    Definition FlatWithZVars: Lang := {|
      Program := string_keyed_map (list Z * list Z * FlatImp.stmt Z);
      GetArgCount := get_argcount;
      GetRetCount := get_retcount;
      Valid := map.forall_values ParamsNoDup;
      Call := locals_based_call_spec FlatImp.exec;
    |}.
    (* |                 *)
    (* | Spilling        *)
    (* V                 *)
    Definition FlatWithRegs: Lang := {|
      Program := string_keyed_map (list Z * list Z * FlatImp.stmt Z);
      GetArgCount := get_argcount;
      GetRetCount := get_retcount;
      Valid := map.forall_values FlatToRiscvDef.valid_FlatImp_fun;
      Call := locals_based_call_spec FlatImp.exec;
    |}.
    (* |                 *)
    (* | FlatToRiscv     *)
    (* V                 *)
    Definition RiscvLang: Lang := {|
      Program :=
        list Instruction *                 (* <- code of all functions concatenated             *)
        string_keyed_map (nat * nat * Z) * (* <- (argcount, retcount, offset) for each function *)
        Z                                  (* <- required stack space in XLEN-bit words         *);
      GetArgCount '(insts, finfo, req_stack_size) := getFstOfThree finfo;
      GetRetCount '(insts, finfo, req_stack_size) := getSndOfThree finfo;
      (* bounds in instructions are checked by `ptsto_instr` *)
      Valid '(insts, finfo, req_stack_size) := map.forall_values max8args finfo;
      Call := riscv_call;
    |}.

    Lemma flatten_functions_NoDup: forall funs funs',
        (forall f argnames retnames body,
          map.get funs f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames) ->
        flatten_functions funs = Success funs' ->
        forall f argnames retnames body,
          map.get funs' f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames.
    Proof.
      unfold flatten_functions. intros.
      eapply map.try_map_values_bw in H0. 2: eassumption.
      unfold flatten_function in *. fwd.
      eapply H. eassumption.
    Qed.

    Lemma flattening_correct: phase_correct SrcLang FlatWithStrVars flatten_functions.
    Proof.
      unfold SrcLang, FlatWithStrVars.
      split; cbn. {
        unfold get_argcount, getFstOfThree, flatten_functions. intros.
        destr (map.get p1 fname).
        - destruct p as ((argnames & retnames) & body).
          eapply map.try_map_values_fw in H. 2: exact E.
          fwd. destruct v2 as ((argnames2 & retnames2) & body2).
          unfold flatten_function in *. fwd. reflexivity.
        - destr (map.get p2 fname). 2: reflexivity.
          exfalso.
          eapply map.try_map_values_bw in H. 2: exact E0.
          fwd. congruence.
      }
      { unfold get_retcount, getSndOfThree, flatten_functions. intros.
        destr (map.get p1 fname).
        - destruct p as ((argnames & retnames) & body).
          eapply map.try_map_values_fw in H. 2: exact E.
          fwd. destruct v2 as ((argnames2 & retnames2) & body2).
          unfold flatten_function in *. fwd. reflexivity.
        - destr (map.get p2 fname). 2: reflexivity.
          exfalso.
          eapply map.try_map_values_bw in H. 2: exact E0.
          fwd. congruence.
      }
      { unfold map.forall_values, ParamsNoDup.
        intros. destruct v as ((argnames & retnames) & body).
        eapply flatten_functions_NoDup; try eassumption.
        unfold valid_fun in *.
        intros. specialize H0 with (1 := H2). simpl in H0. eapply H0.
      }
      unfold locals_based_call_spec. intros. fwd.
      pose proof H0 as GF.
      unfold flatten_functions in GF.
      eapply map.try_map_values_fw in GF. 2: eassumption.
      unfold flatten_function in GF. fwd.
      eexists _, _, _. split. 1: eassumption.
      intros.
      eapply FlatImp.exec.weaken.
      - eapply flattenStmt_correct_aux with (mcH := mc).
        + eassumption.
        + eauto.
        + reflexivity.
        + match goal with
          | |- ?p = _ => rewrite (surjective_pairing p)
          end.
          reflexivity.
        + intros x k A. assumption.
        + unfold map.undef_on, map.agree_on. cbn. intros k A.
          rewrite map.get_empty. destr (map.get l k). 2: reflexivity. exfalso.
          unfold map.of_list_zip in H0.
          edestruct (map.putmany_of_list_zip_find_index _ _ _ _ _ _ H1 E) as [G | G]. 2: {
            rewrite map.get_empty in G. discriminate.
          }
          destruct G as (i & G1 & G2).
          eapply nth_error_In in G1.
          eapply start_state_spec. 2: exact A.
          eapply ListSet.In_list_union_l. eapply ListSet.In_list_union_l. assumption.
        + eapply @freshNameGenState_disjoint_fbody.
      - simpl. intros. fwd. eauto using map.getmany_of_list_extends.
    Qed.

    Lemma regalloc_functions_NoDup: forall funs funs',
        regalloc_functions funs = Success funs' ->
        forall f argnames retnames body,
          map.get funs' f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames.
    Proof.
      unfold regalloc_functions, check_funcs. intros.
      fwd.
      eapply map.try_map_values_bw in E. 2: eassumption.
      fwd.
      eapply map.get_forall_success in E0. 2: eassumption.
      unfold lookup_and_check_func, check_func, assert in *. fwd.
      rewrite <- E1, <- E4.
      split; apply List.NoDup_dedup.
    Qed.

    Lemma regalloc_correct: phase_correct FlatWithStrVars FlatWithZVars regalloc_functions.
    Proof.
      unfold FlatWithStrVars, FlatWithZVars. split; cbn. {
        unfold get_argcount, getFstOfThree, regalloc_functions. intros. fwd.
        destr (map.get p1 fname).
        - destruct p as ((argnames & retnames) & body).
          eapply map.try_map_values_fw in E. 2: exact E1.
          fwd. destruct v2 as ((argnames2 & retnames2) & body2).
          unfold regalloc_function, lookups in *. fwd.
          apply_in_hyps @List.length_all_success.
          rewrite List.map_length in *.
          congruence.
        - destr (map.get p2 fname). 2: reflexivity.
          exfalso.
          eapply map.try_map_values_bw in E. 2: exact E2.
          fwd. congruence.
      }
      { unfold get_retcount, getSndOfThree, regalloc_functions. intros. fwd.
        destr (map.get p1 fname).
        - destruct p as ((argnames & retnames) & body).
          eapply map.try_map_values_fw in E. 2: exact E1.
          fwd. destruct v2 as ((argnames2 & retnames2) & body2).
          unfold regalloc_function, lookups in *. fwd.
          apply_in_hyps @List.length_all_success.
          rewrite List.map_length in *.
          congruence.
        - destr (map.get p2 fname). 2: reflexivity.
          exfalso.
          eapply map.try_map_values_bw in E. 2: exact E2.
          fwd. congruence.
      }
      { unfold map.forall_values, ParamsNoDup. intros.
        destruct v as ((argnames & retnames) & body).
        eapply regalloc_functions_NoDup; eassumption.
      }
      unfold locals_based_call_spec.
      intros. fwd.
      pose proof H0 as GR.
      unfold regalloc_functions in GR.
      fwd. rename E into GR.
      eapply map.try_map_values_fw in GR. 2: eassumption.
      fwd. clear GRp0.
      pose proof E0 as C.
      unfold check_funcs in E0.
      eapply map.get_forall_success in E0. 2: eassumption.
      unfold lookup_and_check_func, check_func in E0. fwd.

      eexists _, _, _. split. 1: eassumption. intros.
      unfold map.of_list_zip in *.
      apply_in_hyps assert_ins_same_length.
      apply_in_hyps assignments_same_length.
      apply_in_hyps @map.putmany_of_list_zip_sameLength.
      assert (List.length argnames = List.length argvals) as P by congruence.
      eapply map.sameLength_putmany_of_list in P. destruct P as [st2 P].
      eapply FlatImp.exec.weaken.
      - eapply checker_correct; eauto.
        eapply states_compat_precond.
        edestruct putmany_of_list_zip_states_compat as (lL' & P' & Cp); try eassumption.
        1: eapply states_compat_empty.
        rewrite H1 in P'. inversion P'. exact Cp.
      - simpl. intros. fwd. eexists. split. 2: eassumption.
        eauto using states_compat_getmany.
    Qed.

    Ltac debool :=
      repeat match goal with
             | H: (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H
             | H: _ /\ _ |- _ => destruct H as [? H]
             | H: _ <? _ = true |- _ => eapply Z.ltb_lt in H
             | H: (_ <=? _)%nat = true |- _ => eapply Nat.leb_le in H
             end.

    Lemma spilling_preserves_valid: forall p1 p2 : string_keyed_map (list Z * list Z * stmt Z),
        spill_functions p1 = Success p2 ->
        map.forall_values ParamsNoDup p1 ->
        map.forall_values FlatToRiscvDef.valid_FlatImp_fun p2.
    Proof.
      unfold spill_functions, map.forall_values. intros.
      eapply map.try_map_values_bw in H. 2: eassumption.
      unfold spill_fun in H. fwd.
      unfold FlatToRiscvDef.valid_FlatImp_fun, FlatToRiscvDef.valid_FlatImp_var,
      FlatToRiscvDef.valid_FlatImp_vars,
      FlatToRiscvDef.valid_FlatImp_var, fp in *.
      debool.
      ssplit.
      - rewrite ?List.firstn_length. change (List.length (Registers.reg_class.all _)) with 8%nat.
        f_equal. blia.
      - rewrite ?List.firstn_length. change (List.length (Registers.reg_class.all _)) with 8%nat.
        f_equal. blia.
      - cbn. ssplit.
        + blia.
        + blia.
        + eapply set_vars_to_reg_range_valid_vars; unfold a0, a7; try blia.
          eapply List.forallb_to_Forall. 2: eassumption.
          unfold is_valid_src_var. intros. debool. assumption.
        + eapply spill_stmt_valid_vars. 1: reflexivity.
          unfold valid_vars_src.
          eapply max_var_sound.
          eapply FlatImp.forallb_vars_stmt_correct.
          2: eassumption.
          unfold is_valid_src_var.
          intros; rewrite ?Bool.andb_true_iff, ?Z.ltb_lt; unfold fp; blia.
        + eapply set_reg_range_to_vars_valid_vars; unfold a0, a7; try blia.
          eapply List.forallb_to_Forall. 2: eassumption.
          unfold is_valid_src_var. intros. debool. assumption.
      - cbn. ssplit.
        + apply set_vars_to_reg_range_uses_standard_arg_regs.
        + apply spill_stmt_uses_standard_arg_regs.
        + apply set_reg_range_to_vars_uses_standard_arg_regs.
    Qed.

    Lemma spilling_correct: phase_correct FlatWithZVars FlatWithRegs spill_functions.
    Proof.
      unfold FlatWithZVars, FlatWithRegs. split; cbn.
      { unfold get_argcount, getFstOfThree, spill_functions. intros. fwd.
        destr (map.get p1 fname).
        - destruct p as ((argnames & retnames) & body).
          eapply map.try_map_values_fw in E. 2: exact H.
          fwd. destruct v2 as ((argnames2 & retnames2) & body2).
          unfold spill_fun in *. fwd.
          f_equal. rewrite List.firstn_length.
          change (Datatypes.length (reg_class.all reg_class.arg)) with 8%nat. blia.
        - destr (map.get p2 fname). 2: reflexivity.
          exfalso.
          eapply map.try_map_values_bw in H. 2: exact E0.
          fwd. congruence.
      }
      { unfold get_retcount, getSndOfThree, regalloc_functions. intros. fwd.
        destr (map.get p1 fname).
        - destruct p as ((argnames & retnames) & body).
          eapply map.try_map_values_fw in E. 2: exact H.
          fwd. destruct v2 as ((argnames2 & retnames2) & body2).
          unfold spill_fun in *. fwd.
          f_equal. rewrite List.firstn_length.
          change (Datatypes.length (reg_class.all reg_class.arg)) with 8%nat. blia.
        - destr (map.get p2 fname). 2: reflexivity.
          exfalso.
          eapply map.try_map_values_bw in H. 2: exact E0.
          fwd. congruence.
      }
      1: exact spilling_preserves_valid.
      unfold locals_based_call_spec. intros. fwd.
      pose proof H0 as GL.
      unfold spill_functions in GL.
      eapply map.try_map_values_fw in GL. 2: eassumption.
      destruct GL as (((argnames2 & retnames2) & fbody2) & Sp & G2).
      exists argnames2, retnames2, fbody2.
      split. 1: exact G2.
      eapply spill_fun_correct; eassumption.
    Qed.

    Lemma riscv_phase_correct: phase_correct FlatWithRegs RiscvLang (riscvPhase compile_ext_call).
    Proof.
      unfold FlatWithRegs, RiscvLang.
      split; cbn. 1, 2: intros p1 ((? & finfo) & ?).
      - eapply riscvPhase_preserves_argcount. assumption.
      - eapply riscvPhase_preserves_retcount. assumption.
      - eapply riscv_phase_preserves_valid. assumption.
      - eapply flat_to_riscv_correct; eassumption.
    Qed.

    Definition compile:
      string_keyed_map (list string * list string * cmd) ->
      result (list Instruction * string_keyed_map (nat * nat * Z) * Z) :=
      (compose_phases flatten_functions
      (compose_phases regalloc_functions
      (compose_phases spill_functions
                      (riscvPhase compile_ext_call)))).

    Lemma composed_compiler_correct: phase_correct SrcLang RiscvLang compile.
    Proof.
      unfold compile.
      exact (compose_phases_correct flattening_correct
            (compose_phases_correct regalloc_correct
            (compose_phases_correct spilling_correct
                                    riscv_phase_correct))).
    Qed.

    (* restates composed_compiler_correct by unfolding definitions used to compose phases,
       and turning exists in hyps into toplevel foralls *)
    Lemma compiler_correct: forall
        (* input of compilation: *)
        (functions: string_keyed_map (list string * list string * cmd))
        (* output of compilation: *)
        (instrs: list Instruction) (finfo: string_keyed_map (nat * nat * Z)) (req_stack_size: Z)
        (* function we choose to call: *)
        (fname: string) (argnames retnames: list string) (fbody: cmd)
        (* high-level initial state & post on final state: *)
        (t: trace) (mH: mem) (argvals: list word) (post: trace -> mem -> list word -> Prop),
        ExprImp.valid_funs functions ->
        compile functions = Success (instrs, finfo, req_stack_size) ->
        map.get functions fname = Some (argnames, retnames, fbody) ->
        (forall l mc,
              map.of_list_zip argnames argvals = Some l ->
              Semantics.exec functions fbody t mH l mc
                (fun t' m' l' mc' => exists retvals: list word,
                     map.getmany_of_list l' retnames = Some retvals /\ post t' m' retvals)) ->
        exists (f_rel_pos: Z),
          map.get finfo fname = Some (List.length argnames, List.length retnames, f_rel_pos) /\
          forall (* low-level machine on which we're going to run the compiled program: *)
                 (initial: MetricRiscvMachine)
                 (* ghost vars that help describe the low-level machine: *)
                 (stack_lo stack_hi: word) (ret_addr p_funcs: word) (Rdata Rexec: mem -> Prop),
            req_stack_size <= word.unsigned (word.sub stack_hi stack_lo) / bytes_per_word ->
            word.unsigned (word.sub stack_hi stack_lo) mod bytes_per_word = 0 ->
            initial.(getPc) = word.add p_funcs (word.of_Z f_rel_pos) ->
            map.get (getRegs initial) RegisterNames.ra = Some ret_addr ->
            word.unsigned ret_addr mod 4 = 0 ->
            map.getmany_of_list initial.(getRegs)
              (List.firstn (List.length argnames) (reg_class.all reg_class.arg)) = Some argvals ->
            initial.(getLog) = t ->
            machine_ok p_funcs stack_lo stack_hi instrs mH Rdata Rexec initial ->
            runsTo initial (fun final : MetricRiscvMachine =>
              exists mH' retvals,
                map.getmany_of_list (getRegs final)
                            (List.firstn (List.length retnames) (reg_class.all reg_class.arg))
                = Some retvals /\
                post final.(getLog) mH' retvals /\
                map.only_differ initial.(getRegs) reg_class.caller_saved final.(getRegs) /\
                final.(getPc) = ret_addr /\
                machine_ok p_funcs stack_lo stack_hi instrs mH' Rdata Rexec final).
    Proof.
      intros.
      pose proof (phase_preserves_post composed_compiler_correct) as C.
      match goal with H: _ |- _ => specialize C with (1 := H) end.
      match goal with H: _ |- _ => specialize C with (1 := H) end.
      unfold Call, SrcLang, RiscvLang, locals_based_call_spec, riscv_call in C.
      edestruct C as (argcount & retcount & f_rel_pos & G & D); clear C. 1: eauto.
      pose proof (phase_preserves_argcount composed_compiler_correct) as AC.
      match goal with H: _ |- _ => specialize AC with (1 := H) end.
      pose proof (phase_preserves_retcount composed_compiler_correct) as RC.
      match goal with H: _ |- _ => specialize RC with (1 := H) end.
      specialize (AC fname). specialize (RC fname).
      unfold GetArgCount, GetRetCount, SrcLang, RiscvLang,
             get_argcount, get_retcount, getFstOfThree, getSndOfThree in *.
      fwd.
      eauto 10.
    Qed.

    Definition instrencode(p: list Instruction): list byte :=
      List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) p.

    Ltac hyp p :=
      multimatch goal with
      | H: context[p] |- _ => H
      end.

    (* combines the above theorem with WeakestPrecondition soundness,
       and makes `map.get finfo fname` a hypothesis rather than conclusion because
       in concrete instantiations, users need to lookup that position themselves anyways *)
    Lemma compiler_correct_wp: forall
        (* input of compilation: *)
        (fs: list (string * (list string * list string * cmd)))
        (* output of compilation: *)
        (instrs: list Instruction) (finfo: string_keyed_map (nat * nat * Z)) (req_stack_size: Z)
        (* function we choose to call: *)
        (fname: string) (argcount retcount: nat) (f_rel_pos: Z)
        (* high-level initial state & post on final state: *)
        (t: trace) (mH: mem) (argvals: list word) (post: trace -> mem -> list word -> Prop)
        (* ghost vars that help describe the low-level machine: *)
        (stack_lo stack_hi ret_addr p_funcs: word) (Rdata Rexec: mem -> Prop)
        (* low-level machine on which we're going to run the compiled program: *)
        (initial: MetricRiscvMachine),
        ExprImp.valid_funs (map.of_list fs) ->
        NoDup (map fst fs) ->
        compile (map.of_list fs) = Success (instrs, finfo, req_stack_size) ->
        WeakestPrecondition.call fs fname t mH argvals post ->
        map.get finfo fname = Some (argcount, retcount, f_rel_pos) ->
        req_stack_size <= word.unsigned (word.sub stack_hi stack_lo) / bytes_per_word ->
        word.unsigned (word.sub stack_hi stack_lo) mod bytes_per_word = 0 ->
        initial.(getPc) = word.add p_funcs (word.of_Z f_rel_pos) ->
        map.get (getRegs initial) RegisterNames.ra = Some ret_addr ->
        word.unsigned ret_addr mod 4 = 0 ->
        map.getmany_of_list initial.(getRegs)
            (List.firstn argcount (reg_class.all reg_class.arg)) = Some argvals ->
        initial.(getLog) = t ->
        machine_ok p_funcs stack_lo stack_hi instrs mH Rdata Rexec initial ->
        runsTo initial (fun final : MetricRiscvMachine =>
          exists mH' retvals,
            map.getmany_of_list (getRegs final)
              (List.firstn retcount (reg_class.all reg_class.arg)) = Some retvals /\
            post final.(getLog) mH' retvals /\
            map.only_differ initial.(getRegs) reg_class.caller_saved final.(getRegs) /\
            final.(getPc) = ret_addr /\
            machine_ok p_funcs stack_lo stack_hi instrs mH' Rdata Rexec final).
    Proof.
      intros.
      let H := hyp WeakestPrecondition.call in rename H into WP.
      eapply WeakestPreconditionProperties.sound_call' in WP.
      2: { eapply map.all_gets_from_map_of_NoDup_list; assumption. }
      fwd.
      edestruct compiler_correct with (argvals := argvals) (post := post) as (f_rel_pos' & G & C);
        try eassumption.
      - intros.
        unfold map.of_list_zip in *. assert (lf = l) by congruence. subst lf.
        apply WPp1p1.
      - replace retcount with (List.length rets) by congruence.
        eapply C; clear C; try assumption; try congruence.
    Qed.

  End WithMoreParams.
End WithWordAndMem.
