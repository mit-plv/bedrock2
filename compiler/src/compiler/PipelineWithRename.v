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
Require Import riscv.Spec.Decode.
Require Export riscv.Spec.Primitives.
Require Export riscv.Spec.MetricPrimitives.
Require Import compiler.GoFlatToRiscv.
Require Import riscv.Utility.MkMachineWidth.
Require Export riscv.Proofs.DecodeEncode.
Require Export riscv.Proofs.EncodeBound.
Require Export compiler.EmitsValid.
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
Require Coq.Init.Byte.
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
Import Utility.

Existing Instance riscv.Spec.Machine.DefaultRiscvState.

Open Scope Z_scope.

Module List.
  Lemma nth_error_option_all{T: Type}: forall {l1: list (option T)} {l2: list T} (i: nat),
    List.option_all l1 = Some l2 ->
    (i < List.length l1)%nat ->
    exists v, nth_error l2 i = Some v.
  Proof.
    induction l1; intros.
    - simpl in *. exfalso. inversion H0.
    - simpl in *. simp.
      destruct i as [|j].
      + simpl. eauto.
      + simpl. assert (j < List.length l1)%nat as D by blia. eauto.
  Qed.

  Lemma In_option_all{T: Type}: forall {l1: list (option T)} {l2: list T} {v1o: option T},
    List.option_all l1 = Some l2 ->
    List.In v1o l1 ->
    exists v1, v1o = Some v1 /\ List.In v1 l2.
  Proof.
    induction l1; intros.
    - simpl in *. contradiction.
    - simpl in *. simp. destruct H0.
      + subst. simpl. eauto.
      + simpl. firstorder idtac.
  Qed.

  (* same as nodup from standard library but using BoolSpec instead of sumbool *)
  Definition dedup{A: Type}(aeqb: A -> A -> bool){aeqb_spec: EqDecider aeqb}: list A -> list A :=
    fix rec l :=
      match l with
      | [] => []
      | x :: xs => if List.find (aeqb x) xs then rec xs else x :: rec xs
      end.

  Lemma dedup_preserves_In{A: Type}(aeqb: A -> A -> bool){aeqb_spec: EqDecider aeqb}(l: list A) a:
    In a l <-> In a (dedup aeqb l).
  Proof.
    induction l.
    - simpl. firstorder idtac.
    - simpl. split; intro H.
      + destruct H.
        * subst. destruct_one_match.
          { apply find_some in E. destruct E as [E1 E2].
            destr (aeqb a a0). 2: discriminate. subst a0. firstorder idtac. }
          { simpl. auto. }
        * destruct_one_match.
          { apply find_some in E. destruct E as [E1 E2].
            destr (aeqb a0 a1). 2: discriminate. subst a0. firstorder idtac. }
          { simpl. firstorder idtac. }
      + destruct_one_match_hyp.
        * apply find_some in E. destruct E as [E1 E2].
          destr (aeqb a0 a1). 2: discriminate. subst a0. firstorder idtac.
        * simpl in H. destruct H.
          { subst. auto. }
          { firstorder idtac. }
  Qed.

  Lemma NoDup_dedup{A: Type}(aeqb: A -> A -> bool){aeqb_spec: EqDecider aeqb}: forall (l: list A),
      NoDup (dedup aeqb l).
  Proof.
    induction l.
    - simpl. constructor.
    - simpl. destruct_one_match.
      + assumption.
      + constructor. 2: assumption.
        intro C.
        apply dedup_preserves_In in C.
        pose proof (find_none _ _ E _ C).
        destr (aeqb a a); congruence.
  Qed.

End List.

Module map. Section map.
  Context {K V1 V2 : Type}{M1 : map.map K V1}{M2 : map.map K V2}(keqb : K -> K -> bool).
  Context {keqb_spec: EqDecider keqb} {ok1: map.ok M1} {ok2: map.ok M2}.
  Lemma map_all_values_not_None_fw: forall (f : V1 -> option V2) (m1 : M1) (m2 : M2) (k: K),
      map.map_all_values f m1 = Some m2 ->
      map.get m1 k <> None ->
      map.get m2 k <> None.
  Proof.
    intros f m1.
    unfold map.map_all_values.
    eapply map.fold_spec.
    - intros. simp. exfalso. rewrite map.get_empty in H0. congruence.
    - intros. simp. rewrite map.get_put_dec. rewrite map.get_put_dec in H2.
      destruct_one_match.
      + congruence.
      + eauto.
  Qed.
End map. End map.

Module Import Pipeline.

  Class parameters := {
    FlatToRiscvDef_params :> FlatToRiscvDef.FlatToRiscvDef.parameters;

    mem :> map.map word byte;
    Registers :> map.map Z word;
    string_keyed_map :> forall T: Type, map.map string T; (* abstract T for better reusability *)
    trace := list (mem * string * list word * (mem * list word));
    ExtSpec := trace -> mem -> string -> list word -> (mem -> list word -> Prop) -> Prop;
    ext_spec : ExtSpec;

    (* Note: this one is not needed because it's subsumed by funname_env,
       and if we do add it, type class inference will infer funname_env in one place
       and src2imp in another and then terms which should be convertible arent'
    src2imp :> map.map string Z; *)

    M: Type -> Type;
    MM :> Monad M;
    RVM :> RiscvProgram M word;
    PRParams :> PrimitivesParams M MetricRiscvMachine;
  }.

  Instance FlattenExpr_parameters{p: parameters}: FlattenExpr.parameters := {
    FlattenExpr.W := _;
    FlattenExpr.locals := _;
    FlattenExpr.mem := mem;
    FlattenExpr.ext_spec := ext_spec;
    FlattenExpr.NGstate := string;
  }.

  Instance FlatToRiscv_params{p: parameters}: FlatToRiscvCommon.parameters := {|
    FlatToRiscvCommon.ext_spec := ext_spec;
  |}.

  Class assumptions{p: parameters}: Prop := {
    word_riscv_ok :> RiscvWordProperties.word.riscv_ok word;
    string_keyed_map_ok :> forall T, map.ok (string_keyed_map T);
    Registers_ok :> map.ok Registers;
    PR :> MetricPrimitives PRParams;
    FlatToRiscv_hyps :> FlatToRiscvCommon.assumptions;
    ext_spec_ok :> Semantics.ext_spec.ok (FlattenExpr.mk_Semantics_params FlattenExpr_parameters);
  }.

End Pipeline.


Section Pipeline1.

  Context {p: parameters}.
  Context {h: assumptions}.

  Local Axiom TODO_sam: False.

  Instance mk_FlatImp_ext_spec_ok:
    FlatImp.ext_spec.ok  string (FlattenExpr.mk_FlatImp_params FlattenExpr_parameters).
  Proof.
    destruct h. destruct ext_spec_ok0.
    constructor.
    all: intros; eauto.
    eapply intersect; eassumption.
  Qed.

  Instance FlattenExpr_hyps: FlattenExpr.assumptions FlattenExpr_parameters.
  Proof.
    constructor.
    - apply (string_keyed_map_ok (p := p) (@word (@FlattenExpr.W (@FlattenExpr_parameters p)))).
    - exact mem_ok.
    - apply (string_keyed_map_ok (p := p) (list string * list string * Syntax.cmd.cmd)).
    - apply (string_keyed_map_ok (p := p) (list string * list string * FlatImp.stmt string)).
    - apply mk_FlatImp_ext_spec_ok.
  Qed.

  Definition available_registers: list Z :=
    Eval cbv in List.unfoldn Z.succ 29 3.

  Lemma NoDup_available_registers: NoDup available_registers.
  Proof. cbv. repeat constructor; cbv; intros; intuition congruence. Qed.

  Lemma valid_FlatImp_vars_available_registers: Forall FlatToRiscvDef.valid_FlatImp_var available_registers.
  Proof. repeat constructor; cbv; intros; discriminate. Qed.

  Local Notation source_env := (@string_keyed_map p (list string * list string * Syntax.cmd)).
  Local Notation flat_env := (@string_keyed_map p (list string * list string * FlatImp.stmt string)).
  Local Notation renamed_env := (@string_keyed_map p (list Z * list Z * FlatImp.stmt Z)).

  Definition flattenPhase(prog: source_env): option flat_env := flatten_functions (2^10) prog.
  Definition renamePhase(prog: flat_env): option renamed_env :=
    rename_functions available_registers prog.

  (* Note: we could also track code size from the source program all the way to the target
     program, and a lot of infrastructure is already there, will do once/if we want to get
     a total compiler.
     Returns the fun_pos_env so that users know where to jump to call the compiled functions. *)
  Definition riscvPhase(ml: MemoryLayout Semantics.width)(prog: renamed_env):
    option (list Instruction * funname_env Z) :=
    bind_opt stack_needed <- stack_usage prog;
    let num_stackwords := word.unsigned (word.sub ml.(stack_pastend) ml.(stack_start)) / bytes_per_word in
    if Z.ltb num_stackwords stack_needed then None (* not enough stack *) else
    let positions := FlatToRiscvDef.function_positions prog in
    let '(i, _, _) := FlatToRiscvDef.compile_funs positions 0 prog in
    let maxSize := word.unsigned ml.(code_pastend) - word.unsigned ml.(code_start) in
    if 4 * Z.of_nat (List.length i) <=? maxSize then Some (i, positions) else None.

  Definition composePhases{A B C: Type}(phase1: A -> option B)(phase2: B -> option C)(a: A) :=
    match phase1 a with
    | Some b => phase2 b
    | None => None
    end.

  Definition compile(ml: MemoryLayout Semantics.width):
    source_env -> option (list Instruction * funname_env Z) :=
    (composePhases flattenPhase
    (composePhases renamePhase
                   (riscvPhase ml))).

  Section Sim.
    Context (ml: MemoryLayout Semantics.width)
            (mlOk: MemoryLayoutOk ml)
            (f_entry_rel_pos : Z)
            (f_entry_name : string)
            (p_call: word) (* address where the call to the entry function is stored *)
            (Rdata Rexec : FlatToRiscvCommon.mem -> Prop).

    Definition related :=
      (compose_relation (FlattenExprSimulation.related (2^10))
      (compose_relation (RegRename.related available_registers ext_spec)
                        (FlatToRiscvSimulation.related f_entry_rel_pos f_entry_name p_call Rdata Rexec
                                                       ml.(code_start) ml.(stack_start) ml.(stack_pastend)))).

    Definition flattenSim := FlattenExprSimulation.flattenExprSim (2^10).
    Definition regAllocSim := renameSim available_registers (@ext_spec p) NoDup_available_registers.
    Definition flatToRiscvSim := FlatToRiscvSimulation.flatToRiscvSim
                                   f_entry_rel_pos f_entry_name p_call Rdata Rexec
                                   ml.(code_start) ml.(stack_start) ml.(stack_pastend).

    Lemma sim: simulation ExprImp.SimExec runsTo related.
    Proof. exact (compose_sim flattenSim (compose_sim regAllocSim flatToRiscvSim)). Qed.
  End Sim.

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
    { eapply map.empty_injective. }
    { eapply map.not_in_range_empty. }
    { apply NoDup_available_registers. }
    simp.
    eapply rename_binds_props in E0; cycle 1.
    { assumption. }
    { assumption. }
    { pose proof NoDup_available_registers as P.
      replace available_registers with (used ++ l) in P by assumption.
      apply invert_NoDup_app in P. tauto. }
    simp.
    pose proof E1 as E1'.
    eapply rename_props in E1; cycle 1.
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
      rewrite <- M.
      assumption.
  Qed.

  Lemma get_build_fun_pos_env: forall pos0 e f,
      map.get e f <> None ->
      exists pos, map.get (FlatToRiscvDef.build_fun_pos_env pos0 e) f = Some pos.
  Proof.
    intros pos0 e.
    unfold FlatToRiscvDef.build_fun_pos_env, FlatToRiscvDef.compile_funs.
    eapply map.fold_spec.
    - intros. rewrite map.get_empty in H. congruence.
    - intros. destruct r as [ [insts pos1] env]. simpl.
      rewrite map.get_put_dec in H1.
      rewrite map.get_put_dec.
      destruct_one_match; eauto.
  Qed.

  Definition instrencode(p: list Instruction): list byte :=
    List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) p.

  Definition ptsto_bytes: word -> list byte -> mem -> Prop := array ptsto (word.of_Z 1).

  Open Scope ilist_scope.

  Definition machine_ok(p_code p_stack_pastend: word)(instrs: list Instruction)(p_call pc: word)
             (mH: mem)(Rdata Rexec: mem -> Prop)(mach: MetricRiscvMachine): Prop :=
      (ptsto_bytes p_code (instrencode instrs) *
       ptsto_bytes p_call (instrencode [[
           Jal RegisterNames.ra (word.unsigned (word.sub p_code p_call))]]) *
       Rdata * Rexec * eq mH
      )%sep mach.(getMem) /\
      mach.(getPc) = pc /\
      mach.(getNextPc) = word.add mach.(getPc) (word.of_Z 4) /\
      regs_initialized mach.(getRegs) /\
      map.get mach.(getRegs) RegisterNames.sp = Some p_stack_pastend /\
      (* configured by PrimitivesParams, can contain invariants needed for external calls *)
      valid_machine mach.

  (* This lemma translates "sim", which depends on the large definition "related", into something
     more understandable and usable. *)
  Lemma compiler_correct: forall
      (ml: MemoryLayout Semantics.width)
      (mlOk: MemoryLayoutOk ml)
      (f_entry_name : string)
      (p_call: word)
      (Rdata Rexec : mem -> Prop)
      (functions: source_env)
      (instrs: list Instruction)
      (pos_map: funname_env Z)
      (mH: mem) (mc: MetricLog)
      (postH: Semantics.trace -> Semantics.mem -> Semantics.locals -> MetricLog -> Prop)
      (initial: MetricRiscvMachine),
      ExprImp.valid_funs functions ->
      compile ml functions = Some (instrs, pos_map) ->
      Semantics.exec functions (Syntax.cmd.call nil f_entry_name nil) initial.(getLog) mH map.empty mc postH ->
      machine_ok ml.(code_start) ml.(stack_pastend) instrs
                 p_call p_call mH Rdata Rexec initial ->
      runsTo initial (fun final => exists mH' lH' mcH',
          postH final.(getLog) mH' lH' mcH' /\
          machine_ok ml.(code_start) ml.(stack_pastend) instrs
                     p_call (word.add p_call (word.of_Z 4)) mH' Rdata Rexec final).
  Proof.
    intros.
    assert (exists f_entry_rel_pos, map.get pos_map f_entry_name = Some f_entry_rel_pos) as GetPos. {
      unfold compile, composePhases, renamePhase, flattenPhase, riscvPhase in *. simp.
      unfold flatten_functions, rename_functions, FlatToRiscvDef.function_positions in *.
      apply get_build_fun_pos_env.
      eapply (map.map_all_values_not_None_fw _ _ _ _ _ E0).
      eapply (map.map_all_values_not_None_fw _ _ _ _ _ E).
      simpl in *. (* PARAMRECORDS *)
      congruence.
    }
    destruct GetPos as [f_entry_rel_pos GetPos].
    eapply runsTo_weaken.
    - pose proof sim as P. unfold simulation, ExprImp.SimState, ExprImp.SimExec in P.
      specialize (P ml f_entry_rel_pos f_entry_name p_call Rdata Rexec
                    (functions, (Syntax.cmd.call [] f_entry_name []), initial.(getLog), mH, map.empty, mc)).
      specialize P with (post1 := fun '(e', c', t', m', l', mc') => postH t' m' l' mc').
      simpl in P.
      eapply P; clear P. 2: eassumption.
      unfold compile, composePhases, renamePhase, flattenPhase in *. simp.
      unfold related, compose_relation.
      unfold FlatToRiscvSimulation.related, FlattenExprSimulation.related, RegRename.related.
      refine (ex_intro _ (_, _, _, _, _, _) _).
      ssplit; try reflexivity.
      { eassumption. }
      { eexists. split; reflexivity. }
      refine (ex_intro _ (_, _, _, _, _, _) _).
      unfold goodMachine.
      ssplit.
      { unfold envs_related.
        intros f [ [argnames resnames] body1 ] G.
        unfold rename_functions in *.
        eapply map.map_all_values_fw.
        5: exact G. 4: eassumption.
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
      { unfold riscvPhase in *. simp. exact GetPos. }
      { simpl. unfold riscvPhase in *. simpl in *. simp.
        case TODO_sam. (* stack usage *) }
      { unfold good_e_impl.
        intros.
        simpl in *.
        match goal with
        | H: rename_functions _ _ = _ |- _ => rename H into RenameEq
        end.
        unfold rename_functions in RenameEq.
        match goal with
        | H: _ |- _ => unshelve epose proof (map.map_all_values_bw _ _ _ _ RenameEq _ _ H)
        end.
        simp. destruct v1 as [ [argnames' retnames'] body' ].
        match goal with
        | H: flatten_functions _ _ = _ |- _ => rename H into FlattenEq
        end.
        unfold flatten_functions in FlattenEq.
        match goal with
        | H: _ |- _ => unshelve epose proof (map.map_all_values_bw _ _ _ _ FlattenEq _ _ H) as P
        end.
        unfold flatten_function in P.
        simp.
        match goal with
        | H: ExprImp.valid_funs _ |- _ => rename H into V
        end.
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
        - case TODO_sam. (* function_positions contains f *)
      }
      { unfold machine_ok in *. simp. assumption. }
      { unfold machine_ok in *. simp. solve_word_eq word_ok. }
      { simpl. unfold map.extends. intros k v Emp. rewrite map.get_empty in Emp. discriminate. }
      { simpl. unfold map.extends. intros k v Emp. rewrite map.get_empty in Emp. discriminate. }
      { simpl. unfold machine_ok in *. simp. assumption. }
      { (* TODO remove duplicate regs_initialized *) unfold machine_ok in *. simp. assumption. }
      { unfold machine_ok in *. simp. assumption. }
      { simpl. case TODO_sam. (* subset footpr xaddrs *) }
      { simpl. case TODO_sam. (* separation logic descrption of initial memory *) }
      { reflexivity. }
      { unfold machine_ok in *. simp. assumption. }
    - intros. unfold compile_inv, related, compose_relation in *.
      repeat match goal with
             | H: context[machine_ok] |- _ => clear H
             | H: context[Semantics.exec] |- _ => clear H
             end.
      unfold FlatToRiscvSimulation.related, FlattenExprSimulation.related, RegRename.related, goodMachine in *.
      simp.
      do 3 eexists. split. 1: eassumption.
      unfold machine_ok. ssplit; try assumption.
      case TODO_sam. (* separation logic *)
    Unshelve. exact (bedrock2.MetricLogging.mkMetricLog 0 0 0 0).
  Qed.

End Pipeline1.
