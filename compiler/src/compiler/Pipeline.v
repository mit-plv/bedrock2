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
Require Import coqutil.Tactics.Simp.
Require Import compiler.FlattenExprSimulation.
Require Import compiler.Spilling.
Require Import compiler.RegAlloc.
Require Import compiler.FlatToRiscvSimulation.
Require Import compiler.Simulation.
Require Import compiler.RiscvEventLoop.
Require Coq.Init.Byte.
Require Import bedrock2.MetricLogging.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.
Require Import compiler.DivisibleBy4.
Require Export coqutil.Word.SimplWordExpr.
Require Import compiler.ForeverSafe.
Require Import FunctionalExtensionality.
Require Import coqutil.Tactics.autoforward.
Require Import compiler.FitsStack.
Require Import compiler.UpperPipeline.
Require Import compiler.LowerPipeline.
Import Utility.

Existing Instance riscv.Spec.Machine.DefaultRiscvState.

Open Scope Z_scope.

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

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Local Notation source_env := (string_keyed_map (list string * list string * Syntax.cmd)).
  Local Notation flat_env := (string_keyed_map (list string * list string * FlatImp.stmt string)).
  Local Notation renamed_env := (string_keyed_map (list Z * list Z * FlatImp.stmt Z)).

  Definition compile(functions: source_env): option (list Instruction * string_keyed_map Z * Z) :=
    match upper_compiler functions with
    | Some functions' => riscvPhase compile_ext_call functions'
    | None => None
    end.

  Ltac debool :=
    repeat match goal with
           | H: (_ && _)%bool = true |- _ => apply Bool.andb_true_iff in H
           | H: _ /\ _ |- _ => destruct H as [? H]
           | H: _ <? _ = true |- _ => eapply Z.ltb_lt in H
           end.

  Lemma spill_functions_valid_FlatImp_fun: forall funs funs',
      spill_functions funs = Some funs' ->
      (forall f argnames retnames body,
          map.get funs f = Some (argnames, retnames, body) ->
          NoDup argnames /\ NoDup retnames (* other conditions are checked computationally *)) ->
      forall f fun_impl,
      map.get funs' f = Some fun_impl ->
      FlatToRiscvDef.valid_FlatImp_fun fun_impl.
  Proof.
    intros. unfold spill_functions in *.
    eapply map.map_all_values_bw in H. 5: eassumption. all: try typeclasses eauto.
    unfold spill_fun in H. simp.
    unfold FlatToRiscvDef.valid_FlatImp_fun, FlatToRiscvDef.valid_FlatImp_var,
       FlatToRiscvDef.valid_FlatImp_vars, FlatToRiscvDef.stmt_not_too_big,
       FlatToRiscvDef.valid_FlatImp_var, FlatImp.ForallVars_stmt, fp in *.
    debool.
    ssplit.
    - eapply List.forallb_to_Forall. 2: eassumption. cbv beta.
      intros. debool. blia.
    - eapply List.forallb_to_Forall. 2: eassumption. cbv beta.
      intros. debool. blia.
    - pose proof spill_stmt_valid_vars as P.
      unfold valid_vars_src, valid_vars_tgt, sp in P.
      unfold spill_fbody. cbn. split. 1: unfold fp; blia.
      eapply P; clear P. 1: reflexivity.
      eapply max_var_sound.
      eapply FlatImp.forallb_vars_stmt_correct.
      3: eassumption.
      all: cbv beta; intros; rewrite ?Bool.andb_true_iff, ?Z.ltb_lt; unfold fp; blia.
    - specialize H0 with (1 := Hp1). eapply H0.
    - specialize H0 with (1 := Hp1). eapply H0.
    - exact I.
  Qed.

  Lemma regalloc_functions_NoDup: forall funs funs',
      regalloc_functions funs = Some funs' ->
      forall f argnames retnames body,
        map.get funs' f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames.
  Proof.
    unfold regalloc_functions, check_funcs. intros.
    simp.
    eapply map.map_all_values_bw in E. 5: eassumption. 2-4: typeclasses eauto.
    simp.
    eapply map.get_forallb in E0. 2: eassumption.
    unfold lookup_and_check_func, check_func, assert in *. simp.
    autoforward with typeclass_instances in E7. rewrite <- E7.
    autoforward with typeclass_instances in E6. rewrite <- E6.
    split; apply List.NoDup_dedup.
  Qed.

  Lemma flatten_functions_NoDup: forall funs funs',
      (forall f argnames retnames body,
          map.get funs f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames) ->
      flatten_functions funs = Some funs' ->
      forall f argnames retnames body,
        map.get funs' f = Some (argnames, retnames, body) -> NoDup argnames /\ NoDup retnames.
  Proof.
    unfold flatten_functions. intros.
    eapply map.map_all_values_bw in H0. 5: eassumption. 2-4: typeclasses eauto.
    unfold flatten_function in *. simp.
    eapply H. eassumption.
  Qed.

  Lemma compiler_correct: forall
      (stack_start stack_pastend: word)
      (f_entry_name : string) (fbody: Syntax.cmd.cmd) (f_entry_rel_pos: Z)
      (p_call p_functions: word)
      (Rdata Rexec : mem -> Prop)
      (functions: source_env)
      (instrs: list Instruction)
      (pos_map: string_keyed_map Z)
      (mH: mem) (mc: MetricLog)
      (postH: Semantics.trace -> mem -> Prop)
      (required_stack_space: Z)
      (initial: MetricRiscvMachine),
      ExprImp.valid_funs functions ->
      compile functions = Some (instrs, pos_map, required_stack_space) ->
      map.get functions f_entry_name = Some (nil, nil, fbody) ->
      map.get pos_map f_entry_name = Some f_entry_rel_pos ->
      required_stack_space <= word.unsigned (word.sub stack_pastend stack_start) / bytes_per_word ->
      word.unsigned (word.sub stack_pastend stack_start) mod bytes_per_word = 0 ->
      Semantics.exec functions fbody initial.(getLog) mH map.empty mc (fun t' m' l' mc' => postH t' m') ->
      machine_ok p_functions f_entry_rel_pos stack_start stack_pastend instrs
                 p_call p_call mH Rdata Rexec initial ->
      runsTo initial (fun final => exists mH',
          postH final.(getLog) mH' /\
          machine_ok p_functions f_entry_rel_pos stack_start stack_pastend instrs
                     p_call (word.add p_call (word.of_Z 4)) mH' Rdata Rexec final).
  Proof.
    intros. unfold compile in *. simp.
    pose proof upper_compiler_correct as U. unfold phase_correct in U.
    edestruct U as (fbody' & G' & Sim); clear U. 1,2: eassumption.
    eapply flat_to_riscv_correct; try typeclasses eauto; try eassumption.
    { unfold upper_compiler, compose_phases in *. simp.
      eapply spill_functions_valid_FlatImp_fun. 1: eassumption.
      eapply regalloc_functions_NoDup. eassumption. }
    eapply Sim; clear Sim. eassumption.
  Qed.

  Definition instrencode(p: list Instruction): list byte :=
    List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) p.

End Pipeline1.
