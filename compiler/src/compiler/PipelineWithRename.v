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

Section WithWordAndMem.
  Context {width: Z} {word: word.word width} {mem: map.map word byte}.

  (* bedrock2.ptsto_bytes.ptsto_bytes takes an n-tuple of bytes, whereas this one takes a list of bytes *)
  Definition ptsto_bytes: word -> list byte -> mem -> Prop := array ptsto (word.of_Z 1).

  Definition mem_available(start pastend: word)(m: mem): Prop :=
    exists anybytes: list byte,
      Z.of_nat (List.length anybytes) = word.unsigned (word.sub pastend start) /\
      ptsto_bytes start anybytes m.

  Definition mem_available_to_exists: forall start pastend m P,
      (mem_available start pastend * P)%sep m ->
      exists anybytes,
        Z.of_nat (List.length anybytes) = word.unsigned (word.sub pastend start) /\
        (ptsto_bytes start anybytes * P)%sep m.
  Proof.
    unfold mem_available, sep. simpl.
    intros. simp. eauto 10.
  Qed.
End WithWordAndMem.

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

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

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
  Definition riscvPhase(ml: MemoryLayout)(prog: renamed_env):
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

  Definition compile(ml: MemoryLayout):
    source_env -> option (list Instruction * funname_env Z) :=
    (composePhases flattenPhase
    (composePhases renamePhase
                   (riscvPhase ml))).

  Section Sim.
    Context (ml: MemoryLayout)
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

  Local Axiom TODO_andres: False.

  (* TODO not sure if this is the best definition, if needed, etc *)
  Definition byte_list_to_word_list(bytes: list byte): list word. case TODO_andres. Defined.

  Lemma byte_list_to_word_list_array: forall p bytes,
      iff1 (array ptsto (word.of_Z 1) p bytes)
           (array ptsto_word (word.of_Z bytes_per_word) p (byte_list_to_word_list bytes)).
  Proof.
    case TODO_andres.
  Qed.

  Lemma byte_list_to_word_list_length: forall bytes,
      Z.of_nat (Datatypes.length (byte_list_to_word_list bytes)) =
      Z.of_nat (Datatypes.length bytes) / bytes_per_word.
  Proof.
    case TODO_andres.
  Qed.

  Lemma get_compile_funs_pos: forall pos0 e,
      pos0 mod 4 = 0 ->
      let '(insts, pos1, posmap) := FlatToRiscvDef.compile_funs map.empty pos0 e in
      pos1 mod 4 = 0 /\
      forall f impl, map.get e f = Some impl -> exists pos2, map.get posmap f = Some pos2 /\ pos2 mod 4 = 0.
  Proof.
    intros pos0 e M0.
    unfold FlatToRiscvDef.compile_funs.
    eapply map.fold_spec.
    - intros. split; [assumption|]. intros. rewrite map.get_empty in H. congruence.
    - intros. destruct r as [ [insts pos1] env]. destruct H0. simpl.
      split.
      + solve_divisibleBy4.
      + intros.
        rewrite map.get_put_dec in H2.
        rewrite map.get_put_dec.
        destruct_one_match; eauto.
  Qed.

  Lemma mod_2width_mod_bytes_per_word: forall x,
      (x mod 2 ^ width) mod bytes_per_word = x mod bytes_per_word.
  Proof.
    intros.
    rewrite <- Znumtheory.Zmod_div_mod.
    - reflexivity.
    - unfold bytes_per_word. destruct width_cases as [E | E]; rewrite E; reflexivity.
    - destruct width_cases as [E | E]; rewrite E; reflexivity.
    - unfold Z.divide.
      exists (2 ^ width / bytes_per_word).
      unfold bytes_per_word.
      destruct width_cases as [E | E]; rewrite E; simpl.
      1: change (Z.of_nat (Pos.to_nat 4)) with (2 ^ 2).
      2: change (Z.of_nat (Pos.to_nat 8)) with (2 ^ 3).
      all: rewrite <- Z.pow_sub_r by blia;
           rewrite <- Z.pow_add_r by blia;
           reflexivity.
  Qed.

  Definition instrencode(p: list Instruction): list byte :=
    List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) p.

  Lemma instrencode_functions: forall ml e instrs pos_map,
      riscvPhase ml e = Some (instrs, pos_map) ->
      iff1 (ptsto_bytes (code_start ml) (instrencode instrs))
           (FlatToRiscvFunctions.functions (code_start ml) (FlatToRiscvDef.function_positions e) e).
  Proof.
    unfold riscvPhase.
    intros.
    simp.
    rename z0 into posFinal.
    case TODO_sam.
  Qed.

  Open Scope ilist_scope.

  Definition machine_ok(p_code: word)(f_entry_rel_pos: Z)(stack_start stack_pastend: word)
             (instrs: list Instruction)
             (p_call pc: word)(mH: mem)(Rdata Rexec: mem -> Prop)(mach: MetricRiscvMachine): Prop :=
      let CallInst := Jal RegisterNames.ra
                          (f_entry_rel_pos - word.unsigned (word.sub p_call p_code)) : Instruction in
      verify CallInst iset /\
      (ptsto_bytes p_code (instrencode instrs) *
       ptsto_bytes p_call (instrencode [CallInst]) *
       mem_available stack_start stack_pastend *
       Rdata * Rexec * eq mH
      )%sep mach.(getMem) /\
      subset (footpr (ptsto_bytes p_code (instrencode instrs) *
                      ptsto_bytes p_call (instrencode [CallInst]) *
                      Rexec)%sep)
             (of_list (getXAddrs mach)) /\
      word.unsigned (mach.(getPc)) mod 4 = 0 /\
      mach.(getPc) = pc /\
      mach.(getNextPc) = word.add mach.(getPc) (word.of_Z 4) /\
      regs_initialized mach.(getRegs) /\
      map.get mach.(getRegs) RegisterNames.sp = Some stack_pastend /\
      (* configured by PrimitivesParams, can contain invariants needed for external calls *)
      valid_machine mach.

  (* This lemma translates "sim", which depends on the large definition "related", into something
     more understandable and usable. *)
  Lemma compiler_correct: forall
      (ml: MemoryLayout)
      (mlOk: MemoryLayoutOk ml)
      (f_entry_name : string) (fbody: Syntax.cmd.cmd) (f_entry_rel_pos: Z)
      (p_call: word)
      (Rdata Rexec : mem -> Prop)
      (functions: source_env)
      (instrs: list Instruction)
      (pos_map: funname_env Z)
      (mH: mem) (mc: MetricLog)
      (postH: Semantics.trace -> Semantics.mem -> Prop)
      (initial: MetricRiscvMachine),
      ExprImp.valid_funs functions ->
      compile ml functions = Some (instrs, pos_map) ->
      map.get functions f_entry_name = Some (nil, nil, fbody) ->
      map.get pos_map f_entry_name = Some f_entry_rel_pos ->
      Semantics.exec functions fbody initial.(getLog) mH map.empty mc (fun t' m' l' mc' => postH t' m') ->
      machine_ok ml.(code_start) f_entry_rel_pos ml.(stack_start) ml.(stack_pastend) instrs
                 p_call p_call mH Rdata Rexec initial ->
      runsTo initial (fun final => exists mH',
          postH final.(getLog) mH' /\
          machine_ok ml.(code_start) f_entry_rel_pos ml.(stack_start) ml.(stack_pastend) instrs
                     p_call (word.add p_call (word.of_Z 4)) mH' Rdata Rexec final).
  Proof.
    intros.
    match goal with
    | H: map.get pos_map _ = Some _ |- _ => rename H into GetPos
    end.
    eapply runsTo_weaken.
    - pose proof sim as P. unfold simulation, ExprImp.SimState, ExprImp.SimExec in P.
      specialize (P ml f_entry_rel_pos f_entry_name p_call Rdata Rexec
                    (functions, (Syntax.cmd.call [] f_entry_name []), initial.(getLog), mH, map.empty, mc)).
      specialize P with (post1 := fun '(e', c', t', m', l', mc') => postH t' m').
      simpl in P.
      eapply P; clear P. 2: {
        econstructor.
        + eassumption.
        + reflexivity.
        + unfold map.of_list_zip, map.putmany_of_list_zip. reflexivity.
        + eassumption.
        + intros. exists nil. split; [reflexivity|].
          exists map.empty. split; [reflexivity|].
          eassumption.
      }
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
      { reflexivity. }
      { unfold machine_ok in *. simp. solve_divisibleBy4. }
      { destruct mlOk. assumption. }
      { unfold riscvPhase in *. simp. exact GetPos. }
      { simpl. unfold riscvPhase in *. simpl in *. simp.
        move E1 at bottom.
        eapply fits_stack_seq. 1: eapply fits_stack_skip. {
          eapply Z.div_pos.
          - eapply proj1. eapply word.unsigned_range.
          - clear. unfold bytes_per_word, Memory.bytes_per.
            destruct width_cases as [E | E]; rewrite E; reflexivity.
        }
        destruct (map.map_all_values_fw _ _ _ _ E _ _ H1) as [ [ [args' rets'] fbody' ] [ F G ] ].
        unfold flatten_function in F. simp.
        epose proof (map.map_all_values_fw _ _ _ _ E0 _ _ G) as [ [ [args' rets'] fbody' ] [ F G' ] ].
        unfold rename_fun in F. simp.
        apply_in_hyps rename_binds_preserves_length.
        destruct rets'; [|discriminate].
        destruct args'; [|discriminate].
        repeat match goal with
               | H: _ |- _ => autoforward with typeclass_instances in H
               end.
        econstructor. 1: eassumption.
        eapply fits_stack_monotone. 2: {
          apply Z.sub_le_mono_r.
          eassumption.
        }
        eapply stack_usage_correct; eassumption. }
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
        - unfold FlatToRiscvDef.function_positions, FlatToRiscvDef.build_fun_pos_env.
          pose proof (get_compile_funs_pos 0 r0 eq_refl) as P.
          destruct (FlatToRiscvDef.compile_funs map.empty 0 r0) as [ [ insts pos1 ] posmap ] eqn: F.
          destruct P as [P1 P2].
          eapply P2.
          eassumption.
      }
      { unfold machine_ok in *. simp. assumption. }
      { unfold machine_ok in *. simp.
        (* PARAMRECORDS *) simpl.
        solve_word_eq word_ok. }
      { simpl. unfold map.extends. intros k v Emp. rewrite map.get_empty in Emp. discriminate. }
      { simpl. unfold map.extends. intros k v Emp. rewrite map.get_empty in Emp. discriminate. }
      { simpl. unfold machine_ok in *. simp. assumption. }
      { (* TODO remove duplicate regs_initialized *) unfold machine_ok in *. simp. assumption. }
      { unfold machine_ok in *. simp. assumption. }
      { unfold machine_ok in *. simp. simpl.
        eapply rearrange_footpr_subset. 1: eassumption.
        (* COQBUG https://github.com/coq/coq/issues/11649 *)
        pose proof (mem_ok: @map.ok (@word (@W (@FlatToRiscvDef_params p))) Init.Byte.byte (@mem p)).

        wwcancel.

        case TODO_sam. (* subset footpr xaddrs *) }
      { simpl.
        (* COQBUG https://github.com/coq/coq/issues/11649 *)
        pose proof (mem_ok: @map.ok (@word (@W (@FlatToRiscvDef_params p))) Init.Byte.byte (@mem p)).
        unfold machine_ok in *. simp.
        edestruct mem_available_to_exists as [ stack_trash [? ?] ]. 1: simpl; ecancel_assumption.
        exists (byte_list_to_word_list stack_trash).
        split. 2: {
          unfold word_array.
          rewrite <- (iff1ToEq (byte_list_to_word_list_array _ _)).
          match goal with
          | E: Z.of_nat _ = word.unsigned (word.sub _ _) |- _ => simpl in E|-*; rewrite <- E
          end.
          match goal with
          | H: riscvPhase _ _ = _ |- _ => pose proof (instrencode_functions _ _ _ _ H) as P
          end.
          symmetry in P.
          simpl in P|-*.
          seprewrite P. clear P.
          unfold ptsto_bytes, ptsto_instr, truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes in *.
          assert (word.ok FlatImp.word) by exact word_ok.
          rewrite <- Z_div_exact_2; cycle 1. {
            unfold bytes_per_word. clear -h.
            destruct width_cases as [E | E]; rewrite E; reflexivity.
          }
          {
            match goal with
            | H: ?x = ?y |- _ => rewrite H
            end.
            destruct mlOk.
            rewrite word.unsigned_sub. unfold word.wrap.
            rewrite mod_2width_mod_bytes_per_word.
            rewrite Zminus_mod.
            rewrite stack_start_aligned.
            rewrite stack_pastend_aligned.
            rewrite Z.sub_diag.
            apply Zmod_0_l.
          }
          wcancel_assumption.
          rewrite word.of_Z_unsigned.
          cancel_seps_at_indices O O. {
            (* PARAMRECORDS *) simpl.
            sepclause_eq word_ok.
          }
          cbn [seps].
          simpl.
          rewrite sep_emp_emp.
          match goal with
          | |- iff1 (emp ?P) (emp ?Q) => apply (RunInstruction.iff1_emp P Q)
          end.
          split; intros _; try exact I.
          split; [assumption|reflexivity].
        }
        match goal with
        | E: Z.of_nat _ = word.unsigned (word.sub _ _) |- _ => simpl in E|-*; rewrite <- E
        end.
        apply byte_list_to_word_list_length. }
      { reflexivity. }
      { unfold machine_ok in *. simp. assumption. }
    - intros. unfold compile_inv, related, compose_relation in *.
      eassert (verify _ _). {
        match goal with
        | H: context[machine_ok] |- _ => destruct H
        end.
        eassumption.
      }
      repeat match goal with
             | H: context[machine_ok] |- _ => clear H
             | H: context[Semantics.exec] |- _ => clear H
             end.
      unfold FlatToRiscvSimulation.related, FlattenExprSimulation.related, RegRename.related, goodMachine in *.
      simp.
      eexists. split. 1: eassumption.
      unfold machine_ok. ssplit; try assumption.
      + case TODO_sam. (* separation logic *)
      + case TODO_sam.
      + destr_RiscvMachine final. subst. solve_divisibleBy4.
    Unshelve.
    all: try exact (bedrock2.MetricLogging.mkMetricLog 0 0 0 0).
    all: try (simpl; typeclasses eauto).
    all: try exact EmptyString.
    all: try exact nil.
  Qed.

End Pipeline1.
