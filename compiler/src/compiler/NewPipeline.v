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
Require Import compiler.RegRename.
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
Require Export compiler.MemoryLayout.
Require Import FunctionalExtensionality.
Require Import coqutil.Tactics.autoforward.
Require Import compiler.FitsStack.
Require Import compiler.UpperPipeline.
Import Utility.

Existing Instance riscv.Spec.Machine.DefaultRiscvState.

Open Scope Z_scope.

Section WithWordAndMem.
  Context {width: Z} {word: word.word width} {mem: map.map word byte}.

  (* bedrock2.ptsto_bytes.ptsto_bytes takes an n-tuple of bytes, whereas this one takes a list of bytes *)
  Definition ptsto_bytes: word -> list byte -> mem -> Prop := array ptsto (word.of_Z 1).

  Definition mem_available(start pastend: word) : mem -> Prop :=
    ex1 (fun anybytes: list byte =>
      emp (Z.of_nat (List.length anybytes) = word.unsigned (word.sub pastend start)) *
      (ptsto_bytes start anybytes))%sep.
End WithWordAndMem.

Module Import Pipeline.

  Class parameters := {
    W :> Words;
    mem :> map.map word byte;
    Registers :> map.map Z word;
    string_keyed_map :> forall T: Type, map.map string T; (* abstract T for better reusability *)
    trace := list (mem * string * list word * (mem * list word));
    ExtSpec := trace -> mem -> string -> list word -> (mem -> list word -> Prop) -> Prop;
    ext_spec : ExtSpec;
    compile_ext_call : string_keyed_map Z -> Z -> Z -> FlatImp.stmt Z -> list Instruction;
    M: Type -> Type;
    MM :> Monad M;
    RVM :> RiscvProgram M word;
    PRParams :> PrimitivesParams M MetricRiscvMachine;
  }.

  Instance FlatToRiscvDef_parameters{p: parameters}: FlatToRiscvDef.FlatToRiscvDef.parameters := {|
    iset := if Utility.width =? 32 then RV32I else RV64I;
    FlatToRiscvDef.FlatToRiscvDef.compile_ext_call := compile_ext_call;
  |}.

  Instance FlattenExpr_parameters{p: parameters}: FlattenExpr.parameters := {
    FlattenExpr.W := _;
    FlattenExpr.locals := _;
    FlattenExpr.mem := mem;
    FlattenExpr.ext_spec := ext_spec;
    FlattenExpr.NGstate := N;
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
    compile_ext_call_correct: forall resvars extcall argvars,
        compiles_FlatToRiscv_correctly
          compile_ext_call (FlatImp.SInteract resvars extcall argvars);
    compile_ext_call_length_ignores_positions: forall stackoffset posmap1 posmap2 c pos1 pos2,
      List.length (compile_ext_call posmap1 pos1 stackoffset c) =
      List.length (compile_ext_call posmap2 pos2 stackoffset c);
  }.

End Pipeline.

Section Pipeline1.

  Context {p: parameters}.
  Context {h: assumptions}.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

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

  Local Notation source_env := (@string_keyed_map p (list string * list string * Syntax.cmd)).
  Local Notation flat_env := (@string_keyed_map p (list string * list string * FlatImp.stmt string)).
  Local Notation renamed_env := (@string_keyed_map p (list Z * list Z * FlatImp.stmt Z)).

  Definition flattenPhase(prog: source_env): option flat_env := flatten_functions (2^10) prog.
  Definition renamePhase(prog: flat_env): option renamed_env :=
    rename_functions_new prog.
  Definition spillingPhase(prog: renamed_env): option renamed_env := spill_functions prog.

  (* Note: we could also track code size from the source program all the way to the target
     program, and a lot of infrastructure is already there, will do once/if we want to get
     a total compiler.
     Returns the fun_pos_env so that users know where to jump to call the compiled functions. *)
  Definition riscvPhase(prog: renamed_env):
    option (list Instruction * funname_env Z * Z) :=
    bind_opt stack_words_needed <- stack_usage prog;
    let positions := FlatToRiscvDef.build_fun_pos_env prog in
    let '(i, _) := FlatToRiscvDef.compile_funs positions prog in
    Some (i, positions, stack_words_needed).

  Definition composePhases{A B C: Type}(phase1: A -> option B)(phase2: B -> option C)(a: A) :=
    match phase1 a with
    | Some b => phase2 b
    | None => None
    end.

  Definition composed_compile: source_env -> option (list Instruction * funname_env Z * Z) :=
    composePhases (composePhases flattenPhase (composePhases renamePhase spillingPhase)) riscvPhase.

  Definition FlatState(varname: Type){pp : FlatImp.parameters varname}: Type :=
    FlatImp.env * FlatImp.stmt varname * bool * FlatImp.trace * FlatImp.mem * FlatImp.locals * MetricLog.

  Definition flatExec{varname: Type}{pp : FlatImp.parameters varname}:
    FlatState varname -> (FlatState varname -> Prop) -> Prop :=
    fun '(e, s, done, t, m, l, mc) post =>
      done = false /\
      FlatImp.exec e s t m l mc (fun t' m' l' mc' => post (e, s, true, t', m', l', mc')).

  (* Note: contrary to GhostConsts, this record only contains risc-v-related types, no FlatImp-related types *)
  Record RiscvFrame: Type := {
    addr_functions: word;
    insts_functions: list Instruction;
    stack_start: word;
    stack_pastend: word;
    xframe: mem -> Prop;
    dframe: mem -> Prop;
  }.

  Definition satisfiesRiscvFrame(f: RiscvFrame)(mH: mem)(mach: MetricRiscvMachine): Prop :=
      (program iset f.(addr_functions) f.(insts_functions) *
       mem_available f.(stack_start) f.(stack_pastend) *
       f.(dframe) * f.(xframe) * eq mH
      )%sep mach.(getMem) /\
      subset (footpr (program iset f.(addr_functions) f.(insts_functions) *
                      f.(xframe))%sep)
             (of_list (getXAddrs mach)) /\
      word.unsigned (mach.(getPc)) mod 4 = 0 /\
      mach.(getNextPc) = word.add mach.(getPc) (word.of_Z 4) /\
      regs_initialized mach.(getRegs) /\
      map.get mach.(getRegs) RegisterNames.sp = Some f.(stack_pastend) /\
      (* configured by PrimitivesParams, can contain invariants needed for external calls *)
      valid_machine mach.

  Local Instance map_ok': @map.ok (@word (@W p)) Init.Byte.byte (@mem p) := mem_ok.

  Lemma get_build_fun_pos_env: forall e f,
      map.get e f <> None ->
      exists pos, map.get (FlatToRiscvDef.build_fun_pos_env e) f = Some pos.
  Proof.
    intros pos0 e.
    unfold FlatToRiscvDef.build_fun_pos_env, FlatToRiscvDef.compile_funs.
    eapply map.fold_spec.
    - intros. rewrite map.get_empty in H. congruence.
    - intros. destruct r as [ insts env]. simpl.
      rewrite map.get_put_dec in H1.
      rewrite map.get_put_dec.
      destruct_one_match; eauto.
  Qed.

  Lemma get_compile_funs_pos: forall e,
      let '(insts, posmap) := FlatToRiscvDef.compile_funs map.empty e in
      forall f impl, map.get e f = Some impl -> exists pos2, map.get posmap f = Some pos2 /\ pos2 mod 4 = 0.
  Proof.
    intros e.
    unfold FlatToRiscvDef.compile_funs.
    eapply map.fold_spec.
    - intros. rewrite map.get_empty in H. congruence.
    - intros. destruct r as [ insts env]. simpl.
      intros.
      rewrite map.get_put_dec in H1.
      rewrite map.get_put_dec.
      destruct_one_match; eauto.
      eexists. split; [reflexivity|].
      solve_divisibleBy4.
  Qed.

  Axiom TODO: False.

  Lemma flatToRiscv_correct: forall functions pos_map stack_words_needed f_entry_name fbody instrs,
      (forall f fun_impl, map.get functions f = Some fun_impl -> FlatToRiscvDef.valid_FlatImp_fun fun_impl) ->
      riscvPhase functions = Some (instrs, pos_map, stack_words_needed) ->
      map.get functions f_entry_name = Some (nil, nil, fbody) ->
      exists f_entry_rel_pos,
        map.get pos_map f_entry_name = Some f_entry_rel_pos /\
        forall initial f mH mc postH retaddr,
          instrs = f.(insts_functions) ->
          satisfiesRiscvFrame f mH initial ->
          initial.(getPc) = word.add f.(addr_functions) (word.of_Z f_entry_rel_pos) ->
          map.get initial.(getRegs) RegisterNames.ra = Some retaddr ->
          (* TODO probably better to execute
             let c := SSeq SSkip (SCall nil f_entry_name nil) in
             instead of fbody because otherwise we need to reprove all of the function's register saving code *)
          FlatImp.exec functions fbody initial.(getLog) mH map.empty mc (fun t' m' l' mc' => postH t' m') ->
          runsTo initial (fun final => exists mH',
            postH final.(getLog) mH' /\
            satisfiesRiscvFrame f mH' initial /\
            final.(getPc) = retaddr).
  Proof.
    unfold riscvPhase. intros. simp.
    edestruct get_build_fun_pos_env as (f_entry_rel_pos & GP). {
      rewrite H1. discriminate.
    }
    eexists. split. 1: exact GP.
    unfold satisfiesRiscvFrame.
    intros. destruct_RiscvMachine initial. simp.
    eapply runsTo_weaken.
    - specialize compile_stmt_correct with (1 := @compile_ext_call_correct _ h).
      unfold compiles_FlatToRiscv_correctly. intros compile_stmt_correct.
      eapply compile_stmt_correct with (g := {| e_pos := (FlatToRiscvDef.build_fun_pos_env functions) |});
        cbn; clear compile_stmt_correct.
      1: eassumption.
      3: eapply stack_usage_correct; eassumption.
      { unfold map.extends. intros *. intro G.
        rewrite map.get_remove_dec in G. destruct_one_match_hyp. 1: discriminate. exact G. }
      { unfold good_e_impl.
        intros *. intro G.
        erewrite @map.get_remove_dec in G. 2,3: cbn; typeclasses eauto.
        destruct_one_match_hyp. 1: discriminate.
        split.
        - eapply H. eassumption.
        - unfold FlatToRiscvDef.build_fun_pos_env, FlatToRiscvDef.build_fun_pos_env.
          pose proof (get_compile_funs_pos functions) as P.
          destruct (FlatToRiscvDef.compile_funs map.empty functions) as [ insts posmap ] eqn: F.
          eapply P.
          eassumption. }
      { reflexivity. }
      { case TODO. (* FlatToRiscvDef.stmt_not_too_big *) }
      { case TODO. (* FlatToRiscvDef.valid_FlatImp_vars fbody *) }
      5: {
        unfold goodMachine. cbn. ssplit.

        (* TODO much more... *)
  Admitted.

  Lemma mem_available_to_exists: forall start pastend (m: mem) P,
      (mem_available start pastend * P)%sep m ->
      exists anybytes,
        Z.of_nat (List.length anybytes) = word.unsigned (word.sub pastend start) /\
        (ptsto_bytes start anybytes * P)%sep m.
  Proof.
    unfold mem_available. intros * H.
    eapply sep_ex1_l in H. (* semicolon here fails *) destruct H.
    eapply sep_assoc in H.
    eapply sep_emp_l in H. destruct H.
    eauto.
  Qed.

  Definition mem_to_available: forall start pastend (m: mem) P anybytes,
     Z.of_nat (List.length anybytes) = word.unsigned (word.sub pastend start) ->
     (ptsto_bytes start anybytes * P)%sep m ->
     (mem_available start pastend * P)%sep m.
  Proof.
    unfold mem_available. intros * H Hsep.
    eapply sep_ex1_l. eexists. eapply sep_assoc. eapply sep_emp_l. eauto.
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
      unfold bytes_per_word, Memory.bytes_per_word.
      destruct width_cases as [E | E]; rewrite E; reflexivity.
  Qed.

  Lemma stack_length_divisible: forall (ml: MemoryLayout) {mlOk: MemoryLayoutOk ml},
    word.unsigned (word.sub (MemoryLayout.stack_pastend ml) (MemoryLayout.stack_start ml)) mod bytes_per_word = 0.
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

  Lemma program_mod_4_0: forall a instrs R m,
      instrs <> [] ->
      (program iset a instrs * R)%sep m ->
      word.unsigned a mod 4 = 0.
  Proof.
    intros.
    destruct instrs as [|instr instrs]. 1: congruence.
    simpl in *.
    unfold sep, ptsto_instr, sep, emp in *.
    simp.
    assumption.
  Qed.

  Lemma compile_funs_nonnil: forall e positions positions' f impl instrs,
      map.get e f = Some impl ->
      FlatToRiscvDef.compile_funs positions e = (instrs, positions') ->
      instrs <> [].
  Proof.
    intros e positions.
    unfold FlatToRiscvDef.compile_funs.
    eapply map.fold_spec; intros.
    - rewrite map.get_empty in H.
      discriminate.
    - rewrite map.get_put_dec in H1.
      destr (k =? f)%string.
      + subst.
        unfold FlatToRiscvDef.add_compiled_function in H2. simp.
        unfold FlatToRiscvDef.compile_function.
        destruct impl as [ [args res] body ].
        intro C. destruct l; discriminate.
      + specialize H0 with (1 := H1).
        destruct r as [ instrs'' positions'' ].
        specialize H0 with (1 := eq_refl).
        intro C. subst instrs.
        unfold FlatToRiscvDef.add_compiled_function in H2. simp.
        unfold FlatToRiscvDef.compile_function in *.
        destruct v as [ [args res] body ].
        destruct instrs''; discriminate.
  Qed.

  Ltac ignore_positions :=
    repeat match goal with
           | |- _ => reflexivity
           | |- _ => rewrite !List.app_length
           | |- _ => solve [eauto]
           | |- _ => progress simpl
           | |- S _ = S _ => f_equal
           | |- (_ + _)%nat = (_ + _)%nat => f_equal
           end.

  Lemma compile_stmt_length_ignores_positions: forall posmap1 posmap2 c stackoffset pos1 pos2,
      List.length (FlatToRiscvDef.compile_stmt posmap1 pos1 stackoffset c) =
      List.length (FlatToRiscvDef.compile_stmt posmap2 pos2 stackoffset c).
  Proof.
    induction c; intros; ignore_positions.
    apply compile_ext_call_length_ignores_positions.
  Qed.

  Lemma compile_function_length_ignores_positions: forall posmap1 posmap2 pos1 pos2 impl,
      List.length (FlatToRiscvDef.compile_function posmap1 pos1 impl) =
      List.length (FlatToRiscvDef.compile_function posmap2 pos2 impl).
  Proof.
    intros. destruct impl as [ [args rets] body ]. ignore_positions.
    apply compile_stmt_length_ignores_positions.
  Qed.

  Lemma build_fun_pos_env_ignores_posmap_aux: forall posmap1 posmap2 e i1 m1 i2 m2,
      map.fold (FlatToRiscvDef.add_compiled_function posmap1) ([], map.empty) e = (i1, m1) ->
      map.fold (FlatToRiscvDef.add_compiled_function posmap2) ([], map.empty) e = (i2, m2) ->
      m1 = m2 /\ List.length i1 = List.length i2.
  Proof.
    intros until e.
    eapply map.fold_parametricity with (fa := (FlatToRiscvDef.add_compiled_function posmap1))
                                       (fb := (FlatToRiscvDef.add_compiled_function posmap2));
      intros.
    - destruct a as [insts1 map1]. destruct b as [insts2 map2].
      unfold FlatToRiscvDef.add_compiled_function in *.
      inversion H0. inversion H1. subst. clear H0 H1.
      specialize H with (1 := eq_refl) (2 := eq_refl). destruct H.
      rewrite ?H0. subst.
      split. 1: reflexivity.
      ignore_positions.
      apply compile_function_length_ignores_positions.
    - inversion H. inversion H0. subst. auto.
  Qed.

  Lemma build_fun_pos_env_ignores_posmap: forall posmap1 posmap2 e,
      snd (map.fold (FlatToRiscvDef.add_compiled_function posmap1) ([], map.empty) e) =
      snd (map.fold (FlatToRiscvDef.add_compiled_function posmap2) ([], map.empty) e).
  Proof.
    intros.
    destr (map.fold (FlatToRiscvDef.add_compiled_function posmap1) ([], map.empty) e).
    destr (map.fold (FlatToRiscvDef.add_compiled_function posmap2) ([], map.empty) e).
    simpl.
    edestruct build_fun_pos_env_ignores_posmap_aux.
    - exact E.
    - exact E0.
    - assumption.
  Qed.

  (* This lemma should relate two map.folds which fold two different f over the same env e:
     1) FlatToRiscvDef.compile_funs, which folds FlatToRiscvDef.add_compiled_function.
        Note that this one is called twice: First in build_fun_pos_env, and then in
        compile_funs, and we rely on the order being the same both times.
     2) functions, which folds sep
     Note that 1) is not commutative (the iteration order determines in which order code
     is layed out in memory), while 2) should be commutative because the "function"
     separation logic predicate it seps onto the separation logic formula is the same
     if we pass it the same function position map. *)
  Lemma functions_to_program: forall functions_start e instrs pos_map stack_size,
      riscvPhase e = Some (instrs, pos_map, stack_size) ->
      iff1 (program iset functions_start instrs)
           (FlatToRiscvCommon.functions functions_start (FlatToRiscvDef.build_fun_pos_env e) e).
  Proof.
    (* PARAMRECORDS *)
    assert (map.ok FlatImp.env). { unfold FlatImp.env. simpl. typeclasses eauto. }
    assert (map.ok mem) as Ok by exact mem_ok.

    unfold riscvPhase.
    intros.
    simp.
    unfold FlatToRiscvDef.compile_funs, functions in *.
    remember (FlatToRiscvDef.build_fun_pos_env e) as positions.
    (* choose your IH carefully! *)
    lazymatch goal with
    | |- ?G => enough ((forall f, map.get r f <> None <-> map.get e f <> None) /\
                       ((forall f pos, map.get r f = Some pos -> map.get positions f = Some pos) -> G))
    end.
    1: {
      destruct H0. apply H1; clear H1.
      intros. rewrite <- H1. f_equal.
      subst.
      apply (f_equal snd) in E0. simpl in E0. rewrite <- E0.
      transitivity (snd (map.fold (FlatToRiscvDef.add_compiled_function map.empty) ([], map.empty) e)).
      - unfold FlatToRiscvDef.build_fun_pos_env, snd. reflexivity.
      - apply build_fun_pos_env_ignores_posmap.
    }
    revert E0.
    revert instrs r. clear E stack_size.
    eapply (map.fold_spec (R:=(list Instruction * _))) with (m:=e); repeat (cbn || simp || intros).
    { rewrite map.fold_empty. intuition try reflexivity.
      - eapply H0. eapply map.get_empty.
      - eapply H0. eapply map.get_empty.
    }
    rewrite map.fold_put; trivial.
    2: { intros.
      eapply functional_extensionality_dep; intros x.
      eapply PropExtensionality.propositional_extensionality; revert x.
      match goal with |- forall x, ?P x <-> ?Q x => change (iff1 P Q) end.
      cancel. }
    case r as (instrs'&r').
    specialize H1 with (1 := eq_refl).
    unfold FlatToRiscvDef.add_compiled_function in E0.
    injection E0; clear E0; intros. subst.
    unfold program in *.
    wseplog_pre.
    destruct H1.
    split. {
      intros. rewrite ?map.get_put_dec.
      destr (k =? f)%string. 2: eauto. intuition discriminate.
    }
    intros.
    rewrite H2. 2: {
      intros.
      eapply H3.
      rewrite map.get_put_dec.
      destr (k =? f)%string. 2: assumption.
      subst. exfalso.
      specialize (H1 f). unfold not in H1. rewrite H0 in H1. rewrite H4 in H1.
      intuition congruence.
    }
    cancel.
    unfold function.
    specialize (H3 k).
    rewrite map.get_put_same in H3.
    specialize H3 with (1 := eq_refl).
    simpl in *. rewrite H3.
    cancel.
    unfold program.
    cancel_seps_at_indices 0%nat 0%nat. 2: reflexivity.
    f_equal.
    f_equal.
    solve_word_eq word_ok.
  Qed.

  Definition machine_ok(p_functions: word)(f_entry_rel_pos: Z)(stack_start stack_pastend: word)
             (finstrs: list Instruction)
             (p_call pc: word)(mH: mem)(Rdata Rexec: mem -> Prop)(mach: MetricRiscvMachine): Prop :=
      let CallInst := Jal RegisterNames.ra
                          (f_entry_rel_pos + word.signed (word.sub p_functions p_call)) : Instruction in
      (program iset p_functions finstrs *
       program iset p_call [CallInst] *
       mem_available stack_start stack_pastend *
       Rdata * Rexec * eq mH
      )%sep mach.(getMem) /\
      subset (footpr (program iset p_functions finstrs *
                      program iset p_call [CallInst] *
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
      (p_call p_functions: word)
      (Rdata Rexec : mem -> Prop)
      (functions: source_env)
      (instrs: list Instruction)
      (pos_map: funname_env Z)
      (mH: mem) (mc: MetricLog)
      (postH: Semantics.trace -> Semantics.mem -> Prop)
      (required_stack_space: Z)
      (initial: MetricRiscvMachine),
      ExprImp.valid_funs functions ->
      composed_compile functions = Some (instrs, pos_map, required_stack_space) ->
      map.get functions f_entry_name = Some (nil, nil, fbody) ->
      map.get pos_map f_entry_name = Some f_entry_rel_pos ->
      Semantics.exec functions fbody initial.(getLog) mH map.empty mc (fun t' m' l' mc' => postH t' m') ->
      machine_ok p_functions f_entry_rel_pos (MemoryLayout.stack_start ml) (MemoryLayout.stack_pastend ml)
                 instrs p_call p_call mH Rdata Rexec initial ->
      runsTo initial (fun final => exists mH',
          postH final.(getLog) mH' /\
          machine_ok p_functions f_entry_rel_pos (MemoryLayout.stack_start ml) (MemoryLayout.stack_pastend ml)
                     instrs p_call (word.add p_call (word.of_Z 4)) mH' Rdata Rexec final).
  Proof.
    intros. unfold composed_compile in *. unfold composePhases at 1 in H0. simp.
    unfold machine_ok in *. simp.
    eapply runsTo_weaken.
    - pose proof flatToRiscv_correct as P. specialize P with (2 := H0).
      pose proof (upper_compiler_correct (Zlocals := locals)) as U. unfold phase_correct in U.
      specialize U with (5 := E) (6 := H1). edestruct U as (fbody2 & G & Uc); clear U.
      1-3: typeclasses eauto. 1: exact ext_spec_ok.
      simp. specialize P with (2 := G). edestruct P as (fr & G' & Q); clear P.
      { case TODO. (* FlatToRiscvDef.valid_FlatImp_fun fun_impl *) }
      rewrite H2 in G'. apply Option.eq_of_eq_Some in G'. subst fr.
      eapply Q with (f := {| addr_functions := p_functions |}); cbn; clear Q.
      + reflexivity.
      + unfold satisfiesRiscvFrame. cbn. case TODO.
      +
  Abort.

  Definition instrencode(p: list Instruction): list byte :=
    List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) p.

End Pipeline1.
