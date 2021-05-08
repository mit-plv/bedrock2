Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Export coqutil.Decidable.
Require Import coqutil.Tactics.ParamRecords.
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
    rename_functions prog.

  (* Note: we could also track code size from the source program all the way to the target
     program, and a lot of infrastructure is already there, will do once/if we want to get
     a total compiler.
     Returns the fun_pos_env so that users know where to jump to call the compiled functions. *)
  Definition riscvPhase(ml: MemoryLayout)(prog: renamed_env):
    option (list Instruction * funname_env Z) :=
    bind_opt stack_needed <- stack_usage prog;
    let num_stackwords := word.unsigned (word.sub ml.(stack_pastend) ml.(stack_start)) / bytes_per_word in
    if Z.ltb num_stackwords stack_needed then None (* not enough stack *) else
    let positions := FlatToRiscvDef.build_fun_pos_env prog in
    let '(i, _) := FlatToRiscvDef.compile_funs positions prog in
    Some (i, positions).

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
            (p_functions: word) (* address where the compiled functions are stored *)
            (Rdata Rexec : FlatToRiscvCommon.mem -> Prop)
            (prog: renamed_env)
            (e1 : FlattenExpr.ExprImp_env)
            (e2 : FlattenExpr.FlatImp_env)
            (funname : string)
            (Hf: flatten_functions (2 ^ 10) e1 = Some e2).
    Let c2 := (@FlatImp.SSeq String.string FlatImp.SSkip (FlatImp.SCall [] funname [])).
    Let c3 := (@FlatImp.SSeq Z FlatImp.SSkip (FlatImp.SCall [] f_entry_name [])).
    Context (av' : Z) (r' : string_keyed_map Z)
            (ER: envs_related e2 prog)
            (Ren: rename map.empty c2 lowest_available_impvar = Some (r', c3, av'))
            (H_p_call: word.unsigned p_call mod 4 = 0)
            (H_p_functions: word.unsigned p_functions mod 4 = 0)
            (G: map.get (FlatToRiscvDef.build_fun_pos_env prog) f_entry_name = Some f_entry_rel_pos)
            (F: fits_stack 0 (word.unsigned (word.sub (stack_pastend ml) (stack_start ml)) / bytes_per_word) prog
                           (FlatImp.SSeq FlatImp.SSkip (FlatImp.SCall [] f_entry_name [])))
            (GEI: good_e_impl prog (FlatToRiscvDef.build_fun_pos_env prog)).

    Definition flattenSim: simulation _ _ _ :=
      FlattenExprSimulation.flattenExprSim (2^10) e1 e2 funname Hf.
    Definition regAllocSim: simulation _ _ _ :=
      renameSim (@ext_spec p)
                e2 prog c2 c3 av' r' ER Ren.
    Definition flatToRiscvSim: simulation _ _ _ :=
      FlatToRiscvSimulation.flatToRiscvSim
        f_entry_rel_pos f_entry_name p_call Rdata Rexec
        p_functions ml.(stack_start) ml.(stack_pastend)
        prog compile_ext_call_correct H_p_call H_p_functions G F GEI.

    Definition sim: simulation _ _ _ :=
      (compose_sim flattenSim (compose_sim regAllocSim flatToRiscvSim)).
  End Sim.

  Lemma rename_fun_valid: forall argnames retnames body impl',
      rename_fun (argnames, retnames, body) = Some impl' ->
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
    { eapply dom_bound_empty. }
    simp.
    eapply rename_binds_props in E0; cycle 1.
    { assumption. }
    { assumption. }
    simp.
    pose proof E1 as E1'.
    eapply rename_props in E1; cycle 1.
    { assumption. }
    { assumption. }
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
      + apply Zle_bool_imp_le in E2.
        unfold FlatToRiscvDef.valid_FlatImp_var, lowest_available_impvar, lowest_nonregister in *.
        blia.
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
      + apply Zle_bool_imp_le in E2.
        unfold FlatToRiscvDef.valid_FlatImp_var, lowest_available_impvar, lowest_nonregister in *.
        blia.
      + match goal with
        | X: _ |- _ => specialize X with (1 := A); rename X into B
        end.
        destruct B as [B | B].
        * apply Zle_bool_imp_le in E2.
          unfold FlatToRiscvDef.valid_FlatImp_var, lowest_available_impvar, lowest_nonregister in *.
          blia.
        * rewrite map.get_empty in B. discriminate B.
    - eapply FlatImp.ForallVars_stmt_impl; [|eassumption].
      simpl. intros. simp.
      match goal with
      | X: _ |- _ => specialize X with (1 := H); rename X into A
      end.
      destruct A as [A | A].
      + apply Zle_bool_imp_le in E2.
        unfold FlatToRiscvDef.valid_FlatImp_var, lowest_available_impvar, lowest_nonregister in *.
        blia.
      + match goal with
        | X: _ |- _ => specialize X with (1 := A); rename X into B
        end.
        destruct B as [B | B].
        * apply Zle_bool_imp_le in E2.
          unfold FlatToRiscvDef.valid_FlatImp_var, lowest_available_impvar, lowest_nonregister in *.
          blia.
        * match goal with
          | X: _ |- _ => specialize X with (1 := B); rename X into C
          end.
          destruct C as [C | C].
          -- apply Zle_bool_imp_le in E2.
             unfold FlatToRiscvDef.valid_FlatImp_var, lowest_available_impvar, lowest_nonregister in *.
             blia.
          -- rewrite map.get_empty in C. discriminate C.
    - eapply map.getmany_of_list_injective_NoDup. 3: eassumption. all: eassumption.
    - eapply map.getmany_of_list_injective_NoDup. 3: eassumption. all: eassumption.
    - unfold FlatToRiscvDef.stmt_not_too_big.
      pose proof (rename_preserves_stmt_size _ _ _ _ _ _ E1') as M.
      rewrite <- M.
      assumption.
  Qed.

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

  Local Definition FlatImp__word_eq : FlatImp.word -> FlatImp.word -> bool := word.eqb.
  Local Instance  EqDecider_FlatImp__word_eq : EqDecider FlatImp__word_eq.
  Proof. eapply word.eqb_spec. Unshelve. all: exact word_ok. Qed.

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
  Lemma functions_to_program: forall ml functions_start e instrs pos_map,
      riscvPhase ml e = Some (instrs, pos_map) ->
      iff1 (program iset functions_start instrs)
           (FlatToRiscvCommon.functions functions_start (FlatToRiscvDef.build_fun_pos_env e) e).
  Proof.
    assert nat as H by exact O. (* preserve names *)

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
      apply (f_equal snd) in E1. simpl in E1. rewrite <- E1.
      transitivity (snd (map.fold (FlatToRiscvDef.add_compiled_function map.empty) ([], map.empty) e)).
      - unfold FlatToRiscvDef.build_fun_pos_env, snd. reflexivity.
      - apply build_fun_pos_env_ignores_posmap.
    }
    revert E1.
    revert instrs r. clear E E0 z.
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
    unfold FlatToRiscvDef.add_compiled_function in E1.
    injection E1; clear E1; intros. subst.
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

  Open Scope ilist_scope.

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
      (initial: MetricRiscvMachine),
      ExprImp.valid_funs functions ->
      compile ml functions = Some (instrs, pos_map) ->
      map.get functions f_entry_name = Some (nil, nil, fbody) ->
      map.get pos_map f_entry_name = Some f_entry_rel_pos ->
      Semantics.exec functions fbody initial.(getLog) mH map.empty mc (fun t' m' l' mc' => postH t' m') ->
      machine_ok p_functions f_entry_rel_pos ml.(stack_start) ml.(stack_pastend) instrs
                 p_call p_call mH Rdata Rexec initial ->
      runsTo initial (fun final => exists mH',
          postH final.(getLog) mH' /\
          machine_ok p_functions f_entry_rel_pos ml.(stack_start) ml.(stack_pastend) instrs
                     p_call (word.add p_call (word.of_Z 4)) mH' Rdata Rexec final).
  Proof.
    intros.
    match goal with
    | H: map.get pos_map _ = Some _ |- _ => rename H into GetPos
    end.
    unfold compile, composePhases, renamePhase, flattenPhase in *. simp.
    eapply runsTo_weaken.
    - pose proof sim as P. unfold simulation, ExprImp.SimState, ExprImp.SimExec in P.
      specialize (P ml f_entry_rel_pos f_entry_name p_call p_functions Rdata Rexec).
      specialize P with (e1 := functions) (s1 := (initial.(getLog), mH, map.empty, mc)).
      specialize P with (post1 := fun '(t', m', l', mc') => postH t' m').
      simpl in P.
      eapply P; clear P; cycle -1. {
        econstructor.
        + eassumption.
        + reflexivity.
        + unfold map.of_list_zip, map.putmany_of_list_zip. reflexivity.
        + eassumption.
        + intros. exists nil. split; [reflexivity|].
          exists map.empty. split; [reflexivity|].
          eassumption.
      }
      { eassumption. }
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
      { unfold machine_ok in *. simp. solve_divisibleBy4. }
      { unfold riscvPhase, machine_ok in *. simp.
        eapply program_mod_4_0. 2: ecancel_assumption.
        destruct (map.map_all_values_fw _ _ _ _ E _ _ H1) as [ [ [args' rets'] fbody' ] [ F G ] ].
        unfold flatten_function in F. simp.
        epose proof (map.map_all_values_fw _ _ _ _ E0 _ _ G) as [ [ [args' rets'] fbody' ] [ F G' ] ].
        unfold rename_fun in F. simp.
        eapply compile_funs_nonnil; eassumption.
      }
      { unfold riscvPhase in *. simp. exact GetPos. }
      { simpl. unfold riscvPhase in *. simpl in *. simp.
        move E1 at bottom.
        eapply fits_stack_seq. 1: eapply fits_stack_skip. 1: reflexivity. {
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
        econstructor. 1: reflexivity. 1: eassumption.
        eapply fits_stack_monotone.
        1: eapply stack_usage_correct; eassumption. 1: reflexivity. blia. }
      { unfold good_e_impl.
        intros.
        simpl in *.
        match goal with
        | H: rename_functions _ = _ |- _ => rename H into RenameEq
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
        specialize V with (1 := Pp1).
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
        - unfold FlatToRiscvDef.build_fun_pos_env, FlatToRiscvDef.build_fun_pos_env.
          pose proof (get_compile_funs_pos r0) as P.
          destruct (FlatToRiscvDef.compile_funs map.empty r0) as [ insts posmap ] eqn: F.
          eapply P.
          eassumption.
      }
      unfold related, compose_relation.
      unfold FlatToRiscvSimulation.related, FlattenExprSimulation.related, RegRename.related.
      refine (ex_intro _ (_, _, _, _) _).
      ssplit; try reflexivity.
      refine (ex_intro _ (_, _, _, _) _).
      ssplit; try reflexivity.
      { intros. ssplit; reflexivity. }
      { unfold machine_ok in *. simp. simpl_param_projections. solve_word_eq word_ok. }
      unfold goodMachine. simpl. ssplit.
      { simpl. unfold map.extends. intros k v Emp. rewrite map.get_empty in Emp. discriminate. }
      { simpl. unfold map.extends. intros k v Emp. rewrite map.get_empty in Emp. discriminate. }
      { simpl. unfold machine_ok in *. simp. assumption. }
      { unfold machine_ok in *. simp. assumption. }
      { unfold machine_ok in *. simp. assumption. }
      { unfold machine_ok in *. simp. simpl.
        eapply rearrange_footpr_subset. 1: eassumption.
        (* COQBUG https://github.com/coq/coq/issues/11649 *)
        pose proof (mem_ok: @map.ok (@word (@W p)) Init.Byte.byte (@mem p)).
        wwcancel.
        eapply functions_to_program.
        eassumption. }
      { simpl.
        (* COQBUG https://github.com/coq/coq/issues/11649 *)
        pose proof (mem_ok: @map.ok (@word (@W p)) Init.Byte.byte (@mem p)).
        unfold machine_ok in *. simp.
        edestruct mem_available_to_exists as [ stack_trash [? ?] ]. 1: simpl; ecancel_assumption.
        destruct (byte_list_to_word_list_array stack_trash)
          as (stack_trash_words&Hlength_stack_trash_words&Hstack_trash_words).
        { rewrite H4.
          apply stack_length_divisible.
          assumption. }
        exists stack_trash_words.
        split. 2: {
          unfold word_array.
          rewrite <- (iff1ToEq (Hstack_trash_words _)).
          match goal with
          | E: Z.of_nat _ = word.unsigned (word.sub _ _) |- _ => simpl in E|-*; rewrite <- E
          end.
          lazymatch goal with
          | H: riscvPhase _ _ = _ |- _ => specialize functions_to_program with (1 := H) as P
          end.
          symmetry in P.
          simpl in P|-*. unfold program in P.
          seprewrite P. clear P.
          rewrite <- Z_div_exact_2; cycle 1. {
            unfold bytes_per_word. clear -h.
            destruct width_cases as [E | E]; rewrite E; reflexivity.
          }
          {
            match goal with
            | H: ?x = ?y |- _ => rewrite H
            end.
            apply stack_length_divisible.
            assumption.
          }
          ParamRecords.simpl_param_projections.
          use_sep_assumption.
          unfold ptsto_bytes.
          wseplog_pre.
          simpl_addrs.
          rewrite !word.of_Z_unsigned.
          wcancel.
        }
        match goal with
        | E: Z.of_nat _ = word.unsigned (word.sub _ _) |- _ => simpl in E|-*; rewrite <- E
        end.
        rewrite Z.sub_0_r. symmetry.
        apply Hlength_stack_trash_words. }
      { reflexivity. }
      { unfold machine_ok in *. simp. assumption. }
    - intros. unfold compile_inv, related, compose_relation in *.
      match goal with
      | H: context[machine_ok] |- _ =>
        unfold machine_ok in H;
        repeat match type of H with
               | _ /\ _ => let A := fresh "HOK0" in destruct H as [A H];
                           lazymatch type of A with
                           | verify _ _ => idtac
                           | _ = p_call => idtac
                         (*| _ => clear A*)
                           end
               end
      end.
      subst.
      repeat match goal with
             | H: context[Semantics.exec] |- _ => clear H
             end.
      unfold FlatToRiscvSimulation.related, FlattenExprSimulation.related, RegRename.related, goodMachine in *.
      simp.
      eexists. split. 1: eassumption.
      unfold machine_ok. ssplit; try assumption.
      + cbv [rem_stackwords rem_framewords ghostConsts] in H2p0p1p8p0.
        cbv [mem_available].
        repeat rewrite ?(iff1ToEq (sep_ex1_r _ _)), ?(iff1ToEq (sep_ex1_l _ _)).
        exists (List.flat_map (fun x => HList.tuple.to_list (LittleEndian.split (Z.to_nat bytes_per_word) (word.unsigned x))) stack_trash).
        rewrite !(iff1ToEq (sep_emp_2 _ _ _)).
        rewrite !(iff1ToEq (sep_assoc _ _ _)).
        eapply (sep_emp_l _ _); split.
        { assert (0 < bytes_per_word). { (* TODO: deduplicate *)
            unfold bytes_per_word; simpl; destruct width_cases as [EE | EE]; rewrite EE; cbv; trivial.
          }
          rewrite (length_flat_map _ (Z.to_nat bytes_per_word)).
          { rewrite Nat2Z.inj_mul, Z2Nat.id by blia. rewrite Z.sub_0_r in H2p0p1p8p0.
            rewrite <-H2p0p1p8p0, <-Z_div_exact_2; try trivial.
            { eapply Z.lt_gt; assumption. }
            { eapply stack_length_divisible; trivial. } }
          intros w.
          rewrite HList.tuple.length_to_list; trivial. }
        use_sep_assumption.
        cbn [dframe xframe ghostConsts program_base ghostConsts e_pos e_impl p_insts insts].
        progress simpl (@FlatToRiscvCommon.mem (@FlatToRiscv_params p)).
        wwcancel.
        cancel_seps_at_indices 0%nat 3%nat. {
          reflexivity.
        }
        cancel_seps_at_indices 0%nat 2%nat. {
          cbn [rem_stackwords rem_framewords ghostConsts p_sp].
          replace (word.sub (stack_pastend ml) (word.of_Z (bytes_per_word *
                      (word.unsigned (word.sub (stack_pastend ml) (stack_start ml)) / bytes_per_word))))
            with (stack_start ml). 2: {
            rewrite <- Z_div_exact_2; cycle 1. {
              unfold bytes_per_word. clear -h. simpl.
              destruct width_cases as [E | E]; rewrite E; reflexivity.
            }
            {
              apply stack_length_divisible.
              assumption.
            }
            rewrite word.of_Z_unsigned.
            solve_word_eq word_ok.
          }
          apply iff1ToEq, cast_word_array_to_bytes.
        }
        unfold ptsto_instr.
        simpl.
        unfold ptsto_bytes, ptsto_instr, truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes.
        simpl.
        wwcancel.
        epose proof (functions_to_program ml _ r0 instrs) as P.
        cbn [seps].
        rewrite <- P; clear P.
        * wwcancel. reflexivity.
        * eassumption.
      + unfold machine_ok in *. simp. simpl.
        eapply rearrange_footpr_subset. 1: eassumption.
        (* COQBUG https://github.com/coq/coq/issues/11649 *)
        pose proof (mem_ok: @map.ok (@word (@W p)) Init.Byte.byte (@mem p)).
        (* TODO remove duplication *)
        lazymatch goal with
        | H: riscvPhase _ _ = _ |- _ => specialize functions_to_program with (1 := H) as P
        end.
        symmetry in P.
        rewrite P. clear P.
        cbn [dframe xframe ghostConsts program_base ghostConsts e_pos e_impl p_insts insts program].
        simpl.
        unfold ptsto_bytes, ptsto_instr, truncated_scalar, littleendian, ptsto_bytes.ptsto_bytes.
        simpl.
        wwcancel.
      + destr_RiscvMachine final. subst. solve_divisibleBy4.
    Unshelve.
    all: try exact (bedrock2.MetricLogging.mkMetricLog 0 0 0 0).
    all: try (simpl; typeclasses eauto).
    all: try exact EmptyString.
    all: try exact nil.
    all: try exact map.empty.
    all: try exact mem_ok.
  Qed.

  Definition instrencode(p: list Instruction): list byte :=
    List.flat_map (fun inst => HList.tuple.to_list (LittleEndian.split 4 (encode inst))) p.

End Pipeline1.
