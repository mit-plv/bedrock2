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
Require Export compiler.ProgramSpec.
Require Export compiler.MemoryLayout.
Require Import FunctionalExtensionality.
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


(* TODO express flatten_functions in terms of this, or add map_values, or get_dom to the
   map interface *)
Section MapKeys.
  Context {K V1 V2: Type} {M1: map.map K V1} {M2: map.map K V2}.

  Definition map_values(f: V1 -> V2)(m1: M1): list K -> M2 :=
    fix rec keys :=
      match keys with
      | nil => map.empty
      | k :: ks =>
        match map.get m1 k with
        | Some v1 => map.put (rec ks) k (f v1)
        | None => map.empty
        end
      end.

  Context (keqb: K -> K -> bool) {keqb_spec: EqDecider keqb}
          {OK1: map.ok M1} {OK2: map.ok M2}.

  Lemma get_map_values: forall (f: V1 -> V2) (keys: list K) (m1: M1) (k: K) (v1: V1),
      (forall x, In x keys -> map.get m1 x <> None) ->
      In k keys ->
      map.get m1 k = Some v1 ->
      map.get (map_values f m1 keys) k = Some (f v1).
  Proof.
    induction keys; intros.
    - simpl in *. contradiction.
    - simpl in *.
      destruct H0.
      + subst.
        destr (map.get m1 k).
        * rewrite map.get_put_same. congruence.
        * exfalso. eapply H. 2: exact E. auto.
      + destr (map.get m1 a).
        * rewrite map.get_put_dec.
          destr (keqb a k).
          { subst. congruence. }
          { eauto. }
        * exfalso. unfold not in H. eauto.
  Qed.

End MapKeys.


Module Import Pipeline.
  Definition varname := string.

  Class parameters := {
    FlatToRiscvDef_params :> FlatToRiscvDef.FlatToRiscvDef.parameters;

    mem :> map.map word byte;
    locals :> map.map varname word;
    Registers :> map.map Register word;
    funname_env :> forall T: Type, map.map string T; (* abstract T for better reusability *)
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
    FlattenExpr.varname := varname;
    FlattenExpr.varname_eqb := String.eqb;
    FlattenExpr.W := _;
    FlattenExpr.locals := locals;
    FlattenExpr.mem := mem;
    FlattenExpr.ext_spec := ext_spec;
    FlattenExpr.NGstate := string;
  }.

  Instance FlatToRisvc_params{p: parameters}: FlatToRiscvCommon.parameters := {|
    FlatToRiscvCommon.ext_spec := ext_spec;
  |}.

  Class assumptions{p: parameters}: Prop := {
    word_riscv_ok :> RiscvWordProperties.word.riscv_ok word;
    mem_ok :> map.ok mem;
    locals_ok :> map.ok locals;
    funname_env_ok :> forall T, map.ok (funname_env T);
    (* src2imp_ok :> map.ok src2imp; *)
    Registers_ok :> map.ok Registers;
    PR :> MetricPrimitives PRParams;
    FlatToRiscv_hyps :> FlatToRiscvCommon.assumptions;
    ext_spec_ok :> Semantics.ext_spec.ok (FlattenExpr.mk_Semantics_params FlattenExpr_parameters);
  }.

End Pipeline.


Section Pipeline1.

  Context {p: parameters}.
  Context {h: assumptions}.

  Definition funname := string.

  Axiom TODO_sam: False.

  Instance FlattenExpr_hyps: FlattenExpr.assumptions FlattenExpr_parameters := {
    FlattenExpr.locals_ok := locals_ok;
    FlattenExpr.mem_ok := mem_ok;
    FlattenExpr.funname_env_ok := funname_env_ok;
    FlattenExpr.ext_spec_ok := ext_spec_ok;
  }.

  Definition available_registers: list Register :=
    Eval cbv in List.unfoldn Z.succ 29 3.

  Local Notation ExprImpProgram :=
    (@Program (FlattenExpr.mk_Syntax_params _) (@Syntax.cmd (FlattenExpr.mk_Syntax_params _)) _).
  Local Notation FlatImpProgram :=
    (@Program (FlattenExpr.mk_Syntax_params _) (@FlatImp.stmt (FlattenExpr.mk_Syntax_params _)) _).
  Local Notation RenamedProgram :=
    (@Program (mk_Syntax_params (@FlatToRiscvDef_params _))
              (@FlatImp.stmt (mk_Syntax_params (@FlatToRiscvDef_params p)))).

  Local Notation renamed_env :=
    (@funname_env p (list Z * list Z * @FlatImp.stmt (@impparams Z string string))).

  Definition flattenPhase(prog: ExprImpProgram): FlatImpProgram :=
    {| funnames := prog.(funnames);
       funimpls := flatten_functions prog.(funimpls) prog.(funnames);
       init_code := ExprImp2FlatImp prog.(init_code);
       loop_body := ExprImp2FlatImp prog.(loop_body); |}.

  Definition renamePhase(prog: FlatImpProgram): option RenamedProgram :=
    bind_opt funimpls' <- rename_functions String.eqb Z.eqb String.eqb String.eqb
                                           available_registers ext_spec
                                           prog.(funimpls) prog.(funnames);
    bind_opt init_code' <- rename_stmt map.empty prog.(init_code) available_registers;
    bind_opt loop_body' <- rename_stmt map.empty prog.(loop_body) available_registers;
    Some (@Build_Program _ _ renamed_env prog.(funnames) funimpls' init_code' loop_body').

  Definition riscvPhase(init_sp: Z)(prog: RenamedProgram): list Instruction :=
    FlatToRiscvDef.compile_prog prog init_sp.

  Definition compile(init_sp: Z)(prog: ExprImpProgram): option (list Instruction) :=
    let flat := flattenPhase prog in
    bind_opt ren <- renamePhase flat;
    Some (riscvPhase init_sp ren).

  Local Notation cmd := (@Syntax.cmd (FlattenExprDef.FlattenExpr.mk_Syntax_params _)).
  Local Notation env := (@Semantics.env (FlattenExpr.mk_Semantics_params _)).
  Local Notation localsH := (@Semantics.locals (FlattenExpr.mk_Semantics_params _)).
  Local Notation Program := (@Program (FlattenExpr.mk_Syntax_params _)).
  Local Notation ProgramSpec := (@ProgramSpec (FlattenExpr.mk_Semantics_params _)).

  Definition regAllocSim := renameSim String.eqb Z.eqb String.eqb String.eqb
                                      available_registers (@ext_spec p).

  Context (srcprog: Program cmd)
          (spec: ProgramSpec)
          (sat: @ProgramSatisfiesSpec (FlattenExpr.mk_Semantics_params _) _
                                      srcprog Semantics.exec spec)
          (ml: MemoryLayout Semantics.width)
          (mlOk: MemoryLayoutOk ml).

  Hypothesis heap_start_agree: spec.(datamem_start) = ml.(heap_start).
  Hypothesis heap_pastend_agree: spec.(datamem_pastend) = ml.(heap_pastend).

  Lemma get_flatten_functions: forall fname argvars resvars body,
      map.get srcprog.(funimpls) fname = Some (argvars, resvars, body) ->
      map.get (flatten_functions (funimpls srcprog) (funnames srcprog)) fname =
      Some (argvars, resvars, ExprImp2FlatImp body).
  Proof.
    destruct srcprog. destruct sat as [_ M0 _ _]. cbn in *. clear sat.
    assert (M: forall f, In f funnames -> map.get funimpls f <> None). {
      intros. eapply M0. assumption.
    }
    intros.
    assert (G: In fname funnames). {
      intros. eapply M0. congruence.
    }
    clear M0.
    generalize dependent funimpls.
    clear heap_start_agree heap_pastend_agree srcprog spec init_code loop_body ml mlOk.
    revert funnames fname argvars resvars body G.
    induction funnames; intros.
    - simpl in *. contradiction.
    - simpl in *.
      destruct G.
      + subst.
        rewrite map.get_put_same. unfold flatten_function.
        simpl in *. (* PARAMRECORDS *)
        rewrite H.
        reflexivity.
      + destr (map.get funimpls a).
        * rewrite map.get_put_dec.
          destruct_one_match.
          { subst.
            unfold flatten_function.
            simpl in *. (* PARAMRECORDS *)
            rewrite H.
            reflexivity. }
          { eauto. }
        * exfalso. unfold not in M0. eauto.
  Qed.

  Let init_sp := word.unsigned ml.(stack_pastend).

  Definition putProgram(prog: ExprImpProgram)(preInitial: MetricRiscvMachine):
    option MetricRiscvMachine :=
    bind_opt insts <- (compile init_sp prog);
    Some (MetricRiscvMachine.putProgram (List.map encode insts) ml.(code_start) preInitial).

  Let num_stackwords :=
    word.unsigned (word.sub ml.(stack_pastend) ml.(stack_start)) / bytes_per_word.

  Definition hl_inv: @ExprImp.SimState (FlattenExpr.mk_Semantics_params _) -> Prop :=
    fun '(e, c, t, m, l, mc) => spec.(isReady) t m l /\ spec.(goodTrace) t /\
                                (* Restriction: no locals can be shared between loop iterations,
                                   and all locals have to be unset at the end of the loop *)
                                l = map.empty.

  Definition related(g: GhostConsts)(relative_code_pos: Z) :=
    (compose_relation FlattenExprSimulation.related
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

    Definition ll_good(done: bool): MetricRiscvMachine -> Prop :=
      compile_inv (related loopBodyGhostConsts (FlatToRiscvDef.loop_pos prog) done) hl_inv.

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

  Definition ll_inv(m: MetricRiscvMachine): Prop :=
    exists renamed_prog,
      (* technical detail: "pc at beginning of loop" and "pc at end of loop" needs to be
         different so that we can have two disjoint states between which the system goes
         back and forth. If we had only one state, we could not prevent "runsTo" from
         always being runsToDone and not making progress, see compiler.ForeverSafe *)
      0 < 4 * Z.of_nat (List.length (FlatToRiscvDef.loop_insts renamed_prog)) < 2 ^ width /\
      runsToGood_Invariant (ll_good renamed_prog) m.

  Lemma sim(renamed_prog: RenamedProgram)(g: GhostConsts)
        (relative_code_pos: Z):
    FlatToRiscvFunctions.funnames g = funnames srcprog ->
    FlatToRiscvFunctions.program_base g = program_base renamed_prog ->
    simulation ExprImp.SimExec runsTo (related g relative_code_pos).
  Proof.
    intros E1 E2.
    refine (compose_sim FlattenExprSimulation.flattenExprSim
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

  Lemma putProgram_establishes_ll_inv: forall preInitial initial,
      putProgram srcprog preInitial = Some initial ->
      layout preInitial.(getMem) ->
      (* the registers must have some (unspecified) value, ie reading a register must not
         be undefined behavior: *)
      regs_initialized preInitial.(getRegs) ->
      preInitial.(getLog) = [] ->
      ll_inv initial.
  Proof.
    intros.
    unfold putProgram, MetricRiscvMachine.putProgram, RiscvMachine.putProgram.
    unfold ll_inv, runsToGood_Invariant.
    destruct_RiscvMachine preInitial.
    unfold putProgram, compile, renamePhase, flattenPhase in *. simp. simpl in *.
    match goal with
    | |- context [riscvPhase init_sp ?R] => set (ren := R : RenamedProgram)
    end.
    exists ren.
    split.
    1: case TODO_sam.
    (* first, run init_sp_code: *)
    pose proof FlatToRiscvLiterals.compile_lit_correct_full as P.
    cbv zeta in P. (* needed for COQBUG https://github.com/coq/coq/issues/11253 *)
    specialize P with (x := RegisterNames.sp) (v := init_sp).
    unfold runsTo in P. eapply P; clear P; simpl.
    { reflexivity. }
    { case TODO_sam. (* subset footpr XAddrs *) }
    { case TODO_sam. }
    { case TODO_sam. }
    { unfold valid_machine. case TODO_sam. }
    (* then, run init_code (using compiler simulation and correctness of init_code) *)
    simpl.
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
        refine (ex_intro _
           (flatten_functions srcprog.(funimpls) srcprog.(funnames), _, _, _, _, _) _).
        ssplit; try reflexivity.
        { intros. eapply get_flatten_functions. assumption. }
        { unfold map.undef_on, map.agree_on. intros. reflexivity. }
        refine (ex_intro _ (_, _, _, _, _, _) _).
        unfold goodMachine.
        ssplit.
        { unfold envs_related.
          intros f [ [argnames resnames] body1 ] G.
          unfold initCodeGhostConsts, ren. cbn [e_impl funimpls].
          unfold rename_functions in E1.
          eapply map.get_map_all_values in E1.
          6: exact G.
          1: {
            eexists. split.
            (* TODO map.get_map_all_values should ensure E is Some *)
            all: case TODO_sam.
          }
          all: case TODO_sam.
        }
        { reflexivity. }
        { reflexivity. }
        { intros. ssplit; reflexivity. }
        { unfold rename_stmt in E2. simp.
          do 2 eexists. exact E. }
        { reflexivity. }
        { case TODO_sam. (* fits_stack *) }
        { unfold good_e_impl.
          intros.
          case TODO_sam. }
        { unfold FlatToRiscvDef.stmt_not_too_big. case TODO_sam. }
        { case TODO_sam. }
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
        pose proof sat.(init_code_correct) as P.
        unfold ExprImp.SimExec.
        intros.
        specialize (P dmem (mkMetricLog 0 0 0 0)).
        specialize_hyp P. {
          rewrite heap_start_agree, heap_pastend_agree.
          assumption.
        }
        change (
          @Semantics.exec.exec (FlattenExpr.mk_Semantics_params (@FlattenExpr_parameters p))
                               (funimpls srcprog) (init_code srcprog) [] dmem map.empty
                              (mkMetricLog 0 0 0 0)
              (fun (t' : Semantics.trace) (m' : Semantics.mem) (l' : localsH) (mc' : MetricLog) =>
                 (fun '(e', c', t', m', l', mc') =>
                    isReady spec t' m' l' /\ goodTrace spec t' /\ l' = map.empty)
                 (funimpls srcprog, init_code srcprog, t', m', l', mc'))) in P.
        exact P.
    - intros.
      simpl in H.
      destruct H as [ [ [ [ [ [ e c ] t ] mH ] lH ] mcH ] [ A [ B [ C D ] ] ] ].
      subst lH.
      unfold ll_good.
      case TODO_sam.
      (* goal is rhs of runsToGood_Invariant from RiscvEventLoop, can we express this in
         simulation-compatible style? *)
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
    intro st. unfold ll_inv. intros [ ren [? ?] ].
    eapply mcomp_sat_weaken with (post1 := runsToGood_Invariant (ll_good ren)). {
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
      unfold ll_good, compile_inv in *. simp.
      pose proof (sim ren (loopBodyGhostConsts ren) (FlatToRiscvDef.loop_pos ren)) as P.
      unfold simulation, runsTo in P.
      eapply P.
      { case TODO_sam. (* funnames equal *) }
      { reflexivity. }
      { eassumption. }
      clear P.
      unfold ExprImp.SimExec, hl_inv in *. simp.
      pose proof @loop_body_correct as P.
      specialize P with (2 := H1rl).
      eapply P; try eassumption.
      match goal with
      | |- ?G => let T := type of sat in replace G with T; [exact sat|]
      end.
      simpl.
      apply f_equal2; try reflexivity.
      apply f_equal2; try reflexivity.
      (* TODO *)
      repeat let x := fresh in extensionality x.
      replace r1 with H by case TODO_sam.
      replace c with H1 by case TODO_sam.
      replace m with H5 by case TODO_sam.
      reflexivity.
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
    - apply ll_inv_is_invariant.
    - exact ll_inv_implies_prefix_of_good.
  Qed.

End Pipeline1.
