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
Import Utility.

Existing Instance riscv.Spec.Machine.DefaultRiscvState.

Open Scope Z_scope.


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

    src2imp :> map.map string Z;

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
    mem_ok :> map.ok mem;
    locals_ok :> map.ok locals;
    funname_env_ok :> forall T, map.ok (funname_env T);
    src2imp_ok :> map.ok src2imp;
    Registers_ok :> map.ok Registers;
    PR :> MetricPrimitives PRParams;
    FlatToRiscv_hyps :> FlatToRiscvCommon.assumptions;
    ext_spec_ok :> Semantics.ext_spec.ok _;
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
    FlattenExpr.ext_spec_ok := match TODO_sam with end;
  }.

  Instance word_riscv_ok: RiscvWordProperties.word.riscv_ok word. case TODO_sam. Defined.

  Definition available_registers: list Register :=
    Eval cbv in List.unfoldn Z.succ 29 3.

  Local Notation cmd := (@Syntax.cmd (FlattenExprDef.FlattenExpr.mk_Syntax_params _)).
  Local Notation env := (@Semantics.env (FlattenExpr.mk_Semantics_params _)).
  Local Notation localsH := (@Semantics.locals (FlattenExpr.mk_Semantics_params _)).
  Local Notation Program := (@Program (FlattenExpr.mk_Semantics_params _)).
  Local Notation ProgramSpec := (@ProgramSpec (FlattenExpr.mk_Semantics_params _)).

  Definition ExprImp2RenamedFlat(s: cmd): FlatImp.stmt :=
    let flat := ExprImp2FlatImp s in rename_stmt map.empty flat available_registers.

  Notation fun_pos_env := (@funname_env p Z).

  Definition snippet2Riscv(e_pos: fun_pos_env)(mypos: Z)(s: cmd): list Instruction :=
    let flat := ExprImp2RenamedFlat s in
    FlatToRiscvDef.compile_snippet e_pos mypos flat.

  Definition regAllocSim := renameSim String.eqb Z.eqb String.eqb String.eqb
                                      available_registers (@ext_spec p).

  Context (prog: Program cmd)
          (spec: ProgramSpec)
          (sat: ProgramSatisfiesSpec prog Semantics.exec spec)
          (ml: MemoryLayout Semantics.width)
          (mlOk: MemoryLayoutOk ml).

  (* TODO reduce duplication between FlatToRiscvDef *)

  (* All code as renamed FlatImp, layed out like it will be layed out in riscv: *)
  (* 1)    set up stack ptr: not in FlatImp *)
  (* 2) *) Let init_code' := ExprImp2RenamedFlat prog.(init_code).
  (* 3) *) Let loop_body' := ExprImp2RenamedFlat prog.(loop_body).
  (* 4)    jump back to loop body: not in FlatImp *)
  (* 5) *) Let functions' := let e' := flatten_functions prog.(funimpls) prog.(funnames) in
                             rename_functions String.eqb Z.eqb String.eqb String.eqb
                                              available_registers ext_spec
                                              e' prog.(funnames).

  (* we make this one a Definition because it's useful for debugging *)
  Definition function_positions: fun_pos_env :=
    FlatToRiscvDef.build_fun_pos_env functions' 0 prog.(funnames).

  Let main_size := List.length (FlatToRiscvDef.compile_main
                                  function_positions 42 init_code' loop_body').

  (* All code as riscv machine code, layed out from low to high addresses: *)
  (* 1) *) Let init_sp_insts := let init_sp := word.unsigned ml.(stack_pastend) in
                                FlatToRiscvDef.compile_lit RegisterNames.sp init_sp.
  (* 2) *) Let init_insts := let main_pos := - 4 * Z.of_nat main_size in
                       FlatToRiscvDef.compile_stmt_new function_positions main_pos init_code'.
           Let loop_pos := let main_pos := - 4 * Z.of_nat main_size in
                           main_pos + 4 * Z.of_nat (Datatypes.length init_insts).
  (* 3) *) Let loop_insts := FlatToRiscvDef.compile_stmt_new
                function_positions loop_pos loop_body'.
  (* 4) *) Let backjump_insts := [IInstruction
                             (Jal Register0 (-4 * Z.of_nat (Datatypes.length loop_insts)))].
  (* 5) *) Let fun_insts := FlatToRiscvDef.compile_funs
                               function_positions functions' 0 prog.(funnames).

  Definition compile_prog: list Instruction :=
    init_sp_insts ++ init_insts ++ loop_insts ++ backjump_insts ++ fun_insts.

  Lemma main_size_correct:
    main_size = (Datatypes.length init_insts + Datatypes.length loop_insts + 1)%nat.
  Proof.
    unfold main_size, init_insts, loop_insts, FlatToRiscvDef.compile_main.
    rewrite !app_length. simpl.
    repeat lazymatch goal with
    | |- ?L = ?R =>
      match L with
      | context[?LL] =>
        lazymatch LL with
        | Datatypes.length (FlatToRiscvDef.compile_stmt_new _ ?pos1 ?C) =>
          match R with
          | context[?RR] =>
            lazymatch RR with
            | Datatypes.length (FlatToRiscvDef.compile_stmt_new _ ?pos2 C) =>
              progress replace LL with RR by refine (compile_stmt_length_position_indep _ _ _ _ _)
            end
          end
        end
      end
    end.
    blia.
  Qed.

  Definition putProgram(preInitial: MetricRiscvMachine): MetricRiscvMachine :=
    MetricRiscvMachine.putProgram (List.map encode compile_prog) ml.(code_start) preInitial.

  (* pc at beginning of loop *)
  Definition pc_start: word := word.add ml.(code_start)
    (word.of_Z (4 * Z.of_nat (List.length init_sp_insts + List.length init_insts))).

  Definition TODO_frame: mem -> Prop. case TODO_sam. Qed.
  (* don't unfold and count many times *)

  Definition loopBodyGhostConsts: GhostConsts.
  refine ({|
    FlatToRiscvFunctions.p_sp := ml.(stack_pastend);
    FlatToRiscvFunctions.num_stackwords :=
      word.unsigned (word.sub ml.(stack_pastend) ml.(stack_start)) / bytes_per_word;
    FlatToRiscvFunctions.p_insts := pc_start;
    FlatToRiscvFunctions.insts := loop_insts;
    (* function positions in e_pos are relative to program_base *)
    FlatToRiscvFunctions.program_base := word.add ml.(code_start)
      (word.of_Z (4 * Z.of_nat (List.length init_sp_insts +
                                List.length init_insts +
                                List.length loop_insts +
                                List.length backjump_insts)));
    FlatToRiscvFunctions.e_pos := function_positions;
    FlatToRiscvFunctions.e_impl := functions';
    FlatToRiscvFunctions.funnames := prog.(funnames);
    FlatToRiscvFunctions.dframe := TODO_frame;
    FlatToRiscvFunctions.xframe := TODO_frame;
  |}).
  Defined.

  Definition loopBody_related :=
    (compose_relation FlattenExprSimulation.related
    (compose_relation (RegRename.related eqb Z.eqb eqb eqb available_registers ext_spec)
                      (FlatToRiscvSimulation.related loopBodyGhostConsts loop_pos))).

  Lemma loopBodySim: simulation ExprImp.SimExec runsTo loopBody_related.
  Proof.
    refine (compose_sim FlattenExprSimulation.flattenExprSim
           (compose_sim _
                        (FlatToRiscvSimulation.flatToRiscvSim loopBodyGhostConsts loop_pos _ _))).
    1: eapply renameSim; try typeclasses eauto.
    - repeat constructor; simpl; blia.
    - eapply (funnames_NoDup sat).
    - simpl. destruct mlOk. solve_divisibleBy4.
  Qed.

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Definition hl_inv: @ExprImp.SimState (FlattenExpr.mk_Semantics_params _) -> Prop :=
    fun '(e, c, done, t, m, l) => spec.(isReady) t m l /\ spec.(goodTrace) t /\
                                  (* Restriction: no locals can be shared between loop iterations,
                                     and all locals have to be unset at the end of the loop *)
                                  l = map.empty.

  Definition ll_ready: MetricRiscvMachine -> Prop :=
    compile_inv loopBody_related hl_inv.

  Definition ll_inv: MetricRiscvMachine -> Prop :=
    runsToGood_Invariant ll_ready pc_start
                         (word.add pc_start (word.of_Z (4 * Z.of_nat (List.length loop_insts))))
                         (- 4 * Z.of_nat (List.length loop_insts)).

  Lemma putProgram_establishes_ll_inv: forall preInitial initial,
      initial = putProgram preInitial ->
      ll_inv initial.
  Proof. case TODO_sam. Qed.

  Context
      (* technical detail: "pc at beginning of loop" and "pc at end of loop" needs to be
         different so that we can have two disjoint states between which the system goes
         back and forth. If we had only one state, we could not prevent "runsTo" from
         always being runsToDone and not making progress, see compiler.ForeverSafe *)
      (loop_insts_nonempty: 0 < Z.of_nat (List.length loop_insts))
      (loop_insts_not_too_big: 4 * Z.of_nat (List.length loop_insts) < 2 ^ width).

  Lemma ll_inv_is_invariant: forall (st: MetricRiscvMachine),
      ll_inv st -> mcomp_sat (run1 iset) st ll_inv.
  Proof.
    intro st.
    eapply runsToGood_is_Invariant with
        (jump := - 4 * Z.of_nat (List.length loop_insts))
        (pc_end := word.add pc_start (word.of_Z (4 * Z.of_nat (List.length loop_insts)))).
    - unfold pc_start. destruct mlOk. solve_divisibleBy4.
    - intro C.
      assert (word.of_Z (4 * Z.of_nat (Datatypes.length loop_insts)) = word.of_Z 0) as D. {
        transitivity (word.sub pc_start pc_start).
        - rewrite C at 1. simpl. (* PARAMRECORDS *) ring.
        - simpl. (* PARAMRECORDS *) ring.
      }
      apply (f_equal word.unsigned) in D.
      unshelve erewrite @word.unsigned_of_Z in D. 1: exact word_ok. (* PARAMRECORDS? *)
      unshelve erewrite word.unsigned_of_Z_0 in D. 1: exact word_ok. (* PARAMRECORDS? *)
      unfold word.wrap in D.
      rewrite Z.mod_small in D by (simpl (* PARAMRECORDS *); blia).
      destruct loop_insts.
      + cbv in loop_insts_nonempty. discriminate.
      + simpl in D. blia.
    - (* Show that ll_ready (almost) ignores pc, nextPc, and metrics *)
      intros.
      unfold ll_ready, compile_inv, loopBody_related, compose_relation,
        FlatToRiscvSimulation.related in *.
      simp.
      match goal with
      | Ha: @getPc _ _ _ _ = _,
        Hb: @getPc _ _ _ _ = ?Q |- _ =>
        match type of Ha with
        | ?P = _ => replace P with Q in Ha;
                      rename Ha into A; move A at bottom
        end
      end.
      destruct b eqn: Heqb; cycle 1. {
        exfalso.
        unfold pc_start, program_base, loopBodyGhostConsts, FlatToRiscvFunctions.goodMachine in *.
        match type of A with
        | ?L = ?R => assert (word.sub L R = word.of_Z 0) as B by (rewrite A; ring)
        end.
        unfold loop_pos, main_size in B.
        simpl in B. (* PARAMRECORDS *)
        rewrite !Nat2Z.inj_add in B. change BinInt.Z.of_nat with Z.of_nat in *.
        match type of B with
        | ?L = _ => ring_simplify L in B
        end.
        pose proof main_size_correct as P.
        unfold main_size in P.
        simpl in B, P. (* PARAMRECORDS *)
        rewrite P in B.
        rewrite !Nat2Z.inj_add in B. change BinInt.Z.of_nat with Z.of_nat in *.
        match type of B with
        | ?L = _ => ring_simplify L in B
        end.
        case TODO_sam. (*  contradictory *)
      }
      destruct s1 as [ [ [ [ [ e1 c1 ] done1 ] t1 ] m1 ] l1 ].
      assert (l1 = map.empty). {
        unfold hl_inv in *. simp. reflexivity.
      }
      subst.
      destruct s2 as [ [ [ [ [ e2 c2 ] done2 ] t2 ] m2 ] l2 ].
      assert (l2 = map.empty). {
        unfold FlattenExprSimulation.related in *. simp. reflexivity.
      }
      subst.
      apply RegRename.related_redo in Hlrl.
      pose proof (FlattenExprSimulation.related_change_done false _ _ _ _ _ _ _ _ _ _ _ _ Hll).
      clear Hll.
      let r := fresh m "_regs" in
      let p := fresh m "_pc" in
      let n := fresh m "_npc" in
      let me := fresh m "_mem" in
      let x := fresh m "_xaddrs" in
      let l := fresh m "_log" in
      let mc := fresh m "_metrics" in
      destruct state as [ [r p n me x l] mc ].
      repeat match goal with
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             | |- _ => progress cbv beta iota
             | |- _ => eassumption
             | |- _ => reflexivity
             end.
      + simpl. unfold pc_start, loop_pos.
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
    - case TODO_sam.
    - solve_divisibleBy4.
    - solve_word_eq word_ok.
    - (* use compiler correctness for loop_body *)
      intros.
      unfold ll_ready, compile_inv in *. simp.
      eapply runsTo_weaken.
      + pose proof loopBodySim as P.
        unfold simulation in P.
        specialize P with (post1 := hl_inv).
        eapply P. 1: eassumption.
        clear P.
        unfold ExprImp.SimExec, hl_inv in *. simp.
        split. 1: case TODO_sam. (* doesn't hold, how to deal with the `done` flag? *)
        intros.
        pose proof @loop_body_correct as P.
        specialize (P _ cmd prog Semantics.exec spec sat).
        match goal with
        | |- Semantics.exec.exec ?e ?c ?t ?m ?l ?mc ?post =>
          replace e with (funimpls prog) by case TODO_sam;
          replace c with (loop_body prog) by case TODO_sam
        end.
        eapply P; try eassumption.
      + cbv beta. intros. split. 1: eassumption.
        unfold related in *. simp.
        (* TODO: is the guarantee from pipelineSim strong enough to prove what's needed
           for runsToGood_is_Invariant? *)
        case TODO_sam.
  Qed.

  Lemma ll_inv_implies_prefix_of_good: forall st,
      ll_inv st -> exists suff, spec.(goodTrace) (suff ++ st.(getLog)).
  Proof.
    unfold ll_inv, runsToGood_Invariant. intros.
    eapply extend_runsTo_to_good_trace. 2: case TODO_sam. 2: eassumption.
    simpl. unfold ll_ready, compile_inv, loopBody_related, hl_inv,
           compose_relation, FlattenExprSimulation.related,
           RegRename.related, FlatToRiscvSimulation.related, FlatToRiscvFunctions.goodMachine.
    intros. simp. eassumption.
  Qed.

  Lemma pipeline_proofs:
    (forall preInitial initial,
        initial = putProgram preInitial ->
        ll_inv initial) /\
    (forall st, ll_inv st -> mcomp_sat (run1 iset) st ll_inv) /\
    (forall st, ll_inv st -> exists suff, spec.(goodTrace) (suff ++ st.(getLog))).
  Proof.
    split; [|split].
    - exact putProgram_establishes_ll_inv.
    - apply ll_inv_is_invariant.
    - exact ll_inv_implies_prefix_of_good.
  Qed.

End Pipeline1.
