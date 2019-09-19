Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Export coqutil.Decidable.
Require        compiler.ExprImp.
Require Export compiler.FlattenExprDef.
Require Export compiler.FlattenExpr.
Require        compiler.FlatImp.
Require        compiler.FlatToRiscvMetric.
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
Require Export compiler.RegAlloc3.
Require coqutil.Map.SortedList.
Require Import riscv.Utility.Utility.
Require Export riscv.Platform.Memory.
Require Export riscv.Utility.InstructionCoercions.
Require Import compiler.SeparationLogic.
Require Import compiler.Simp.
Require Import compiler.FlattenExprSimulation.
Require Import compiler.RegAlloc.
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
    src2imp_ops :> map.ops src2imp;

    ext_guarantee : MetricRiscvMachine -> Prop;
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

  Instance FlatToRisvc_params{p: parameters}: FlatToRiscvCommon.FlatToRiscv.parameters := {|
    FlatToRiscvCommon.FlatToRiscv.ext_spec := ext_spec;
    FlatToRiscvCommon.FlatToRiscv.ext_guarantee := ext_guarantee;
  |}.

  Class assumptions{p: parameters}: Prop := {
    mem_ok :> map.ok mem;
    locals_ok :> map.ok locals;
    funname_env_ok :> forall T, map.ok (funname_env T);
    src2imp_ok :> map.ok src2imp;
    Registers_ok :> map.ok Registers;
    PR :> MetricPrimitives PRParams;
    FlatToRiscv_hyps :> FlatToRiscvCommon.FlatToRiscv.assumptions;
    ext_spec_ok :> Semantics.ext_spec.ok _;
  }.

End Pipeline.


Section Pipeline1.

  Context {p: parameters}.
  Context {h: assumptions}.

  Definition funname := string.

  Axiom TODO: False.

  Instance FlattenExpr_hyps: FlattenExpr.assumptions FlattenExpr_parameters := {
    FlattenExpr.locals_ok := locals_ok;
    FlattenExpr.mem_ok := mem_ok;
    FlattenExpr.funname_env_ok := funname_env_ok;
    FlattenExpr.ext_spec_ok := match TODO with end;
  }.

  Instance word_riscv_ok: RiscvWordProperties.word.riscv_ok word. case TODO. Defined.

  Definition available_registers: list Register :=
    Eval cbv in List.unfoldn Z.succ 29 3.

  Local Notation cmd := (@Syntax.cmd (FlattenExprDef.FlattenExpr.mk_Syntax_params _)).
  Local Notation env := (@Semantics.env (FlattenExpr.mk_Semantics_params _)).
  Local Notation localsH := (@Semantics.locals (FlattenExpr.mk_Semantics_params _)).
  Local Notation Program := (@Program (FlattenExpr.mk_Semantics_params _)).
  Local Notation ProgramSpec := (@ProgramSpec (FlattenExpr.mk_Semantics_params _)).

  Definition functions2Riscv(e: env)(funs: list funname): list Instruction * fun_pos_env :=
    let e' := flatten_functions e funs in
    let e'' := rename_functions String.eqb Z.eqb String.eqb String.eqb available_registers ext_spec e' funs in
    FlatToRiscvDef.compile_functions e'' funs.

  Definition ExprImp2RenamedFlat(s: cmd): FlatImp.stmt :=
    let flat := ExprImp2FlatImp s in
    match rename_stmt map.empty flat available_registers with
    | Some flat' => flat'
    | None => FlatImp.SSkip
    end.

  Definition snippet2Riscv(e_pos: fun_pos_env)(mypos: Z)(s: cmd): list Instruction :=
    let flat := ExprImp2RenamedFlat s in
    FlatToRiscvDef.compile_snippet e_pos mypos flat.

  Definition goodMachine(e: env)(t: Semantics.trace)
             (mH: Semantics.mem)
             (lH: localsH)
             (st: MetricRiscvMachine): Prop :=
    exists funnames g posenv lL,
      (* TODO should we relate low-level (regalloc'ed) and high-level locals? *)
      functions2Riscv e funnames = (g.(insts), posenv) /\
      FlatToRiscvFunctions.goodMachine t mH lL g st.

  Definition goodMachine': MetricRiscvMachine -> Prop. case TODO. Defined.

  Definition regAllocSim := RegAlloc.checkerSim String.eqb Z.eqb String.eqb String.eqb
                                                available_registers 777 (@ext_spec p).

  Definition related :=
    (compose_relation FlattenExprSimulation.related
    (compose_relation (RegAlloc.related eqb Z.eqb eqb eqb ext_spec)
                      FlatToRiscvSimulation.related)).

  Definition pipelineSim: simulation ExprImp.SimExec runsTo related :=
    (compose_sim FlattenExprSimulation.flattenExprSim
    (compose_sim regAllocSim
                 FlatToRiscvSimulation.flatToRiscvSim)).

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Context (prog: Program cmd)
          (spec: ProgramSpec)
          (sat: ProgramSatisfiesSpec prog Semantics.exec spec)
          (ml: MemoryLayout Semantics.width).

  Definition hl_inv: @ExprImp.SimState (FlattenExpr.mk_Semantics_params _) -> Prop :=
    fun '(e, c, done, t, m, l) => spec.(isReady) t m l /\ spec.(goodTrace) t.

  Definition ll_ready: MetricRiscvMachine -> Prop :=
    compile_inv related hl_inv.

  Axiom insts_init: list Instruction.
  Axiom insts_body: list Instruction.

  (* pc at beginning of loop *)
  Definition pc_start: word :=
    word.add ml.(code_start) (word.of_Z (4 * Z.of_nat (List.length insts_init))).

  Definition ll_inv: MetricRiscvMachine -> Prop := runsToGood_Invariant ll_ready pc_start.

  (* uses relative jumps for function calls and expects that the compiled functions will be
     put right after the code returned by this compilation function *)
  Definition compile_main(e_pos: fun_pos_env)(init_code loop_body: cmd): list Instruction :=
    (* TODO the two below should share local variables and not rename independently *)
    let init_code' := ExprImp2RenamedFlat init_code in
    let loop_body' := ExprImp2RenamedFlat loop_body in
    let main_size := List.length (FlatToRiscvDef.compile_main e_pos 42 init_code' loop_body') in
    FlatToRiscvDef.compile_main e_pos (- 4 * Z.of_nat main_size) init_code' loop_body'.

  Definition compile_prog(init_sp: Z)(p: Program cmd): list Instruction :=
    (* all positions in e_pos are relative to the position of the first function *)
    let '(fun_insts, e_pos) := functions2Riscv p.(funimpls) p.(funnames) in
    FlatToRiscvDef.compile_lit RegisterNames.sp init_sp ++
    compile_main e_pos p.(init_code) p.(loop_body) ++
    fun_insts.

  Definition putProgram(p: Program cmd)(code_addr: word)
             (stack_pastend: word)(preInitial: MetricRiscvMachine): MetricRiscvMachine :=
    let insts := compile_prog (word.unsigned stack_pastend) p in
    MetricRiscvMachine.putProgram (List.map encode insts) code_addr preInitial.

(*
      (* technical detail: "pc at beginning of loop" and "pc at end of loop" needs to be
         different so that we can have two disjoint states between which the system goes
         back and forth. If we had only one state, we could not prevent "runsTo" from
         always being runsToDone and not making progress, see compiler.ForeverSafe *)
      (insts_body_nonempty: insts_body <> nil)
*)

  Lemma putProgram_establishes_ll_inv: forall preInitial initial,
      initial = (putProgram prog ml.(code_start) ml.(stack_pastend) preInitial) ->
      ll_inv initial.
  Proof.
  Admitted.

  Lemma ll_inv_is_invariant: forall (st: MetricRiscvMachine),
      ll_inv st -> mcomp_sat (run1 iset) st ll_inv.
  Proof.
    intro st.
    eapply runsToGood_is_Invariant with
        (jump := - 4 * Z.of_nat (Datatypes.length insts_body))
        (pc_end := word.add pc_start (word.of_Z (4 * Z.of_nat (List.length insts_body)))).
    - (* Show that ll_ready ignores pc, nextPc, and metrics *)
      intros.
      unfold ll_ready, compile_inv, related, compose_relation, FlatToRiscvSimulation.related in *.
      simp. destruct_RiscvMachine state.
      repeat match goal with
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             | |- _ => progress cbv beta iota
             | |- _ => eassumption
             | |- _ => reflexivity
             end.
      + simpl.
        (* not the case: it only accepts pc at beginning or end of instructions,
           how to communicate this? *)
        case TODO.
      + case TODO.
    - unfold pc_start. case TODO.
    - case TODO.
    - case TODO.
    - solve_divisibleBy4.
    - solve_word_eq word_ok.
    - (* use compiler correctness for loop_body *)
      intros.
      unfold ll_ready, compile_inv in *. simp.
      eapply runsTo_weaken.
      + pose proof pipelineSim as P.
        unfold simulation in P.
        specialize P with (post1 := hl_inv).
        eapply P. 1: eassumption.
        clear P.
        unfold ExprImp.SimExec, hl_inv in *. simp.
        split. 1: case TODO. (* doesn't hold, how to deal with the `done` flag? *)
        intros.
        pose proof @loop_body_correct as P.
        specialize (P _ cmd prog Semantics.exec spec sat).
        match goal with
        | |- Semantics.exec.exec ?e ?c ?t ?m ?l ?mc ?post =>
          replace e with (funimpls prog) by case TODO;
          replace c with (loop_body prog) by case TODO
        end.
        eapply P; eassumption.
      + cbv beta. intros. split. 1: eassumption.
        unfold related in *. simp.
        (* TODO: is the guarantee from pipelineSim strong enough to prove what's needed
           for runsToGood_is_Invariant? *)
        case TODO.
  Qed.

  Lemma ll_inv_implies_prefix_of_good: forall st,
      ll_inv st -> exists suff, spec.(goodTrace) (suff ++ st.(getLog)).
  Proof.
    unfold ll_inv, runsToGood_Invariant. intros.
    eapply extend_runsTo_to_good_trace. 2: eassumption.
    simpl. unfold ll_ready, compile_inv, related, hl_inv,
           compose_relation, FlattenExprSimulation.related,
           RegAlloc.related, FlatToRiscvSimulation.related, FlatToRiscvFunctions.goodMachine.
    intros. simp. eassumption.
  Qed.

  Lemma pipeline_proofs:
    (forall preInitial initial,
        initial = putProgram prog ml.(code_start) ml.(stack_pastend) preInitial ->
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
