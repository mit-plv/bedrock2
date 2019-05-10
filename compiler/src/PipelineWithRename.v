Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Export coqutil.Decidable.
Require        compiler.ExprImp.
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
Require Export compiler.NameGen.
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
Require Import compiler.RegAlloc.
Require Import compiler.EventLoop.
Require Import bedrock2.MetricLogging.
Require Import compiler.FlatToRiscvCommon.
Require Import compiler.FlatToRiscvFunctions.

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

    NGstate: Type;
    NG :> NameGen varname NGstate;

    src2imp :> map.map varname Register;

    ext_guarantee : MetricRiscvMachine -> Prop;
    M: Type -> Type;
    MM :> Monad M;
    RVM :> RiscvProgram M word;
    PRParams :> PrimitivesParams M MetricRiscvMachine;
  }.

  Instance FlattenExpr_parameters{p: parameters}: FlattenExpr.parameters := {
    FlattenExpr.varname := varname;
    FlattenExpr.W := _;
    FlattenExpr.locals := locals;
    FlattenExpr.mem := mem;
    FlattenExpr.ext_spec := ext_spec;
    FlattenExpr.NGstate := NGstate;
  }.

  Instance FlatToRisvc_params{p: parameters}: FlatToRiscvCommon.FlatToRiscv.parameters := {|
    FlatToRiscvCommon.FlatToRiscv.ext_spec := ext_spec;
    FlatToRiscvCommon.FlatToRiscv.ext_guarantee := ext_guarantee;
  |}.

  Class assumptions{p: parameters} := {
    varname_eq_dec :> DecidableEq varname;
    mem_ok :> map.ok mem;
    locals_ok :> map.ok locals;
    funname_env_ok :> forall T, map.ok (funname_env T);
    src2imp_ops :> map.ops src2imp;
    PR :> MetricPrimitives PRParams;
    FlatToRiscv_hyps :> FlatToRiscvCommon.FlatToRiscv.assumptions;
    ext_spec_ok :> Semantics.ext_spec.ok _;
  }.

End Pipeline.


Section Pipeline1.

  Context {p: parameters}.
  Context {h: assumptions}.

  Definition funname := string.

  Axiom TODO: forall {T: Type}, T.

  Instance FlattenExpr_hyps: FlattenExpr.assumptions FlattenExpr_parameters := {
    FlattenExpr.varname_eq_dec := varname_eq_dec;
    FlattenExpr.locals_ok := locals_ok;
    FlattenExpr.mem_ok := mem_ok;
    FlattenExpr.funname_env_ok := funname_env_ok;
    FlattenExpr.ext_spec_ok := TODO;
  }.

  Instance word_riscv_ok: RiscvWordProperties.word.riscv_ok word. Admitted.

  Definition available_registers: list Register :=
    Eval cbv in List.unfoldn Z.succ 29 3.

  Definition ExprImp2Riscv(s: @Syntax.cmd (FlattenExpr.FlattenExpr.mk_Syntax_params _)):
    list Instruction :=
    let flat := ExprImp2FlatImp s in
    match rename_stmt string Register funname string map.empty flat available_registers with
    | Some flat' => FlatToRiscvDef.compile_stmt flat'
    | None => nil
    end.

  Definition ExprImp2RenamedFlat(s: @Syntax.cmd (FlattenExpr.FlattenExpr.mk_Syntax_params _)):
    FlatImp.stmt :=
    let flat := ExprImp2FlatImp s in
    match rename_stmt string Register funname string map.empty flat available_registers with
    | Some flat' => flat'
    | None => FlatImp.SSkip
    end.

(*
  Definition compile_functions(e: Semantics.env)(funnames: list funname): list Instruction :=
    FlatToRiscvDef.compile_functions (flatten_functions e funnames) funnames.
*)

  Local Notation cmd := (@Syntax.cmd (FlattenExpr.FlattenExpr.mk_Syntax_params _)).
  Local Notation env := (@Semantics.env (FlattenExpr.mk_Semantics_params _)).

  Definition compile_prog(e: env) (init_sp: Z) (init_code loop_body: cmd)
             (funs: list funname): list Instruction :=
    let e' := flatten_functions e funs in
    let e'' := rename_functions string Register funname string available_registers e' funs in
    (* TODO the two below should share local variables and not rename independently *)
    let init_code' := ExprImp2RenamedFlat init_code in
    let loop_body' := ExprImp2RenamedFlat loop_body in
    FlatToRiscvDef.compile_lit RegisterNames.sp init_sp ++
    FlatToRiscvDef.compile_prog e'' init_code' loop_body' funs.

  Lemma compile_prog_correct
      (* high-level trace invariant which holds at the beginning of each loop iteration,
         but might not hold in the middle of the loop because more needs to be appended *)
      (hl_inv: trace -> Prop)
      (* high-level invariant on the all high-level state which holds at beginning of each
         loop iteration: *)
      (hl_ready: trace -> mem -> locals -> MetricLog -> Prop)
      (hl_ready_implies_hl_inv: forall t m l mc, hl_ready t m l mc -> hl_inv t)
      (e: env) (t0: trace) (m0: mem) (l0: locals) (mc0: MetricLog)
      (init_code loop_body: cmd)
      (funnames: list funname)
      (exec_init: Semantics.exec e init_code t0 m0 l0 mc0 hl_ready)
      (exec_body: forall t m l mc, hl_ready t m l mc ->
                                   Semantics.exec e loop_body t m l mc hl_ready)
    :
      (* there exists a low-level invariant which is somewhat complex and therefore not exposed *)
      exists ll_inv: MetricRiscvMachine -> Prop,
        (* how a client can establish ll_inv: *)
        (forall st: MetricRiscvMachine,
            True ->
            ll_inv st) /\
        (* how a client can use ll_inv: *)
        (forall st: MetricRiscvMachine, ll_inv st -> mcomp_sat (run1 iset) st ll_inv /\
                                                     exists suff, hl_inv (suff ++ st.(getLog))).
  Proof.
    intros.

    assert (pc_start: word) by admit. (* start of loop body *)
    assert (insts_init: list Instruction) by admit.
    assert (insts_body: list Instruction) by admit.

    set (ll_ready := fun (st: MetricRiscvMachine) =>
      exists regsH memH metricsH R p_stacklimit p_sp stack_trash initial_pc program_base
      e_pos e_impl,
        hl_ready st.(getLog) memH regsH metricsH /\
        map.get st.(getRegs) RegisterNames.sp = Some p_sp /\
        (R * eq memH * @word_array FlatToRisvc_params p_stacklimit stack_trash *
         program initial_pc insts_init * program pc_start insts_body *
         @functions FlatToRisvc_params program_base e_pos e_impl funnames)%sep st.(getMem)).

    pose proof (runsToGood_is_Invariant ll_ready) as P.
    exists (runsToGood_Invariant ll_ready pc_start).

  Admitted.

End Pipeline1.
