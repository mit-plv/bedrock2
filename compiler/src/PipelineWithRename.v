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
    PR :> MetricPrimitives PRParams;
    FlatToRiscv_hyps :> FlatToRiscvCommon.FlatToRiscv.assumptions;
    ext_spec_ok :> Semantics.ext_spec.ok _;
  }.

End Pipeline.


Section Pipeline1.

  Context {p: parameters}.
  Context {h: assumptions}.

  Local Notation RiscvMachineL := (MetricRiscvMachine Register _).

  Definition funname := string.
  Definition iset := if width =? 32 then RV32IM else RV64IM.

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

  Context {src2imp : map.map varname Register}.
  Context {src2imp_ops : map.ops src2imp}.

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

  Definition compile_prog(e: @Semantics.env (FlattenExpr.mk_Semantics_params _)) (init_sp: Z)
             (init_code loop_body: @Syntax.cmd (FlattenExpr.FlattenExpr.mk_Syntax_params _))
             (funs: list funname): list Instruction :=
    let e' := flatten_functions e funs in
    let e'' := rename_functions string Register funname string available_registers e' funs in
    (* TODO the two below should share local variables and not rename independently *)
    let init_code' := ExprImp2RenamedFlat init_code in
    let loop_body' := ExprImp2RenamedFlat loop_body in
    FlatToRiscvDef.compile_lit RegisterNames.sp init_sp ++
    FlatToRiscvDef.compile_prog e'' init_code' loop_body' funs.

End Pipeline1.
