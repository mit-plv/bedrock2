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
Require Import compiler.MetricsToRiscv.


Existing Instance riscv.Spec.Machine.DefaultRiscvState.

Open Scope Z_scope.

Module Import Pipeline.
  Definition varname := Register.

  Class parameters := {
    FlatToRiscvDef_params :> FlatToRiscvDef.FlatToRiscvDef.parameters;

    mem :> map.map word byte;
    locals :> map.map varname word;
    funname_env :> forall T: Type, map.map string T; (* abstract T for better reusability *)
    trace := list (mem * String.string * list word * (mem * list word));
    ExtSpec := trace -> mem -> String.string -> list word -> (mem -> list word -> Prop) -> Prop;
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

  Local Notation RiscvMachineL := MetricRiscvMachine.

  Definition funname := string.
  Definition iset := if width =? 32 then RV32IM else RV64IM.

  Instance FlattenExpr_hyps: FlattenExpr.assumptions FlattenExpr_parameters := {
    FlattenExpr.varname_eq_dec := varname_eq_dec;
    FlattenExpr.locals_ok := locals_ok;
    FlattenExpr.mem_ok := mem_ok;
    FlattenExpr.funname_env_ok := funname_env_ok;
    FlattenExpr.ext_spec_ok := ext_spec_ok;
  }.

  Instance word_riscv_ok: RiscvWordProperties.word.riscv_ok word. Admitted.

  (* only works if varname=Register *)
  Definition ExprImp2Riscv(s: Syntax.cmd): list Instruction :=
    FlatToRiscvDef.compile_stmt (ExprImp2FlatImp s).

  Definition compile_functions(e: Semantics.env)(funnames: list funname): list Instruction :=
    FlatToRiscvDef.compile_functions (flatten_functions e funnames) funnames.

  Definition compile_prog(e: Semantics.env)(s: Syntax.cmd)(funs: list funname): list Instruction :=
    let e' := flatten_functions e funs in
    let s' := ExprImp2FlatImp s in
    FlatToRiscvDef.compile_prog e' s' FlatImp.SSkip funs.

  Definition enough_registers(s: Syntax.cmd): Prop :=
    FlatToRiscvDef.valid_registers (ExprImp2FlatImp s).

  (* simpler than debugging why blia/blia fails *)
  Ltac ineq_step :=
    first
      [ eapply Z.le_trans; [eassumption|]
      | eapply Z.le_trans; [|eassumption]
      | eapply Z.lt_le_trans; [eassumption|]
      | eapply Z.lt_le_trans; [|eassumption]
      | eapply Z.le_lt_trans; [eassumption|]
      | eapply Z.le_lt_trans; [|eassumption] ].

  (* The following two size lemmas are nice to have, but not really needed here:
     FlatToRiscv.compile_stmt_correct will apply them on its own when needed. *)

  Lemma flatToRiscv_size: forall (s: FlatImp.stmt) (insts: list Instruction),
      FlatToRiscvDef.compile_stmt s = insts ->
      0 <= Zlength insts <= FlatImp.stmt_size s.
  Proof.
    intros. subst.
    apply (EmitsValid.compile_stmt_size s).
  Qed.

  Lemma exprImp2Riscv_size: forall (s: Syntax.cmd) (insts: list Instruction),
      ExprImp2Riscv s = insts ->
      0 <= Zlength insts <= ExprImp.cmd_size s.
  Proof.
    intros.
    unfold ExprImp2Riscv, ExprImp2FlatImp in *.
    match goal with
    | H: context [fst ?x] |- _ => destruct x eqn: E
    end.
    apply FlattenExpr.flattenStmt_size in E.
    apply flatToRiscv_size in H.
    split; [blia|].
    destruct E as [_ E].
    destruct H as [_ H].
    simpl in *.
    (* TODO why do lia and omega fail here? PARAMRECORDS? *)
    Fail blia. Fail bomega.
    eapply Z.le_trans; eassumption.
  Qed.

  Lemma exprImp2Riscv_correct: forall sH mH mcH t instsL (initialL: RiscvMachineL) post,
      ExprImp.cmd_size sH < 2 ^ 10 ->
      enough_registers sH ->
      ExprImp2Riscv sH = instsL ->
      (word.unsigned initialL.(getPc)) mod 4 = 0 ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      initialL.(getLog) = t ->
      (program initialL.(getPc) instsL * eq mH)%sep initialL.(getMem) ->
      ext_guarantee initialL ->
      Semantics.exec.exec map.empty sH t mH map.empty mcH post ->
      runsTo (mcomp_sat (run1 iset))
             initialL
             (fun finalL => exists mH' lH' mcH',
                  post finalL.(getLog) mH' lH' mcH' /\
                  map.extends finalL.(getRegs) lH' /\
                  (program initialL.(getPc) (ExprImp2Riscv sH) * eq mH')%sep (getMem finalL) /\
                  (finalL.(getMetrics) - initialL.(getMetrics) <= lowerMetrics (mcH' - mcH))%metricsL).
  Proof.
    intros. subst.
    eapply runsTo_weaken. Unshelve.
    - eapply FlatToRiscvMetric.compile_stmt_correct
          with (postH := (fun t m l mc =>
                            exists l' mc',
                              post t m l' mc' /\
                              map.extends l l' /\
                              (mc - mcH <= mc' - mcH)%metricsH)
               ); try reflexivity.
      + eapply FlatImp.exec.weaken.
        * match goal with
          | |- _ ?env ?s ?t ?m ?l ?mc ?post =>
            epose proof (@FlattenExpr.flattenStmt_correct _ _ _ _ _ _ _ _ _ eq_refl) as Q
          end.
          eapply Q.
          eassumption.
        * simpl. intros. simp. do 2 eexists. do 2 (split; try eassumption).
      + unfold FlatToRiscvDef.stmt_not_too_big.
        unfold ExprImp2Riscv, ExprImp2FlatImp in *.
        match goal with
        | |- context [fst ?x] => destruct x eqn: E
        end.
        match goal with
        | H: _ = (?a, ?b) |- context [fst ?x] => replace x with (a, b) by reflexivity
        end.
        unfold fst.
        apply FlattenExpr.flattenStmt_size in E.
        ineq_step.
        destruct E as [_ E].
        simpl in *.
        (* TODO why do blia and blia fail here? PARAMRECORDS? *)
        Fail blia. Fail blia.
        exact E.
      + unfold enough_registers, ExprImp2FlatImp, fst in *. assumption.
      + assumption.
      + match goal with
        | H: context [ program _ ?insts ] |- context [ program _ ?insts' ] =>
          change insts' with insts
        end.
        simpl in *.
        seplog.
      + assumption.
      + assumption.
    - simpl. intros. simp. do 3 eexists. do 3 (split; try eassumption).
      + seplog.
      + solve_MetricLog.
  Qed.

  Lemma exprImp2Riscv_correctTrace: forall sH mH mcH t instsL (initialL: RiscvMachineL) (post: trace -> Prop),
      ExprImp.cmd_size sH < 2 ^ 10 ->
      enough_registers sH ->
      ExprImp2Riscv sH = instsL ->
      (word.unsigned initialL.(getPc)) mod 4 = 0 ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      initialL.(getLog) = t ->
      (program initialL.(getPc) instsL * eq mH)%sep initialL.(getMem) ->

      ext_guarantee initialL ->
      Semantics.exec.exec map.empty sH t mH map.empty mcH (fun t' m' l' mc' => post t') ->
      runsTo (mcomp_sat (run1 iset))
             initialL
             (fun finalL =>
                  post finalL.(getLog)).
  Proof.
    intros.
    eapply runsTo_weaken.
    - eapply exprImp2Riscv_correct; try eassumption.
    - intros. simpl in *. simp.
      assumption.
  Qed.

End Pipeline1.
