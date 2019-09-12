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

    NGstate: Type;
    NG :> NameGen varname NGstate;

    src2imp :> map.map varname Register;
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
    FlattenExpr.NGstate := NGstate;
  }.

  Instance FlatToRisvc_params{p: parameters}: FlatToRiscvCommon.FlatToRiscv.parameters := {|
    FlatToRiscvCommon.FlatToRiscv.ext_spec := ext_spec;
    FlatToRiscvCommon.FlatToRiscv.ext_guarantee := ext_guarantee;
  |}.

  Class assumptions{p: parameters}: Prop := {
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

  Definition funname := string.

  Axiom TODO: forall {T: Type}, T.

  Instance FlattenExpr_hyps: FlattenExpr.assumptions FlattenExpr_parameters := {
    FlattenExpr.locals_ok := locals_ok;
    FlattenExpr.mem_ok := mem_ok;
    FlattenExpr.funname_env_ok := funname_env_ok;
    FlattenExpr.ext_spec_ok := TODO;
  }.

  Instance word_riscv_ok: RiscvWordProperties.word.riscv_ok word. Admitted.

  Definition available_registers: list Register :=
    Eval cbv in List.unfoldn Z.succ 29 3.

  Local Notation cmd := (@Syntax.cmd (FlattenExprDef.FlattenExpr.mk_Syntax_params _)).
  Local Notation env := (@Semantics.env (FlattenExpr.mk_Semantics_params _)).
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

(*
  Definition goodMachine(e: env)(mH: mem)(st: MetricRiscvMachine): Prop :=
    exists t l mc g,
      functions2Riscv e funs = (g.(insts)
      FlatToRiscvFunctions.goodMachine t mH l mc g st.
*)

  Definition goodMachine: MetricRiscvMachine -> Prop. Admitted.

  Lemma exprImp2Riscv_correct: forall (e: env) (sH: cmd) lH mH mcH t program_base e_pos pos
                                      (initialL: MetricRiscvMachine) post instsL,
      snippet2Riscv e_pos pos sH = instsL ->
      Semantics.exec.exec e sH t mH lH mcH post ->
      initialL.(getPc) = word.add program_base (word.of_Z pos) ->
      goodMachine initialL ->
      runsTo initialL (fun finalL => exists t' mH' lH' mcH',
          post t' mH' lH' mcH' /\
          finalL.(getPc) = word.add initialL.(getPc)
                                   (word.of_Z (4 * Z.of_nat (List.length instsL))) /\
          goodMachine finalL).
  Admitted.

(*
  Lemma exprImp2Riscv_correct: forall (e: env) (sH: cmd) lH mH mcH t instsL
                                      (initialL: MetricRiscvMachine) post R,
      @ExprImp.cmd_size (FlattenExpr.mk_Semantics_params _) sH < 2 ^ 10 ->
      ExprImp2Riscv sH = instsL ->
      (word.unsigned initialL.(getPc)) mod 4 = 0 ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      initialL.(getLog) = t ->
      (program initialL.(getPc) instsL * eq mH * R)%sep initialL.(getMem) ->
      ext_guarantee initialL ->
      Semantics.exec.exec e sH t mH lH mcH post ->
      runsToNonDet.runsTo (mcomp_sat (run1 iset))
             initialL
             (fun finalL => exists mH' lH' mcH',
                  post finalL.(getLog) mH' lH' mcH' /\
                  map.extends finalL.(getRegs) lH' /\
                  (program initialL.(getPc) (ExprImp2Riscv sH) * eq mH' * R)%sep (getMem finalL) /\
                  getPc finalL = add (getPc initialL) (mul (ZToReg 4) (ZToReg (Zlength instsL))) /\
                  getNextPc finalL = add (getPc finalL) (ZToReg 4)).
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
      split; [assumption|].
      split; [assumption|].
      solve_MetricLog.
  Qed.
*)

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

  Add Ring wring : (word.ring_theory (word := word))
      (preprocess [autorewrite with rew_word_morphism],
       morphism (word.ring_morph (word := word)),
       constants [word_cst]).

  Context (prog: Program cmd)
          (spec: ProgramSpec)
          (sat: ProgramSatisfiesSpec prog Semantics.exec spec)
          (ml: MemoryLayout Semantics.width).

  Axiom insts_init: list Instruction.
  Axiom insts_body: list Instruction.

(*
      (* technical detail: "pc at beginning of loop" and "pc at end of loop" needs to be
         different so that we can have two disjoint states between which the system goes
         back and forth. If we had only one state, we could not prevent "runsTo" from
         always being runsToDone and not making progress, see compiler.ForeverSafe *)
      (insts_body_nonempty: insts_body <> nil)
*)

  (* pc at beginning of loop *)
  Definition pc_start: word :=
    word.add ml.(code_start) (word.of_Z (4 * Z.of_nat (List.length insts_init))).

  Definition ll_ready(st: MetricRiscvMachine): Prop :=
    exists regsH memH,
      spec.(isReady) st.(getLog) memH regsH /\
      spec.(goodTrace) st.(getLog) /\
      goodMachine st.

(*
  Definition ll_ready(st: MetricRiscvMachine): Prop :=
      exists regsH memH metricsH R p_stacklimit p_sp stack_trash initial_pc program_base
      e_pos e_impl,
        hl_ready st.(getLog) memH regsH metricsH /\
        map.get st.(getRegs) RegisterNames.sp = Some p_sp /\
        (R * eq memH * @word_array FlatToRisvc_params p_stacklimit stack_trash *
         program initial_pc insts_init * program pc_start insts_body *
         @functions FlatToRisvc_params program_base e_pos e_impl funnames)%sep st.(getMem).
*)

  Definition ll_inv: MetricRiscvMachine -> Prop := runsToGood_Invariant ll_ready pc_start.

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
        (startState := st) (* TODO should this be a "very-initial" state before executing init_code? *)
        (jump := - 4 * Z.of_nat (Datatypes.length insts_body))
        (pc_end := word.add pc_start (word.of_Z (4 * Z.of_nat (List.length insts_body)))).
    - intros. unfold ll_ready in *. simp. destruct_RiscvMachine state.
      repeat match goal with
             | |- exists _, _  => eexists
             | |- _ /\ _ => split
             | |- _ => eassumption
             end.
      match goal with
      | A: ?G |- ?G' => replace G' with G; [exact A|progress f_equal]
      end.
      f_equal. 2: admit. f_equal. all: admit.
    - unfold pc_start. admit.
    - admit.
    - admit.
    - solve_divisibleBy4.
    - solve_word_eq word_ok.
    - (* use compiler correctness for init_code *)
      eapply runsTo_weaken.
      + eapply exprImp2Riscv_correct; try exact exec_init; try reflexivity.
        (* establish goodMachine & other sideconditions of exprImp2Riscv_correct *)
        all: admit.
      + simpl. intros. unfold ll_ready. simp.
        repeat eexists. 1: { Fail exact H0. admit. }
        (* TODO: guarantee from exprImp2Riscv_correct needs to be stronger *)
        all: admit.
    - (* use compiler correctness for loop_body *)
      intros.
      unfold ll_ready in *. simp.
      eapply runsTo_weaken.
      + eapply exprImp2Riscv_correct.
        1: reflexivity.
        1: { pose proof @loop_body_correct as P.
             specialize (P _ cmd prog Semantics.exec spec sat).
             eapply P; eassumption. }
        all: admit.
      + simpl. intros. unfold ll_ready.
        (* TODO: guarantee from exprImp2Riscv_correct needs to be stronger *)
        admit.
    all: fail.
  Admitted.

  Lemma ll_inv_implies_prefix_of_good: forall st,
      ll_inv st -> exists suff, spec.(goodTrace) (suff ++ st.(getLog)).
  Proof.
    unfold ll_inv, runsToGood_Invariant. intros.
    eapply extend_runsTo_to_good_trace. 2: eassumption.
    simpl. unfold ll_ready.
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
