Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Export lib.LibTacticsMin.
Require Export coqutil.Decidable.
Require        compiler.ExprImp.
Require Export compiler.FlattenExpr.
Require        compiler.FlatImp.
Require        compiler.FlatToRiscv.
Require Export riscv.Spec.Decode.
Require Export riscv.Spec.Machine.
Require Export riscv.Platform.Run.
Require Export riscv.Platform.Minimal.
Require Export riscv.Utility.Monads.
Require Import riscv.Utility.runsToNonDet.
Require Import compiler.util.MyOmega.
Require Import Coq.micromega.Lia.
Require Export compiler.NameGen.
Require Export compiler.util.Common.
Require Export coqutil.Decidable.
Require Export riscv.Utility.Encode.
Require Export riscv.Spec.Primitives.
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


Existing Instance riscv.Spec.Machine.DefaultRiscvState.
<<<<<<< HEAD

=======
>>>>>>> upstream/master

Open Scope Z_scope.

Module Import Pipeline.
  Definition varname := Register.

  Class parameters := {
    FlatToRiscvDef_params :> FlatToRiscvDef.FlatToRiscvDef.parameters;
    actname := FlatToRiscvDef.FlatToRiscvDef.actname;

    W :> Words;
    mem :> map.map word byte;
    locals :> map.map varname word;
    trace := list (mem * actname * list word * (mem * list word));
    ExtSpec := trace -> mem -> actname -> list word -> (mem -> list word -> Prop) -> Prop;
    ext_spec : ExtSpec;

    NGstate: Type;
    NG :> NameGen varname NGstate;

    ext_guarantee : RiscvMachine Register FlatToRiscvDef.FlatToRiscvDef.actname -> Prop;
    M: Type -> Type;
    MM :> Monad M;
    RVM :> RiscvProgram M word;
    PRParams :> PrimitivesParams M (RiscvMachine Register actname);
  }.

  Instance FlatToRisvc_params{p: parameters}: FlatToRiscv.FlatToRiscv.parameters := {|
    FlatToRiscv.FlatToRiscv.ext_spec := ext_spec;
    FlatToRiscv.FlatToRiscv.ext_guarantee := ext_guarantee;
  |}.

  Class assumptions{p: parameters} := {
    actname_eq_dec :> DecidableEq actname;
    varname_eq_dec :> DecidableEq varname;
    mem_ok :> map.ok mem;
    locals_ok :> map.ok locals;
    PR :> Primitives PRParams;
    FlatToRiscv_hyps :> FlatToRiscv.FlatToRiscv.assumptions;
  }.

End Pipeline.


Section Pipeline1.

  Context {p: parameters}.
  Context {h: assumptions}.

  Definition funname := Empty_set.
  Definition iset := if width =? 32 then RV32IM else RV64IM.

  Instance FlattenExpr_parameters: FlattenExpr.parameters := {|
    FlattenExpr.varname := varname;
    FlattenExpr.actname := actname;
    FlattenExpr.W := W;
    FlattenExpr.varname_eq_dec := varname_eq_dec;
    FlattenExpr.actname_eq_dec := actname_eq_dec;
    FlattenExpr.locals := locals;
    FlattenExpr.mem := mem;
    FlattenExpr.locals_ok := locals_ok;
    FlattenExpr.mem_ok := mem_ok;
    FlattenExpr.ext_spec := ext_spec;
    FlattenExpr.max_ext_call_code_size := _;
    FlattenExpr.max_ext_call_code_size_nonneg := FlatImp.FlatImpSize.max_ext_call_code_size_nonneg;
    FlattenExpr.NGstate := NGstate;
    FlattenExpr.NG := NG;
  |}.

  Instance word_riscv_ok: RiscvWordProperties.word.riscv_ok word. Admitted.

  Definition flatten(s: Syntax.cmd): FlatImp.stmt :=
    let ngs: NGstate := freshNameGenState (ExprImp.allVars_cmd_as_list s) in
    let (sFlat, ngs') := flattenStmt ngs s in sFlat.

  (* only works if varname=Register *)
  Definition exprImp2Riscv(s: Syntax.cmd): list Instruction :=
    FlatToRiscvDef.compile_stmt iset (flatten s).

  Definition enough_registers(s: Syntax.cmd): Prop :=
    FlatToRiscvDef.valid_registers (flatten s).

  (* simpler than debugging why omega/lia fails *)
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
      FlatToRiscvDef.compile_stmt iset s = insts ->
      0 <= Zlength insts <= FlatImp.stmt_size s.
  Proof.
    intros. subst.
    apply (EmitsValid.compile_stmt_size iset s).
  Qed.

  Lemma exprImp2Riscv_size: forall (s: Syntax.cmd) (insts: list Instruction),
      exprImp2Riscv s = insts ->
      0 <= Zlength insts <= ExprImp.cmd_size s.
  Proof.
    intros.
    unfold exprImp2Riscv, flatten in *.
    destruct_one_match_hyp.
    apply FlattenExpr.flattenStmt_size in E.
    apply flatToRiscv_size in H.
    split; [lia|].
    destruct E as [_ E].
    destruct H as [_ H].
    simpl in *.
    (* TODO why do omega and lia fail here? PARAMRECORDS? *)
    Fail omega. Fail lia.
    eapply Z.le_trans; eassumption.
  Qed.

  Lemma exprImp2Riscv_correct: forall sH mH t instsL initialL (post: trace -> Prop),
      ExprImp.cmd_size sH < 2 ^ 10 ->
      enough_registers sH ->
      exprImp2Riscv sH = instsL ->
      (word.unsigned initialL.(getPc)) mod 4 = 0 ->
      initialL.(getNextPc) = word.add initialL.(getPc) (word.of_Z 4) ->
      initialL.(getLog) = t ->
      (program initialL.(getPc) instsL * eq mH)%sep initialL.(getMem) ->
      ext_guarantee initialL ->
      Semantics.exec.exec map.empty sH t mH map.empty (fun t' m' l' => post t') ->
      runsTo (mcomp_sat (run1 iset))
             initialL
             (fun finalL => post finalL.(getLog)).
  Proof.
    intros. subst.
    eapply runsTo_weaken.
    - eapply FlatToRiscv.compile_stmt_correct
        with (postH := (fun t m l => post t)); try reflexivity.
      + eapply FlatImp.exec.weaken.
        * match goal with
          | |- _ ?env ?s ?t ?m ?l ?post =>
            epose proof (@FlattenExpr.flattenStmt_correct _ _ s _ t m _ eq_refl) as Q
          end.
          eapply Q.
          eassumption.
        * simpl. intros. simp. assumption.
      + unfold FlatToRiscvDef.stmt_not_too_big.
        unfold exprImp2Riscv, ExprImp2FlatImp, flatten in *.
        destruct_one_match_hyp.
        match goal with
        | H: _ = (?a, ?b) |- context [fst ?x] => replace x with (a, b)
        end.
        unfold fst.
        apply FlattenExpr.flattenStmt_size in E.
        ineq_step.
        destruct E as [_ E].
        simpl in *.
        (* TODO why do omega and lia fail here? PARAMRECORDS? *)
        Fail omega. Fail lia.
        exact E.
      + unfold enough_registers, ExprImp2FlatImp, flatten, fst in *. assumption.
      + assumption.
      + match goal with
        | H: context [ program _ ?insts ] |- context [ program _ ?insts' ] =>
          change insts' with insts
        end.
        simpl in *.
        seplog.
      + assumption.
      + assumption.
    - simpl. intros. simp. assumption.
  Qed.

End Pipeline1.
