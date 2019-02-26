Require Export Coq.Lists.List.
Require Import Coq.ZArith.ZArith.
Export ListNotations.
Require Export lib.LibTacticsMin.
Require Export coqutil.Decidable.
Require        compiler.ExprImp.
Require Export compiler.FlattenExpr.
Require        compiler.FlatImp.
Require        compiler.FlatToRiscv.
Require Export riscv.Decode.
Require Export riscv.Program.
Require Export riscv.Run.
Require Export riscv.Minimal.
Require Export riscv.util.Monads.
Require Import riscv.runsToNonDet.
Require Import compiler.util.MyOmega.
Require Import Coq.micromega.Lia.
Require Export compiler.NameGen.
Require Export compiler.util.Common.
Require Export coqutil.Decidable.
Require Export riscv.Encode.
Require Export riscv.Primitives.
Require Import compiler.GoFlatToRiscv.
Require Import riscv.MkMachineWidth.
Require Export riscv.proofs.DecodeEncode.
Require Export riscv.proofs.EncodeBound.
Require Export compiler.EmitsValid.
Require Export compiler.RegAlloc3.
Require coqutil.Map.SortedList.
Require Import riscv.Utility.
Require Export riscv.Memory.
Require Export riscv.InstructionCoercions.
Require Import compiler.SeparationLogic.
Require Import compiler.Simp.


Existing Instance riscv.Program.DefaultRiscvState.


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
    let ngs: NGstate := freshNameGenState (ExprImp.allVars_cmd s) in
    let (sFlat, ngs') := flattenStmt ngs s in sFlat.

  (* only works if varname=Register *)
  Definition exprImp2Riscv(s: Syntax.cmd): list Instruction :=
    FlatToRiscvDef.compile_stmt iset (flatten s).

  Definition enough_registers(s: Syntax.cmd): Prop :=
    FlatToRiscvDef.valid_registers (flatten s).

  Lemma exprImp2Riscv_correct: forall sH mH instsL initialL postH imemStart,
      ExprImp.cmd_size sH < 2 ^ 7 ->
      enough_registers sH ->
      exprImp2Riscv sH = instsL ->
      (GoFlatToRiscv.program imemStart instsL * eq mH)%sep initialL.(getMem) ->
      Semantics.exec.exec map.empty sH nil mH map.empty postH ->
      runsTo (mcomp_sat (run1 iset))
             initialL
             (fun finalL =>
                exists finalMH,
                  (GoFlatToRiscv.program imemStart instsL * eq finalMH)%sep finalL.(getMem) /\
                  postH finalL.(getLog) finalMH finalL.(getRegs)).
    Abort. (* won't hold because low-level registers differ from locals *)

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

  Lemma exprImp2Riscv_correct: forall sH mH instsL initialL (post: trace -> Prop) imemStart,
      ExprImp.cmd_size sH < 2 ^ 10 ->
      enough_registers sH ->
      exprImp2Riscv sH = instsL ->
      initialL.(getLog) = nil ->
      initialL.(getRegs) = map.empty ->
      (program imemStart instsL * eq mH)%sep initialL.(getMem) ->
      Semantics.exec.exec map.empty sH nil mH map.empty (fun t m l => post t) ->
      runsTo (mcomp_sat (run1 iset))
             initialL
             (fun finalL => post finalL.(getLog)).
  Proof.
    intros.
    eapply runsTo_weaken.
    - eapply @FlatToRiscv.compile_stmt_correct
        with (postH := (fun t m l => post t)); try reflexivity.
      + admit.
      + eapply FlatImp.exec.weaken.
        * rewrite H2, H3.
          match goal with
          | |- _ ?env ?s ?t ?m ?l ?post =>
            epose proof (@FlattenExpr.flattenStmt_correct _ _ s t m _ eq_refl) as Q
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
      + admit.
      + admit.
      + admit.
      + admit.
      + admit.
    - simpl. intros. simp. assumption.
      Unshelve. intros. apply True.
  Admitted.

  (*
  (* We could also say something about the memory, but then the statement becomes more complex.
     And note that the register we look at could contain any value loaded from the memory. *)
  Lemma exprImp2Riscv_correct: forall {Bw: BitWidths} sH initialL instsL fuelH finalH initialMemH finalMemH,
    (Z.of_nat (ExprImp.cmd_size sH) < 2 ^ 7)%Z ->
    enough_registers sH ->
    exprImp2Riscv sH = instsL ->
    4 * Zlength instsL <= Memory.memSize initialL.(machineMem) ->
    evalH empty_map fuelH empty_map initialMemH sH = Some (finalH, finalMemH) ->
    FlatToRiscv.mem_inaccessible initialMemH 0 (4 * Zlength instsL) ->
    FlatToRiscvInvariants.containsMem initialL.(machineMem) initialMemH ->
    exists fuelL,
      forall resVar res,
      get finalH resVar = Some res ->
      getReg (evalL fuelL instsL initialL).(core).(registers) resVar = res.
  Proof.
    introv B ER C MB EvH Ina Cm.
    unfold exprImp2Riscv, flatten in C.
    unfold enough_registers, flatten in ER.
    destruct_one_match_hyp.
    unfold evalH in EvH.
    assert (FlatToRiscv.stmt_not_too_big s) as N. {
      unfold FlatToRiscv.stmt_not_too_big.
      pose proof @flattenStmt_size as D1.
      clear -B D1.
      (* specialize (D1 E).*)
      (* apply Nat2Z.inj_le in D1. *)
      repeat (so fun hyporgoal => match hyporgoal with
      | context [ (2 ^ ?a)%Z ] => let r := eval cbv in (2 ^ a)%Z in change (2 ^ a)%Z with r in *
      end).
      Set Printing Implicit.
      (* TODO ZName.ZName vs Name mismatch *)
      lia.
    }
    pose proof @flattenStmt_correct as P.
    specialize (P _ _ _ _ _ _ _ _ _ _ fuelH sH s initialMemH finalH finalMemH).
    destruct P as [fuelM [finalM [EvM GM] ] ].
    - unfold ExprImp2FlatImp. rewrite E. reflexivity.
    - unfold evalH. apply EvH.
    - pose proof  FlatToRiscv.compile_stmt_correct as P.
      specialize P with (imemStart := (@ZToReg _ MW 0)).
      let r := eval unfold evalL in (evalL 0 instsL initialL) in
          match r with
          | execState _ ?x => specialize P with (initialL := x)
          end.
      edestruct P as [fuelL [P1 P2] ]; clear P.
      + unfold translate, DefaultRiscvState, default_translate.
        intros.
          autorewrite with alu_defs.
        (* TODO all of this should be something like autorewrite in * *)
        destruct_one_match; [exfalso|reflexivity].
        apply Bool.negb_true_iff in E0.
        apply reg_eqb_false in E0.
        pose proof pow2_wXLEN_4 as Q.
        rewrite <- (wordToNat_natToWord_idempotent' wXLEN Q) in H.
        rewrite <- wordToNat_mod in H.
        * apply wordToNat_zero in H. contradiction.
        * apply natToWord_nzero; omega.
      + unfold translate, DefaultRiscvState, default_translate.
        intros.
        autorewrite with alu_defs.
        destruct_one_match; [exfalso|reflexivity].
        apply Bool.negb_true_iff in E0.
        apply weqb_false_iff in E0.
        pose proof ZToReg 8_lt_pow2_wXLEN as Q.
        rewrite <- (wordToNat_natToWord_idempotent' wXLEN Q) in H.
        rewrite <- wordToNat_mod in H.
        * apply wordToNat_zero in H. contradiction.
        * apply natToWord_nzero; omega.
      + eassumption.
      + assumption.
      + assumption.
      + rewrite roundTrip_0. reflexivity.
      + eassumption.
      + unfold putProgram. simpl.
        Memory.destruct_list_length.
        * rewrite H. simpl. assumption.
        * pose proof MB.
          rewrite H in MB.
          apply store_word_list_preserves_containsMem;
            unfold Memory.valid_addr;
            rewrite? map_length;
            rewrite? roundTrip_0;
            auto;
            simpl;
            omega.
      + apply putProgram_containsProgram with (s := s);
          rewrite? roundTrip_0; rewrite? Nat.add_0_l; (assumption || reflexivity).
      + reflexivity.
      + simpl. rewrite wplus_unit. reflexivity.
      + rewrite roundTrip_0. assumption.
      + exists fuelL. intros.
        unfold getReg, FlatToRiscv.State_is_RegisterFile.
        unfold extends in P1.
        unfold evalL.
        erewrite P1; try reflexivity.
        apply GM. exact H.
  Qed.
         *)

End Pipeline1.
