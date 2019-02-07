Require Export Coq.Lists.List.
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
Require Export bbv.DepEqNat.
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


Existing Instance riscv.Program.DefaultRiscvState.


Open Scope Z_scope.

Module Import Pipeline.
  Class parameters := {
    varname := Register;
    actname: Type;
    actname_eq_dec :> DecidableEq actname;
    W :> Words;
    mem :> map.map word byte;
    locals :> map.map varname word;
    trace := list (mem * actname * list word * (mem * list word));
    ExtSpec := trace -> mem -> actname -> list word -> (mem -> list word -> Prop) -> Prop;
    ext_spec : ExtSpec;

    NGstate: Type;
    NG :> NameGen varname NGstate;

    (* registers :> map.map Register word; (* same as locals at the moment *) *)
    registerSetFunctions :> compiler.util.Set.SetFunctions Register;
    reg2varMapping :> map.map Register varname;

    M: Type -> Type;
    MM :> Monad M;
    RVM :> RiscvProgram M word;
    PR :> Primitives actname M;
  }.
End Pipeline.


Section Pipeline1.

  Context {p: parameters}.

  Definition funname := Empty_set.
  Local Notation RiscvMachine := (RiscvMachine Register actname).
  Definition iset := if width =? 32 then RV32IM else RV64IM.

  Instance syntax_params: Syntax.parameters := {|
    Syntax.varname := varname;
    Syntax.funname := funname;
    Syntax.actname := actname;
  |}.

  Definition TODO{T: Type}: T. Admitted.

  Instance semantics_params: Semantics.parameters := {|
    Semantics.syntax := syntax_params;
    Semantics.width := width;
    Semantics.word := word;
    Semantics.byte := byte;
    Semantics.mem := mem;
    Semantics.locals := locals;
    Semantics.env := TODO; (* map with Empty_set keys *)
    Semantics.funname_eqb := TODO;
    Semantics.ext_spec := TODO;
  |}.

  (* TODO should we have two instances, one for FlatImp with varname (before regalloc),
     and one for FlatImp with Register (after regaloc) ? *)

  Instance FlatImp_params: FlatImp.FlatImp.parameters := {|
    FlatImp.FlatImp.syntax_params := syntax_params;
    FlatImp.FlatImp.W := W;
    FlatImp.FlatImp.varname_eq_dec := TODO;
    FlatImp.FlatImp.funcname_eq_dec := TODO;
    FlatImp.FlatImp.actname_eq_dec := TODO;
    FlatImp.FlatImp.locals := locals;
    FlatImp.FlatImp.env := TODO;
    FlatImp.FlatImp.mem := mem;
    FlatImp.FlatImp.locals_ok := TODO;
    FlatImp.FlatImp.env_ok := TODO;
    FlatImp.FlatImp.mem_ok := TODO;
    FlatImp.FlatImp.ext_spec := TODO;
    FlatImp.FlatImp.max_ext_call_code_size action := TODO;
    FlatImp.FlatImp.max_ext_call_code_size_nonneg := TODO;
  |}.

  Instance FlatToRiscvDef_params: FlatToRiscvDef.FlatToRiscvDef.parameters := {|
    FlatToRiscvDef.FlatToRiscvDef.actname := actname;
    FlatToRiscvDef.FlatToRiscvDef.compile_ext_call := TODO;
    FlatToRiscvDef.FlatToRiscvDef.max_ext_call_code_size := TODO;
    FlatToRiscvDef.FlatToRiscvDef.compile_ext_call_length := TODO;
  |}.

  Instance FlatToRiscv_params: FlatToRiscv.FlatToRiscv.parameters := {|
    FlatToRiscv.FlatToRiscv.def_params := _;
    FlatToRiscv.FlatToRiscv.W := W;
    FlatToRiscv.FlatToRiscv.locals := locals;
    FlatToRiscv.FlatToRiscv.locals_ok := TODO;
    FlatToRiscv.FlatToRiscv.mem := mem;
    FlatToRiscv.FlatToRiscv.mem_ok := TODO;
    FlatToRiscv.FlatToRiscv.actname_eq_dec := actname_eq_dec;
    FlatToRiscv.FlatToRiscv.M := M;
    FlatToRiscv.FlatToRiscv.MM := MM;
    FlatToRiscv.FlatToRiscv.RVM := RVM;
    FlatToRiscv.FlatToRiscv.PR := PR;
    FlatToRiscv.FlatToRiscv.ext_spec := TODO;
    FlatToRiscv.FlatToRiscv.env := TODO;
    FlatToRiscv.FlatToRiscv.env_ok := TODO;
    FlatToRiscv.FlatToRiscv.compile_ext_call_correct := TODO;
    FlatToRiscv.FlatToRiscv.ext_guarantee := TODO;
    FlatToRiscv.FlatToRiscv.ext_guarantee_preservable := TODO;
    FlatToRiscv.FlatToRiscv.go_load := TODO; (* interesting: how to instantiate this one?? *)
    FlatToRiscv.FlatToRiscv.go_store := TODO; (* interesting: how to instantiate this one?? *)
  |}.

  Definition flatten(s: Syntax.cmd): FlatImp.stmt :=
    let ngs: NGstate := freshNameGenState (ExprImp.allVars_cmd s) in
    let (sFlat, ngs') := flattenStmt ngs s in sFlat.

  (* only works if varname=Register *)
  Definition exprImp2Riscv(s: Syntax.cmd): list Instruction :=
    FlatToRiscvDef.compile_stmt iset (flatten s).

  Notation registerset := (@compiler.util.Set.set Register registerSetFunctions).

  Definition riscvRegisters: registerset := compiler.util.Set.of_list (List.map Z.of_nat (List.seq 1 31)).

  (* convention: there's one single result which is put into register $x1 *)
  Definition interesting_alloc(resVar: varname): reg2varMapping := map.put map.empty 1 resVar.

  Definition exprImp2Riscv_with_regalloc(resVar: varname)(s: Syntax.cmd): list Instruction :=
    let oStmt :=
      (register_allocation varname Register funname actname
                           Register0
                           (flatten s)
                           map.empty
                           (interesting_alloc resVar)) in
      match oStmt with
      | Some s => FlatToRiscvDef.compile_stmt iset s
      | None => nil
      end.

  (*
  Lemma putProgram_containsProgram: forall {Bw: BitWidths} s a p (initial: RiscvMachine),
      FlatToRiscv.valid_registers s ->
      FlatToRiscv.compile_stmt LwXLEN SwXLEN s = p ->
      FlatToRiscv.stmt_not_too_big s ->
      regToZ_unsigned a mod 4 = 0 ->
      regToZ_unsigned a + 4 * (Zlength p) <= Memory.memSize initial.(machineMem) ->
      FlatToRiscv.containsProgram
        (putProgram (List.map (fun i => ZToWord 32 (encode i)) p) a initial).(machineMem) p a.
  Proof.
    intros. subst p. unfold putProgram.
    pose proof BitWidths.pow2_wXLEN_4 as X.
    rewrite FlatToRiscv.containsProgram_alt.
    unfold FlatToRiscv.containsProgram', FlatToRiscv.decode_prog, Minimal.putProgram.
    destruct initial as [ [regs pc0 eh] m ].
    simpl in *. split.
    - rewrite Memory.store_word_list_preserves_memSize. assumption.
    - rewrite Memory.load_store_word_list_eq; rewrite? map_Zlength; auto.
      rewrite map_map.
      apply Memory.list_elementwise_same_Z'. intuition idtac.
      (* TODO de-duplicate *)
      + pose proof Memory.map_Znth_error' as P.
        specialize P with (1 := H0).
        destruct P as [ inst [A B] ]. subst e.
        rewrite A. f_equal.
        rewrite uwordToZ_ZToWord.
        rewrite Z.mod_small.
        * symmetry. apply decode_encode.
          eapply compile_stmt_emits_valid; try eassumption.
          Fail exact A.
          Admitted. (*
        * apply encode_range.
      + erewrite map_nth_error by eassumption.
        f_equal.
        rewrite uwordToZ_ZToWord.
        * apply decode_encode.
          eapply compile_stmt_emits_valid; eassumption.
        * apply encode_range.
  Qed.
*)

  Lemma store_word_list_preserves_containsMem: forall offset words mL mH,
      regToZ_unsigned offset + 4 * Zlength words <= Memory.memSize mL ->
      Memory.valid_addr offset 4 (Memory.memSize mL) ->
      FlatToRiscv.mem_inaccessible mH (regToZ_unsigned offset) (4 * Zlength words) ->
      FlatToRiscvInvariants.containsMem mL mH ->
      FlatToRiscvInvariants.containsMem (Memory.store_word_list words offset mL) mH.
  Proof.
    unfold FlatToRiscvInvariants.containsMem. intros.
    specialize (H2 addr v H3).
    rewrite Memory.store_word_list_preserves_memSize.
    intuition idtac.
    unfold FlatToRiscv.mem_inaccessible in *.
    pose proof H3.
    unfold Memory.read_mem in H3.
    destruct_one_match_hyp; try discriminate. clear E.
    unfold FlatToRiscvBitWidthSpecifics.loadWordwXLEN, wXLEN_in_bytes, wXLEN, bitwidth in *.
    (*
    destruct Bw;
      [ rewrite Memory.loadWord_outside_store_word_list
      |  erewrite Memory.loadDouble_outside_store_word_list ];
      eauto; Memory.mem_simpl.
  Qed.
     *)
  Admitted.
  *)
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

  Lemma exprImp2Riscv_correct: forall sH mH instsL initialL (post: trace -> Prop) imemStart,
      ExprImp.cmd_size sH < 2 ^ 7 ->
      enough_registers sH ->
      exprImp2Riscv sH = instsL ->
      (GoFlatToRiscv.program imemStart instsL * eq mH)%sep initialL.(getMem) ->
      Semantics.exec.exec map.empty sH nil mH map.empty (fun t m l => post t) ->
      runsTo (mcomp_sat (run1 iset))
             initialL
             (fun finalL => post finalL.(getLog)).
  Admitted.


  Lemma bw_sim: forall sH mH instsL initialL (postH postL: trace -> Prop) imemStart,
      ExprImp.cmd_size sH < 2 ^ 7 ->
      enough_registers sH ->
      exprImp2Riscv sH = instsL ->
      (GoFlatToRiscv.program imemStart instsL * eq mH)%sep initialL.(getMem) ->
      Semantics.exec.exec map.empty sH nil mH map.empty (fun t m l => postH t) ->
      runsTo (mcomp_sat (run1 iset))
             initialL
             (fun finalL => postL finalL.(getLog)) ->
      (forall t, postL t -> postH t).
  Proof.
    intros.
    pose proof exprImp2Riscv_correct as P.
    specialize (P _ _ _ _ _ _ H H0 H1 H2 H3).

  Abort. (* hopefully we won't need this backwards direction *)


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
