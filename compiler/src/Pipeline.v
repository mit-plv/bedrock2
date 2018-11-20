Require Export Coq.Lists.List.
Export ListNotations.
Require Export lib.LibTacticsMin.
Require Export riscv.util.Word.
Require Export compiler.Decidable.
Require Export compiler.Op.
Require        compiler.ExprImp.
Require Export compiler.FlattenExpr.
Require        compiler.FlatImp.
Require        compiler.FlatToRiscv.
Require Export riscv.Decode.
Require Export riscv.Program.
Require Export riscv.Run.
Require Export riscv.Minimal.
Require Export riscv.util.Monads.
Require Import compiler.runsToSatisfying.
Require Import compiler.util.MyOmega.
Require Import Coq.micromega.Lia.
Require Export bbv.DepEqNat.
Require Export compiler.NameGen.
Require Export compiler.util.Common.
Require Export riscv.util.BitWidths.
Require Export compiler.Decidable.
Require Export riscv.Encode.
Require Export riscv.AxiomaticRiscv.
Require Export riscv.proofs.DecodeEncode.
Require Export riscv.proofs.EncodeBound.
Require Export compiler.EmitsValid.
Require Export compiler.RegAlloc3.
Require compiler.util.List_Map.
Require Import riscv.Utility.
Require Export riscv.Memory.
Require Export riscv.InstructionCoercions.
Require Import compiler.Basic32Semantics. (* TODO don't fix bitwidth here *)
Require Import riscv.MachineWidth32.

Open Scope Z_scope.

Section Pipeline.

  Notation mword := (word 32).
  Context {stateMap: MapFunctions Register mword}.
  Notation state := (map Register mword).

  Context {mem: Set}.
  Context {IsMem: Memory.Memory mem mword}.

  Local Notation RiscvMachine := (@RiscvMachine mword mem state).
  Context {RVM: RiscvProgram (OState RiscvMachine) mword}.

  Existing Instance riscv.Program.DefaultRiscvState.

  Existing Instance FlatToRiscv.State_is_RegisterFile.

  Context {RVAX: @AxiomaticRiscv mword _ state FlatToRiscv.State_is_RegisterFile mem _ RVM}.

  Variable LwXLEN: Register -> Register -> Z -> Instruction.

  Variable SwXLEN: Register -> Register -> Z -> Instruction.

  Context {BWS: FlatToRiscvBitWidthSpecifics.FlatToRiscvBitWidthSpecifics mword mem}.
  Context {BWSP: FlatToRiscvBitWidthSpecificProofs.FlatToRiscvBitWidthSpecificProofs mword mem}.

  Definition var := Register.
  Definition func := Empty_set.

  Context {varset: SetFunctions var}.
  Notation vars := (set var).
  Context {NGstate: Type}.
  Context {NG: NameGen var NGstate}.

  Definition flatten(s: Syntax.cmd): FlatImp.stmt var func :=
    let ngs: NGstate := freshNameGenState (ExprImp.allVars_cmd s) in
    let (sFlat, ngs') := flattenStmt id ngs s in sFlat.

  Instance annoying_instance: MapFunctions func
   (list var *
    list var *
    Syntax.cmd).
  Admitted.

  Instance annoying_instance': MapFunctions func
   (list var *
    list var *
    @FlatImp.stmt var func).
  Admitted.

  Definition exprImp2Riscv(s: Syntax.cmd): list Instruction :=
    FlatToRiscv.compile_stmt LwXLEN SwXLEN (flatten s).

  Notation registerset := (@set Register
               (@map_range_set var Register (List_Map.List_Map _ _))).

  Definition riscvRegisters: registerset := of_list (List.map Z.of_nat (List.seq 1 31)).

  (* convention: there's one single result which is put into register $x1 *)
  Definition interesting_alloc(resVar: var): map var var := put empty_map resVar resVar.

  Definition exprImp2Riscv_with_regalloc(resVar: var)(s: Syntax.cmd): list Instruction :=
    let oStmt :=
      (register_allocation var var func
                           Register0
                           riscvRegisters
                           (flatten s)
                           empty_map
                           (interesting_alloc resVar)) in
      match oStmt with
      | Some s => FlatToRiscv.compile_stmt LwXLEN SwXLEN s
      | None => nil
      end.

  Definition evalH := @ExprImp.eval_cmd _ _ _ _.

  Definition evalL{B: BitWidths}(fuel: nat)(insts: list Instruction)(initial: RiscvMachine): RiscvMachine :=
    execState (run fuel) (putProgram (List.map (fun i => ZToWord 32 (encode i)) insts) (ZToReg 0) initial).

  Lemma wXLEN_32{Bw: BitWidths}: (32 <= wXLEN)%nat.
  Proof.
    clear. unfold wXLEN, bitwidth. destruct Bw; omega.
  Qed.

  Lemma wXLEN_cases{Bw: BitWidths}: (wXLEN = 32 \/ wXLEN = 64)%nat.
  Proof.
    clear. unfold wXLEN, bitwidth. destruct Bw; omega.
  Qed.

  Local Arguments mult: simpl never.

  (*
  Definition putProgram(p: list Instruction)(a: mword)(initial: RiscvMachine): RiscvMachine :=
    putProgram (List.map (fun i => ZToWord 32 (encode i)) p) a initial.
  *)
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

  Definition enough_registers(s: Syntax.cmd): Prop :=
    FlatToRiscv.valid_registers (flatten s).

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
      (* TODO ZName.ZName vs Name mismatch
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
  Admitted.

End Pipeline.
