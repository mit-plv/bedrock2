Require Import Coq.Lists.List.
Import ListNotations.
Require Import lib.LibTacticsMin.
Require Import bbv.Word.
Require Import compiler.Decidable.
Require Import compiler.Op.
Require Import compiler.ResMonad.
Require        compiler.ExprImp.
Require Import compiler.FlattenExpr.
Require        compiler.FlatImp.
Require        compiler.FlatToRiscv.
Require Import riscv.Riscv.
Require Import riscv.util.Monads.
Require Import compiler.runsToSatisfying.
Require Import compiler.MyOmega.
Require Import bbv.DepEqNat.
Require Import compiler.NameGen.
Require Import compiler.Common.
Require Import riscv.RiscvBitWidths.
Require Import compiler.NameWithEq.
Require Import riscv.encode.Encode.
Require Import riscv.AxiomaticRiscv.
Require Import riscv.proofs.DecodeEncode.
Require Import riscv.proofs.EncodeBound.
Require Import compiler.EmitsValid.

Section Pipeline.

  Context {Bw: RiscvBitWidths}.

  Context {state: Type}.
  Context {stateMap: Map state Register (word wXLEN)}.

  Context {mem: nat -> Set}.
  Context {IsMem: Memory.Memory (mem wXLEN) wXLEN}.
  
  Local Notation RiscvMachine := (@RiscvMachine Bw (mem wXLEN) state).
  Context {RVM: RiscvProgram (OState RiscvMachine) (word wXLEN)}.

  Existing Instance riscv.Program.DefaultRiscvState.
  
  Existing Instance FlatToRiscv.State_is_RegisterFile.
  
  Context {RVAX: @AxiomaticRiscv Bw state FlatToRiscv.State_is_RegisterFile (mem wXLEN) _ RVM}.

  Definition var := Register.

  Context {vars: Type}.
  Context {varset: set vars var}.
  Context {NGstate: Type}.
  Context {NG: NameGen var vars NGstate}.

  
  Definition exprImp2Riscv(s: ExprImp.stmt): list Instruction :=
    let ngs := freshNameGenState (ExprImp.allVars_stmt s) in
    let (sFlat, ngs') := flattenStmt ngs s in
    FlatToRiscv.compile_stmt sFlat.

  Definition evalH := ExprImp.eval_stmt.

  Definition evalL(fuel: nat)(insts: list Instruction)(initial: RiscvMachine): RiscvMachine :=
    execState (run fuel) (putProgram (map (fun i => ZToWord 32 (encode i)) insts) $0 initial).

  Lemma wXLEN_32: 32 <= wXLEN.
  Proof.
    clear. unfold wXLEN, bitwidth. destruct Bw; omega.
  Qed.

  Lemma wXLEN_cases: wXLEN = 32 \/ wXLEN = 64.
  Proof.
    clear. unfold wXLEN, bitwidth. destruct Bw; omega.
  Qed.

  Local Arguments mult: simpl never.

  Lemma putProgram_containsProgram: forall s a p (initial: RiscvMachine),
      FlatToRiscv.valid_registers s ->
      FlatToRiscv.compile_stmt s = p ->
      EmitsValid.stmt_not_too_big s ->
      #a mod 4 = 0 ->
      #a + 4 * (length p) <= Memory.memSize initial.(machineMem) ->
      FlatToRiscv.containsProgram
        (putProgram (map (fun i => ZToWord 32 (encode i)) p) a initial).(machineMem) p a.
  Proof.  
    intros. subst.
    pose proof RiscvBitWidths.pow2_wXLEN_4 as X.
    rewrite FlatToRiscv.containsProgram_alt.
    unfold FlatToRiscv.containsProgram', FlatToRiscv.decode_prog, putProgram.
    destruct initial as [[regs pc0 eh] m].
    simpl in *. split.
    - rewrite Memory.store_word_list_preserves_memSize. assumption.
    - rewrite Memory.load_store_word_list_eq; rewrite? map_length; auto.
      rewrite map_map.
      apply Memory.list_elementwise_same'. intuition idtac.
      (* TODO de-duplicate *)
      + pose proof Memory.map_nth_error' as P.
        specialize P with (1 := H0).
        destruct P as [ inst [A B] ]. subst e.
        rewrite A. f_equal.
        rewrite uwordToZ_ZToWord.
        * symmetry. apply decode_encode.
          eapply compile_stmt_emits_valid; eassumption.
        * apply encode_range.
      + erewrite map_nth_error by eassumption.
        f_equal.
        rewrite uwordToZ_ZToWord.
        * apply decode_encode.
          eapply compile_stmt_emits_valid; eassumption.
        * apply encode_range.
  Qed.

  Lemma weqb_false_iff: forall (sz : nat) (x y : word sz), weqb x y = false <-> x <> y.
  Proof.
    intros.
    pose proof (weqb_true_iff x y).
    destruct (weqb x y) eqn: E; intuition congruence.
  Qed.

  (* TODO rename pow2_wXLEN_4 like this *)
  Lemma eight_lt_pow2_wXLEN: 8 < pow2 wXLEN.
  Proof.
    unfold wXLEN, bitwidth. destruct Bw;
      do 3 rewrite pow2_S;
      change 8 with (2 * (2 * (2 * 1))) at 1;
      (repeat apply mult_lt_compat_l; [ | repeat constructor ..]);
      apply one_lt_pow2.
  Qed.
  
  (* We could also say something about the memory, but then the statement becomes more complex.
     And note that the register we look at could contain any value loaded from the memory. *)
  Lemma exprImp2Riscv_correct: forall sH initialL instsL fuelH finalH initialMemH finalMemH,
    ExprImp.stmt_size sH < 2 ^ 14 ->
    exprImp2Riscv sH = instsL ->
    4 * length instsL <= Memory.memSize initialL.(machineMem) ->
    evalH empty fuelH empty initialMemH sH = Some (finalH, finalMemH) ->
    FlatToRiscv.mem_inaccessible initialMemH 0 (4 * length instsL) ->
    exists fuelL,
      forall resVar res,
      get finalH resVar = Some res ->
      getReg (evalL fuelL instsL initialL).(core).(registers) resVar = res.
  Proof.
    introv B C MB EvH Ina.
    unfold exprImp2Riscv in C.
    destruct_one_match_hyp.
    unfold evalH in EvH.
    pose proof flattenStmt_correct as P.
    specialize (P fuelH sH s initialMemH finalH finalMemH).
    destruct P as [fuelM [finalM [EvM GM]]].
    - unfold ExprImp2FlatImp. rewrite E. reflexivity.
    - unfold evalH. apply EvH.
    - pose proof  FlatToRiscv.compile_stmt_correct as P.
      specialize P with (imemStart := $0).
      let r := eval unfold evalL in (evalL 0 instsL initialL) in
          match r with
          | execState _ ?x => specialize P with (initialL := x)
          end.
      edestruct P as [fuelL [P1 P2]]; clear P.
      + unfold translate, DefaultRiscvState, default_translate.
        intros.
        autorewrite with alu_defs.
        (* TODO all of this should be something like autorewrite in * *)
        destruct_one_match; [exfalso|reflexivity].
        apply Bool.negb_true_iff in E0.
        apply weqb_false_iff in E0.
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
        pose proof eight_lt_pow2_wXLEN as Q.
        rewrite <- (wordToNat_natToWord_idempotent' wXLEN Q) in H.
        rewrite <- wordToNat_mod in H.
        * apply wordToNat_zero in H. contradiction.
        * apply natToWord_nzero; omega.
      + eassumption.
      + unfold FlatToRiscv.stmt_not_too_big.
        pose proof @flattenStmt_size as D1.
        specialize (D1 _ _ _ _ _ _ _ _ _ _ E).
        clear -B D1.
        change 20 with (16 + 4).
        rewrite Nat.pow_add_r.
        apply Nat.mul_lt_mono_pos_r; [ simpl; omega | ].
        change 16 with (2 + 14).
        rewrite Nat.pow_add_r.
        change (2 ^ 2) with 4.
        omega.
      + admit. (* TODO valid_registers *)
      + rewrite roundTrip_0. reflexivity.
      + eassumption.
      + admit. (* TODO containsMem! *)
      + apply putProgram_containsProgram with (s := s).
        * (* TODO valid_registers *)
          admit.
        * assumption.
        * (* TODO stmt_not_too_big *)
          admit.
        * rewrite roundTrip_0. reflexivity.
        * rewrite roundTrip_0. rewrite Nat.add_0_l. assumption.
      + reflexivity.
      + simpl. rewrite wplus_unit. reflexivity.
      + rewrite roundTrip_0. assumption.
      + exists fuelL. intros.
        unfold getReg, FlatToRiscv.State_is_RegisterFile.
        unfold StateCalculus.extends in P1.
        unfold evalL.
        erewrite P1; try reflexivity.
        apply GM. exact H.
  Admitted.

End Pipeline.
