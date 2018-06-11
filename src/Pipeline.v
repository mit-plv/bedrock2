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

  Lemma mod_add_r: forall a b,
      b <> 0 ->
      (a + b) mod b = a mod b.
  Proof.
    intros. rewrite <- Nat.add_mod_idemp_r by omega.
    rewrite Nat.mod_same by omega.
    rewrite Nat.add_0_r.
    reflexivity.
  Qed.

  Arguments mult: simpl never.

  (* TODO put into Memory.v *)
  Lemma store_word_list_preserves_memSize_aux: forall sz (m: mem wXLEN) a l,
      length l = sz ->
      Memory.memSize (Memory.store_word_list l a m) = Memory.memSize m.
  Proof.
    induction sz; intros; subst; destruct l; simpl in *; try congruence.
    inversions H.
    rewrite IHsz by reflexivity.
    apply Memory.storeWord_preserves_memSize.
  Qed.

  Lemma store_word_list_preserves_memSize: forall (m: mem wXLEN) l a,
      Memory.memSize (Memory.store_word_list l a m) = Memory.memSize m.
  Proof.
    intros. eapply store_word_list_preserves_memSize_aux. reflexivity.
  Qed.

  Lemma loadWord_before_store_word_list: forall sz (m: mem wXLEN) l (a1 a2: word wXLEN),
      length l = sz ->
      #a1 + 4 <= #a2 ->
      #a2 + 4 * sz <= (Memory.memSize m) ->
      Memory.valid_addr a1 4 (Memory.memSize m) ->
      Memory.valid_addr a2 4 (Memory.memSize m) ->
      Memory.loadWord (Memory.store_word_list l a2 m) a1  = Memory.loadWord m a1.
  Proof.
    induction sz; intros; subst; destruct l; simpl in *; try congruence.
    inversions H.
    pose proof (Memory.memSize_bound m).
    destruct l.
    - simpl. apply Memory.loadStoreWord_ne; try assumption.
      intro C. subst. omega.
    - simpl in H1. rewrite IHsz.
      + apply Memory.loadStoreWord_ne; try assumption.
        intro C. subst. omega.
      + reflexivity.
      + pose proof FlatToRiscv.pow2_wXLEN_4.
        unfold Memory.valid_addr in *. intuition idtac.
        rewrite wordToNat_wplus'; rewrite wordToNat_natToWord_idempotent'; try omega.
      + simpl. rewrite Memory.storeWord_preserves_memSize. 
        rewrite wordToNat_wplus';
          rewrite wordToNat_natToWord_idempotent' by (apply FlatToRiscv.pow2_wXLEN_4);
          intuition (try omega).
      + rewrite Memory.storeWord_preserves_memSize. assumption.
      + rewrite Memory.storeWord_preserves_memSize.
        unfold Memory.valid_addr in *.
        rewrite wordToNat_wplus';
          rewrite wordToNat_natToWord_idempotent' by (apply FlatToRiscv.pow2_wXLEN_4);
          rewrite? mod_add_r by omega;  
          intuition (try omega).
  Qed.

  Local Arguments Nat.modulo: simpl never.

  Lemma load_store_word_list_eq: forall l (m: mem wXLEN) ll a1 a2,
      a2 = a1 ->
      ll = length l ->
      #a1 mod 4 = 0 ->
      #a1 + 4 * (length l) <= Memory.memSize m ->
      Memory.load_word_list (Memory.store_word_list l a1 m) a2 ll = l.
  Proof.
    induction l; intros; subst; simpl in *.
    - reflexivity.
    - pose proof (Memory.memSize_bound m).
      pose proof FlatToRiscv.pow2_wXLEN_4.
      destruct l.
      + simpl. f_equal. apply Memory.loadStoreWord_eq; try reflexivity.
        unfold Memory.valid_addr. omega.
      + f_equal.
        * erewrite loadWord_before_store_word_list; try reflexivity.
          { apply Memory.loadStoreWord_eq; try reflexivity.
            unfold Memory.valid_addr. omega. }
          { simpl in H2. rewrite wordToNat_wplus';
            rewrite wordToNat_natToWord_idempotent' by assumption;
            omega. }
          { simpl in *.
            rewrite Memory.storeWord_preserves_memSize.
            rewrite wordToNat_wplus';
            rewrite wordToNat_natToWord_idempotent' by assumption;
            omega. }
          { rewrite Memory.storeWord_preserves_memSize.
            unfold Memory.valid_addr. omega. }
          { rewrite Memory.storeWord_preserves_memSize.
            simpl in H2.
            unfold Memory.valid_addr.
            rewrite wordToNat_wplus';
              rewrite wordToNat_natToWord_idempotent' by assumption;
              rewrite? mod_add_r by omega;  
              intuition (try omega).
          }
        * rewrite IHl; try reflexivity.
          { simpl in H2.
            rewrite wordToNat_wplus';
              rewrite wordToNat_natToWord_idempotent' by assumption;
              rewrite? mod_add_r by omega;  
              intuition (try omega). }
          { simpl in H2.
            rewrite Memory.storeWord_preserves_memSize.
            simpl.
            rewrite wordToNat_wplus';
              rewrite wordToNat_natToWord_idempotent' by assumption;
              rewrite? mod_add_r by omega;  
              intuition (try omega). }
  Qed.

  Lemma list_elementwise_same': forall (A : Type) (l1 l2 : list A),
      (forall i e, nth_error l1 i = Some e <-> nth_error l2 i = Some e) ->
      l1 = l2.
  Proof.
    intros.
    apply Memory.list_elementwise_same.
    intro i.
    destruct (nth_error l1 i) as [e1|] eqn: E1.
    - edestruct H as [A1 A2]. specialize (A1 E1). congruence.
    - destruct (nth_error l2 i) as [e2|] eqn: E2; [|reflexivity].
      edestruct H as [A1 A2]. specialize (A2 E2). congruence.
  Qed.

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
    rewrite FlatToRiscv.containsProgram_alt.
    unfold FlatToRiscv.containsProgram', FlatToRiscv.decode_prog, putProgram.
    destruct initial as [[regs pc0 eh] m].
    simpl in *. split.
    - rewrite store_word_list_preserves_memSize. assumption.
    - rewrite load_store_word_list_eq; rewrite? map_length; auto.
      rewrite map_map.
      apply list_elementwise_same'. intuition idtac.
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
        replace Utility.rem with Utility.remu by admit. (* TODO *)
        autorewrite with alu_defs.
        rewrite FlatToRiscv.four_def.
        destruct_one_match; [exfalso|reflexivity].
        admit. (* TODO mod 4 stuff *)
      + unfold translate, DefaultRiscvState, default_translate.
        intros.
        replace Utility.rem with Utility.remu by admit. (* TODO *)
        unfold Utility.eight.
        autorewrite with alu_defs.
        rewrite FlatToRiscv.four_def.
        destruct_one_match; [exfalso|reflexivity].
        admit. (* TODO mod 8 stuff *)
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
