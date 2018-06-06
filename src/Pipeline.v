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

Section Pipeline.

  Context {Bw: RiscvBitWidths}.

  Context {state: Type}.
  Context {stateMap: Map state Register (word wXLEN)}.

  Context {mem: nat -> Set}.
  Context {IsMem: Memory.Memory (mem wXLEN) wXLEN}.
  
  Local Notation RiscvMachine := (@RiscvMachine Bw (mem wXLEN) state).
  Context {RVM: RiscvProgram (OState RiscvMachine) (word wXLEN)}.

  (* assumes generic translate and raiseException functions *)
  Context {RVS: @RiscvState (OState RiscvMachine) (word wXLEN) _ _ RVM}.  

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
    execState (run fuel) (putProgram (map (fun i => ZToWord 32 (encode i)) insts) initial).

  Lemma wXLEN_32: 32 <= wXLEN.
  Proof.
    clear. unfold wXLEN, bitwidth. destruct Bw; omega.
  Qed.

  Lemma wXLEN_cases: wXLEN = 32 \/ wXLEN = 64.
  Proof.
    clear. unfold wXLEN, bitwidth. destruct Bw; omega.
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
    rewrite IHsz.
    - apply Memory.loadStoreWord_ne; try assumption.
      intro C. subst. omega.
    - reflexivity.
    - pose proof FlatToRiscv.pow2_wXLEN_4.
      unfold Memory.valid_addr in *. intuition idtac.
      rewrite wordToNat_wplus'; rewrite wordToNat_natToWord_idempotent'; try omega.
      (* TODO similar to containsProgram stuff *)
      admit.
    - admit.
    - rewrite Memory.storeWord_preserves_memSize. assumption.
    - rewrite Memory.storeWord_preserves_memSize. (* TODO *) admit.
  Admitted.

  Lemma loadWord_store_word_list: forall i (m: mem wXLEN) l a,
      0 <= i < length l ->
      Memory.valid_addr a 4 (Memory.memSize m) ->
      Memory.loadWord (Memory.store_word_list l a m) (a ^+ $(4 * i))  = nth i l $0.
  Proof.
    induction i; intros; destruct l; simpl in *.
    - exfalso. omega.
    - erewrite loadWord_before_store_word_list.
      + apply Memory.loadStoreWord_eq.
        * assumption.
        * (* TODO make FlatToRiscv.solve_word_eq available *) admit.
      + reflexivity.
      + admit.
      + (* TODO needs more hyps *) admit.
      + rewrite Memory.storeWord_preserves_memSize. admit.
      + admit.
    - exfalso. omega.
    - replace (a ^+ $ (4 * S i)) with ((a ^+ $4) ^+ $(4 * i)) by admit.
      rewrite IHi.
      + reflexivity.
      + omega.
      + rewrite Memory.storeWord_preserves_memSize. admit.
  Admitted.

  Lemma putProgram_containsProgram: forall p (initial: RiscvMachine),
    4 * (length p) <= Memory.memSize initial.(machineMem) ->
    FlatToRiscv.containsProgram
      (putProgram (map (fun i : Instruction => ZToWord 32 (encode i)) p) initial).(machineMem) p $0.
  Proof.  
    intros. unfold FlatToRiscv.containsProgram, putProgram.
    intros.
    destruct initial as [[regs pc0 eh] m].
    rewrite roundTrip_0. simpl in *. split.
    - rewrite store_word_list_preserves_memSize. assumption.
    - intros.
      unfold FlatToRiscv.ldInst.
      rewrite loadWord_store_word_list.
      + remember (fun i0 : Instruction => ZToWord 32 (encode i0)) as f.
        replace (natToWord 32 0) with (f (InvalidInstruction 0)) by (subst; reflexivity).
        rewrite map_nth.
        erewrite nth_error_nth by eassumption.
        subst f.
        rewrite wordToZ_ZToWord.
        * apply decode_encode.
          unfold verify.
          (* TODO argue that inst was emitted by compiler and therefore respects imm bounds *)
          admit.
        * (* TODO argue that inst was emitted by compiler and therefore is 32 bits *)
          admit.
      + assert (i < length p). {
          apply nth_error_Some. intro. congruence.
        }
        rewrite map_length.
        omega.
      + unfold Memory.valid_addr.
        rewrite roundTrip_0. simpl.
        destruct p; simpl in *.
        * exfalso. eapply FlatToRiscv.nth_error_nil_Some. eassumption.
        * omega.
  Admitted.

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
      edestruct P as [fuelL [P1 P2]].
      + admit. (* TODO translate_id *)
      + admit. (* TODO translate_id *)
      + eassumption.
      + unfold FlatToRiscv.stmt_not_too_big.
        pose proof @flattenStmt_size as D1.
        specialize (D1 _ _ _ _ _ _ _ _ _ _ _ _ E).
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
      + apply putProgram_containsProgram.
        assumption.
      + reflexivity.
      + simpl. rewrite wplus_unit. reflexivity.
      + rewrite roundTrip_0. assumption.
      + exists fuelL. intros.
        clear P.
        unfold getReg, FlatToRiscv.State_is_RegisterFile.
        unfold StateCalculus.extends in P1.
        unfold evalL.
        erewrite P1; try reflexivity.
        apply GM. exact H.
  Admitted.

End Pipeline.
