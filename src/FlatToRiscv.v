Require Import compiler.StateMonad.
Require Import compiler.Common.
Require Import compiler.FlatImp.
Require Import compiler.StateCalculus.
Require Import compiler.zcast.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import compiler.Op.
Require Import compiler.ResMonad.
Require Import compiler.Riscv.
Require Import compiler.Machine.

Section FlatToRiscv.

  Context {w: nat}. (* bit width *)
  Context {var: Set}.
  Context {eq_var_dec: DecidableEq var}.
  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.

  Definition var2Register: var -> @Register var := RegS.

  Definition compile_op(res: var)(op: binop)(arg1 arg2: var): list (@Instruction var) :=
    let rd := var2Register res in
    let rs1 := var2Register arg1 in
    let rs2 := var2Register arg2 in
    match op with
    | OPlus => [Add rd rs1 rs2]
    | OMinus => [Sub rd rs1 rs2]
    | OTimes => [Mul rd rs1 rs2]
    | OEq => [Sub rd rs1 rs2; Seqz rd rd]
    | OLt => [Sltu rd rs1 rs2]
    | OAnd => [And rd rs1 rs2]
    end.

  (* using the same names (var) in source and target language *)
  Fixpoint compile_stmt(s: @stmt w var): list (@Instruction var) :=
    match s with
    | SLit x v => [Addi (var2Register x) RegO (zcast 12 v)] (* only works if literal is < 2^12 *)
    | SOp x op y z => compile_op x op y z
    | SSet x y => [Add (var2Register x) RegO (var2Register y)]
    | SIf cond bThen bElse =>
        let bThen' := compile_stmt bThen in
        let bElse' := compile_stmt bElse in
        (* only works if branch lengths are < 2^12 *)
        [Beq (var2Register cond) RegO ($4 ^* $(S (length bThen')))] ++
        bThen' ++
        [Jal RegO ($4 ^* $(length bElse'))] ++
        bElse'
    | SLoop body1 cond body2 =>
        let body1' := compile_stmt body1 in
        let body2' := compile_stmt body2 in
        (* only works if branch lengths are < 2^12 *)
        body1' ++
        [Beq (var2Register cond) RegO ($4 ^* $(S (length body2')))] ++
        body2' ++
        [Jal RegO (wneg ($4 ^* $(S (length body1' + length body2'))))]
    | SSeq s1 s2 => compile_stmt s1 ++ compile_stmt s2
    | SSkip => nil
    end.

  Definition containsProgram(m: RiscvMachine)(program: list (@Instruction var))(offset: word w)
    := forall i inst, nth_error program i = Some inst ->
                      m.(instructionMem) (offset ^+ $4 ^* $i) = inst.

  Definition containsState(m: RiscvMachine)(s: state)
    := forall x v, get s x = Some v -> m.(registers) x = v.

  (*
  Definition containsProgramAndState(m: RiscvMachine)(program: list (@Instruction var))(s: state)
    := containsProgram m program m.(pc) /\ containsState m s.
  *)

  (* TODO define type classes in such a way that this is not needed *)
  Definition myRiscvMachine := @IsRiscvMachine w var _.
  Existing Instance myRiscvMachine.

(* inline because the inverison is already done
  Lemma compile_op_correct: forall x y z fuelH op insts initialH finalH initialL,
    compile_op x op y z = insts ->
    eval_stmt fuelH initialH (SOp x op y z) = Success finalH ->
    containsProgram initialL insts initialL.(pc) ->
    containsState initialL initialH ->
    exists (fuelL: nat) (finalL: RiscvMachine),
      execState (run fuelL) initialL = finalL /\
      containsState finalL finalH.
  Proof.
    introv C EvH Cp Cs.
    destruct fuelH as [|fuelH]; [discriminate|].
    simpl in EvH.
  Abort.
  *)
  
  Axiom wmult_neut_r: forall (sz : nat) (x : word sz), x ^* $0 = $0.

  Require Import lib.LibTactics. (* contains annoying notation which makes Register a keyword *)

  Lemma containsProgram_cons_inv: forall s inst insts offset,
    containsProgram s (inst :: insts) offset ->
    s.(instructionMem) offset = inst /\
    containsProgram s insts (offset ^+ $4).
  Proof.
    introv Cp. unfold containsProgram in Cp. split.
    + specialize (Cp 0). specializes Cp; [reflexivity|].
      rewrite wmult_neut_r in Cp.
      rewrite wplus_comm in Cp. rewrite wplus_unit in Cp.
      assumption.
    + unfold containsProgram.
      intros i inst0 E. specialize (Cp (S i)). simpl in Cp.
      specialize (Cp _ E).
      rewrite <- Cp. f_equal.
      rewrite <- wplus_assoc. f_equal. rewrite (natToWord_S w i).
      replace ($4 ^* ($1 ^+ $i)) with ((($1 ^+ $i) ^* $4): word w) by apply wmult_comm.
      rewrite wmult_plus_distr.
      rewrite wmult_unit.
      f_equal.
      apply wmult_comm.
  Qed.

  Lemma containsProgram_app_inv: forall s insts1 insts2 offset,
    containsProgram s (insts1 ++ insts2) offset ->
    containsProgram s insts1 offset /\
    containsProgram s insts2 (offset ^+ $4 ^* $(length insts1)).
  Proof.
    introv Cp. unfold containsProgram in *. split.
    + intros. apply Cp. rewrite nth_error_app1; [assumption|].
      apply nth_error_Some. intro E. rewrite E in H. discriminate.
    + intros. rewrite <- wplus_assoc.
      do 2 rewrite (wmult_comm $4).
      rewrite <- wmult_plus_distr. rewrite <- wmult_comm.
      rewrite <- natToWord_plus.
      apply Cp.
      rewrite nth_error_app2 by omega.
      replace (length insts1 + i - length insts1) with i by omega.
      assumption.
  Qed.

  Ltac destruct_containsProgram :=
    repeat match goal with
    | Cp: _ |- _ =>
      (apply containsProgram_cons_inv in Cp || apply containsProgram_app_inv in Cp);
      let Cp' := fresh Cp in 
      destruct Cp as [Cp' Cp];
      simpl in Cp'
    | Cp: containsProgram _ [] _ |- _ => clear Cp
    end.

  Lemma containsState_put: forall prog1 prog2 pc1 pc2 initialH initialRegs x v1 v2,
    containsState (mkRiscvMachine prog1 initialRegs pc1) initialH ->
    v1 = v2 ->
    containsState (mkRiscvMachine prog2 
      (fun reg2 : var =>
               if dec (x = reg2)
               then v1
               else initialRegs reg2)
       pc2)
     (put initialH x v2).
  Proof.
    unfold containsState. intros. simpl.
    rewrite get_put in H1. destruct_one_match.
    - inversions H1. reflexivity.
    - simpl in H. apply H. assumption.
  Qed.


  Lemma distr_if_over_app: forall T U P1 P2 (c: sumbool P1 P2) (f1 f2: T -> U) (x: T),
    (if c then f1 else f2) x = if c then f1 x else f2 x.
  Proof. intros. destruct c; reflexivity. Qed.

  Lemma pair_eq_acc: forall T1 T2 (a: T1) (b: T2) t,
    t = (a, b) -> a = fst t /\ b = snd t.
  Proof. intros. destruct t. inversionss. auto. Qed.

  (* alternative way of saying "exists fuel, run fuel initial = final /\ P final" *)
  Inductive runsToSatisfying(initial: @RiscvMachine w var)(P: @RiscvMachine w var -> Prop): Prop :=
    | runsToDone:
       P initial ->
       runsToSatisfying initial P
    | runsToStep:
       runsToSatisfying (execState run1 initial) P ->
       runsToSatisfying initial P.

  Lemma runsToSatisfying_trans: forall P Q initial,
    runsToSatisfying initial P ->
    (forall middle, P middle -> runsToSatisfying middle Q) ->
    runsToSatisfying initial Q.
  Proof.
    introv R1. induction R1; introv R2; [solve [auto]|].
    apply runsToStep. apply IHR1. apply R2.
  Qed.

  Lemma execute_preserves_instructionMem: forall inst initial,
    (snd (execute inst initial)).(instructionMem) = initial.(instructionMem).
  Proof.
    intros. unfold execute.
    repeat (destruct_one_match; simpl; try reflexivity).
  Qed.

  Lemma run1_preserves_instructionMem: forall initial,
    (execState run1 initial).(instructionMem) = initial.(instructionMem).
  Proof.
    intros.
    destruct initial as [initialProg initialRegs initialPc]. simpl.
    unfold execState, StateMonad.put. simpl.
    rewrite execute_preserves_instructionMem.
    reflexivity.
  Qed.

  Lemma runsTo_preserves_instructionMem: forall P initial,
    runsToSatisfying initial P ->
    runsToSatisfying initial
       (fun final => P final /\ final.(instructionMem) = initial.(instructionMem)).
  Proof.
    intros. induction H.
    - apply runsToDone. auto.
    - apply runsToStep. rewrite run1_preserves_instructionMem in IHrunsToSatisfying. assumption.
  Qed.

(*
  (* alternative way of saying "exists fuel, run fuel initial = final /\ P final" *)
  Inductive runsToSatisfying(P: @RiscvMachine w var -> Prop)(initial: @RiscvMachine w var): Prop :=
    | runsToDone:
       P initial ->
       runsToSatisfying P initial
    | runsToStep:
       runsToSatisfying P (execState run1 initial) ->
       runsToSatisfying P initial.

  (* alternative way of saying "exists fuel, run fuel initial = final /\ P final" *)
  Inductive runsToSatisfying(P: @RiscvMachine w var -> Prop):
    forall (initial: @RiscvMachine w var), Prop :=
    | runsToDone: forall initial,
       P initial ->
       runsToSatisfying P initial
    | runsToStep: forall initial, 
       runsToSatisfying P (execState run1 initial) ->
       runsToSatisfying P initial.

  (* alternative way of saying "exists fuel, run fuel initial = final /\ P final" *)
  Inductive runsToSatisfying:
    forall (initial: @RiscvMachine w var) (P: @RiscvMachine w var -> Type), Type :=
    | runsToDone: forall initial P,
       P initial ->
       runsToSatisfying initial P
    | runsToStep: forall initial P, 
       runsToSatisfying (execState run1 initial) P ->
       runsToSatisfying initial P.
*)

  Axiom fits_imm12: forall v: word w, wordToNat v < pow2 12.

  Axiom compile_fits_imm12: forall s, 4 * S (length (compile_stmt s)) < pow2 12.

  Lemma regs_overwrite: forall x v1 v2 (initialRegs: var -> word w),
      (fun reg2 : var => if dec (x = reg2) then v2 else
                         if dec (x = reg2) then v1 else
                         initialRegs reg2)
    = (fun reg2 : var => if dec (x = reg2) then v2 else initialRegs reg2).
  Proof.
    intros.
    extensionality reg2. destruct_one_match; reflexivity.
  Qed.

  Lemma reduce_eq_to_sub_and_lt: forall (y z: word w) {T: Type} (thenVal elseVal: T),
    (if wlt_dec (y ^- z) $1 then thenVal else elseVal) =
    (if weq y z             then thenVal else elseVal).
  Proof.
  Admitted.

  Ltac simpl_run1 :=
         cbv [run1 execState StateMonad.put execute instructionMem registers 
             pc getPC loadInst setPC getRegister setRegister myRiscvMachine IsRiscvMachine gets
             StateMonad.get Return Bind State_Monad ].

  Lemma compile_stmt_correct_aux: forall fuelH s insts initialH finalH initialL finalPc,
    compile_stmt s = insts ->
    eval_stmt fuelH initialH s = Success finalH ->
    containsProgram initialL insts initialL.(pc) ->
    containsState initialL initialH ->
    finalPc = initialL.(pc) ^+ $ (4) ^* $ (length insts) ->
    runsToSatisfying initialL (fun finalL => containsState finalL finalH /\
       finalL.(pc) = finalPc).
  Proof.
    induction fuelH; [intros; discriminate |].
    introv C EvH Cp Cs PcEq.
    invert_eval_stmt.
    - subst. destruct_containsProgram.
      destruct initialL as [initialProg initialRegs initialPc].
      apply runsToStep. apply runsToDone.
      simpl_run1.
      simpl in Cp0.
      rewrite Cp0. simpl.
      rewrite <- (wmult_comm $1). rewrite wmult_unit. refine (conj _ eq_refl).
      eapply containsState_put; [eassumption|].
      unfold zcast.
      rewrite wordToNat_natToWord_idempotent'.
      + rewrite natToWord_wordToNat. apply wplus_unit.
      + apply fits_imm12.
    - simpl in C. subst.
      destruct initialL as [initialProg initialRegs initialPc].
      simpl in Cp.
      pose proof Cs as Cs'.
      unfold containsState in Cs. simpl in Cs.
      rename H into Gy, H0 into Gz. apply Cs in Gy. apply Cs in Gz.
      subst x0 x1.
      apply runsToStep.
      simpl_run1.
      destruct op eqn: EOp;
      destruct_containsProgram;
      repeat match goal with
      | E: ?t = ?rhs |- context [?t] => rewrite E
      end;
      simpl;
      match goal with
      | _: op = OEq |- _ => idtac
      | _ => solve [
          apply runsToDone;
          rewrite <- (wmult_comm $1); rewrite wmult_unit; refine (conj _ eq_refl);
          eapply containsState_put; [eassumption|reflexivity]]
      end.
      apply runsToStep.
      simpl_run1.
      progress rewrite Cp1. simpl.
      destruct (dec (x = x)); [|contradiction].
      rewrite regs_overwrite.
      apply runsToDone.
      rewrite <- natToWord_mult. rewrite <- wplus_assoc. rewrite <- natToWord_plus.
      refine (conj _ eq_refl).
      eapply containsState_put; [ eassumption |].
      apply reduce_eq_to_sub_and_lt.
    - simpl in C. subst.
      destruct initialL as [initialProg initialRegs initialPc].
      destruct_containsProgram.
      apply runsToStep.
      simpl_run1.
      rewrite Cp0.
      apply runsToDone. simpl.
      rewrite <- (wmult_comm $1). rewrite wmult_unit. refine (conj _ eq_refl).
      eapply containsState_put; [ eassumption |].
      unfold containsState in Cs. simpl in Cs.
      erewrite Cs by eassumption.
      apply wplus_unit.
    - simpl in C. subst.
      destruct_containsProgram.
      apply runsToStep.
      destruct initialL as [initialProg initialRegs initialPc]; simpl in *.
      simpl_run1.
      rewrite Cp0. simpl.
      pose proof Cs as Cs'.
      unfold containsState in Cs'. simpl in Cs'.
      apply Cs' in H. subst x.
      destruct (weq (initialRegs cond) $ (0)); [contradiction|]. simpl.
      match goal with
      | |- runsToSatisfying ?st _ => specialize IHfuelH with (initialL := st); simpl in IHfuelH
      end.
      specialize (IHfuelH s1).
      specializes IHfuelH; [reflexivity|eassumption|eassumption|eassumption|reflexivity|idtac].
      apply runsTo_preserves_instructionMem in IHfuelH. simpl in IHfuelH.
      apply (runsToSatisfying_trans _ _ _ IHfuelH).
      intros middleL [[Cs2 F] E].
      destruct middleL as [middleProg middleRegs middlePc]. simpl in *. subst middleProg middlePc.
      apply runsToStep.
      simpl_run1.
      rewrite Cp2. simpl.
      apply runsToDone.
      refine (conj Cs2 _).
      rewrite <- ? wplus_assoc.
      f_equal. rewrite app_length. simpl.
      clear.
      rewrite <- ? natToWord_mult.
      unfold zcast.
      rewrite <- ? natToWord_plus.
      f_equal.
      rewrite wordToNat_natToWord_idempotent'; [omega|].
      pose proof (compile_fits_imm12 s2). unfold pow2 in *. omega.
    - simpl in C. subst.
      destruct_containsProgram.
      apply runsToStep.
      destruct initialL as [initialProg initialRegs initialPc]; simpl in *.
      simpl_run1.
      rewrite Cp0. simpl.
      pose proof Cs as Cs'.
      unfold containsState in Cs'. simpl in Cs'.
      apply Cs' in H. rewrite H.
      destruct (weq $0 $0); [|contradiction]. simpl.
      eapply (IHfuelH s2); [reflexivity|eassumption|idtac|eassumption|idtac].
      + match goal with
        | H: containsProgram ?st1 ?insts1 ?ofs1 |- containsProgram ?st2 ?insts2 ?ofs2 =>
            unify insts1 insts2;
            assert (ofs1 = ofs2) as OfsEq
        end. {
          simpl.
          unfold zcast. rewrite <- ? natToWord_mult.
          rewrite wordToNat_natToWord_idempotent' by (apply compile_fits_imm12).
          rewrite <- ? wplus_assoc.
          f_equal. f_equal. rewrite <- natToWord_plus. f_equal. omega.
        }
        rewrite <- OfsEq. assumption.
      + simpl.
        rewrite <- ? wplus_assoc. f_equal.
        rewrite app_length. simpl.
        clear.
        rewrite <- ? natToWord_mult.
        unfold zcast.
        rewrite <- ? natToWord_plus.
        f_equal.
        rewrite wordToNat_natToWord_idempotent'; [omega|].
        apply compile_fits_imm12.
    - simpl in C. subst.
      destruct_containsProgram.
      destruct initialL as [initialProg initialRegs initialPc]; simpl in *.
      match goal with
      | |- runsToSatisfying ?st _ => specialize IHfuelH with (initialL := st); simpl in IHfuelH
      end.
      specialize (IHfuelH s1).
      specializes IHfuelH; [reflexivity|eassumption|eassumption|eassumption|reflexivity|idtac].
      apply runsTo_preserves_instructionMem in IHfuelH. simpl in IHfuelH.
      apply (runsToSatisfying_trans _ _ _ IHfuelH).
      intros middleL [[Cs2 F] E].
      destruct middleL as [middleProg middleRegs middlePc]. simpl in *. subst middleProg middlePc.
      apply runsToStep.
      simpl_run1.
      rewrite Cp1. simpl.
      pose proof Cs2 as Cs2'.
      unfold containsState in Cs2'. simpl in Cs2'.
      apply Cs2' in H0. rewrite H0.
      destruct (weq $0 $0); [|contradiction]. simpl.
      apply runsToDone.
      refine (conj Cs2 _).
      clear.
      rewrite <- ? wplus_assoc.
      f_equal.
      repeat (rewrite app_length; simpl).
      rewrite <- ? natToWord_mult.
      unfold zcast.
      rewrite <- ? natToWord_plus.
      f_equal.
      rewrite wordToNat_natToWord_idempotent'; [omega|].
      apply compile_fits_imm12.
    - admit. (* TODO SLoop *)
    - simpl in C. subst. apply containsProgram_app_inv in Cp. destruct Cp as [Cp1 Cp2].
      rename x into middleH.
      eapply runsToSatisfying_trans.
      + specialize (IHfuelH s1).
        specializes IHfuelH; [reflexivity|eassumption|eassumption|eassumption|reflexivity|idtac].
        apply runsTo_preserves_instructionMem in IHfuelH.
        apply IHfuelH.
      + simpl. intros middleL [[Cs2 F] E]. rewrite <- F in Cp2.
        eapply (IHfuelH s2); [reflexivity|eassumption|idtac|eassumption|idtac].
        * unfold containsProgram in *. rewrite E. assumption.
        * rewrite F. rewrite <- ? wplus_assoc. f_equal.
          rewrite ! (wmult_comm $4).
          rewrite <- wmult_plus_distr.
          rewrite app_length.
          rewrite natToWord_plus.
          reflexivity.
    - simpl in C. subst. apply runsToDone. split; [assumption|].
      simpl. rewrite <- natToWord_mult. simpl. rewrite wplus_comm, wplus_unit. 
      reflexivity.
  Qed.

End FlatToRiscv.
