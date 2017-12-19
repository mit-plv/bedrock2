Require Import lib.LibTacticsMin.
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
Require Import Coq.Program.Tactics.

Section FlatToRiscv.

  Context {wlit: nat}. (* bit width of literals *)
  Context {wdiff: nat}. (* bit width difference between literals and words *)
  Notation w := (wlit + wdiff).
  Context {wlit_eq : wlit = 12}.
  Context {w_lbound: w >= 20}.
  Context {var: Set}.
  Context {eq_var_dec: DecidableEq var}.
  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.

  Definition var2Register: var -> @Register var := RegS.

  Definition compile_op(res: var)(op: binop)(arg1 arg2: var): list (@Instruction wlit var) :=
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

  Definition signed_lit_to_word(v: word wlit): word w := nat_cast word eq_refl (sext v wdiff).

  Definition signed_jimm_to_word(v: word 20): word w.
    refine (nat_cast word _ (sext v (w - 20))). clear -w_lbound. abstract omega.
  Defined.

  (* using the same names (var) in source and target language *)
  Fixpoint compile_stmt(s: @stmt wlit var): list (@Instruction wlit var) :=
    match s with
    | SLit x v => [Addi (var2Register x) RegO v]
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
        [Jal RegO (wneg ($4 ^* $(S (S (length body1' + length body2')))))]
    | SSeq s1 s2 => compile_stmt s1 ++ compile_stmt s2
    | SSkip => nil
    end.

  Lemma compile_stmt_size: forall s,
    length (compile_stmt s) <= 2 * (stmt_size s).
  Proof.
    induction s; simpl; try destruct op; simpl;
    repeat (rewrite app_length; simpl); omega.
  Qed.

  Definition containsProgram(m: RiscvMachine)(program: list (@Instruction wlit var))(offset: word w)
    := forall i inst, nth_error program i = Some inst ->
                      m.(instructionMem) (offset ^+ $4 ^* $i) = inst.

  Definition containsState(m: RiscvMachine)(s: state)
    := forall x v, get s x = Some v -> m.(registers) x = v.

  (*
  Definition containsProgramAndState(m: RiscvMachine)(program: list (@Instruction var))(s: state)
    := containsProgram m program m.(pc) /\ containsState m s.
  *)

  (* TODO define type classes in such a way that this is not needed *)
  Definition myRiscvMachine := @IsRiscvMachine wlit wdiff var _.
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
  Inductive runsToSatisfying
    (initial: @RiscvMachine wlit wdiff var)
    (P: @RiscvMachine wlit wdiff var -> Prop)
  : Prop :=
    | runsToDone:
       P initial ->
       runsToSatisfying initial P
    | runsToStep:
       runsToSatisfying (execState (run1 (w_lbound := w_lbound)) initial) P ->
       runsToSatisfying initial P.

  Lemma execState_compose{S A: Type}: forall (m1 m2: State S A) (initial: S),
    execState m2 (execState m1 initial) = execState (m1 ;; m2) initial.
  Proof.
    intros. unfold execState. unfold Bind, Return, State_Monad.
    destruct (m1 initial). reflexivity.
  Qed.

  Lemma runsToSatisfying_exists_fuel: forall initial P,
    runsToSatisfying initial P ->
    exists fuel, P (execState (run (w_lbound := w_lbound) fuel) initial).
  Proof.
    introv R. induction R.
    - exists 0. exact H.
    - destruct IHR as [fuel IH]. exists (S fuel).
      unfold run in *.
      rewrite execState_compose in IH.
      apply IH.
  Qed.

  Lemma runsToSatisfying_trans: forall P Q initial,
    runsToSatisfying initial P ->
    (forall middle, P middle -> runsToSatisfying middle Q) ->
    runsToSatisfying initial Q.
  Proof.
    introv R1. induction R1; introv R2; [solve [auto]|].
    apply runsToStep. apply IHR1. apply R2.
  Qed.

  Lemma runsToSatisfying_imp: forall (P Q : RiscvMachine -> Prop) initial,
    runsToSatisfying initial P ->
    (forall final, P final -> Q final) ->
    runsToSatisfying initial Q.
  Proof.
    introv R1 R2. eapply runsToSatisfying_trans; [eassumption|].
    intros final Pf. apply runsToDone. auto.
  Qed.

  Lemma execute_preserves_instructionMem: forall inst initial,
    (snd (execute (w_lbound := w_lbound) inst initial)).(instructionMem) = initial.(instructionMem).
  Proof.
    intros. unfold execute.
    repeat (destruct_one_match; simpl; try reflexivity).
  Qed.

  Lemma run1_preserves_instructionMem: forall initial,
    (execState (run1 (w_lbound := w_lbound)) initial).(instructionMem) = initial.(instructionMem).
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

  Ltac solve_word_eq :=
    clear;
    repeat match goal with
    | v: word _ |- _ =>
       rewrite <- (natToWord_wordToNat v);
       let v' := fresh v in forget (# v) as v';
       clear v
    end;
    repeat (rewrite app_length; simpl);
    repeat (rewrite <- natToWord_mult || rewrite <- natToWord_plus);
    match goal with
    | |- $ _ = $ _ => f_equal
    end;
    (repeat rewrite wordToNat_natToWord_idempotent'; [omega|..]).

  Lemma two_times_div2: forall n, 2 * Nat.div2 n <= n.
  Proof.
    eapply strong. intros n IH.
    destruct n.
    - constructor.
    - destruct n.
      + simpl. constructor. constructor. 
      + simpl (Nat.div2 (S (S n))).
        specialize (IH n).
        specializes IH; omega.
  Qed.

  Lemma wmsb_0: forall sz (m: word (S sz)) default,
    # m < pow2 sz ->
    @wmsb (S sz) m default = false.
  Proof.
    induction sz; intros.
    - simpl in *. assert (#m = 0) as N by omega.
      rewrite <- (roundTrip_0 1) in N.
      apply wordToNat_inj in N. subst m.
      simpl. reflexivity.
    - pose proof (shatter_word_S m) as P.
      destruct P as [b [m0 E]]. subst.
      unfold wmsb. fold wmsb.
      apply IHsz.
      simpl in H. destruct b; omega.
  Qed.

  Lemma wmsb_0_natToWord: forall sz n default,
    2 * n < pow2 (S sz) ->
    @wmsb (S sz) (natToWord (S sz) n) default = false.
  Proof.
    intros. apply wmsb_0.
    pose proof (wordToNat_natToWord_le (S sz) n). unfold pow2 in H. fold pow2 in H. omega.
  Qed.

  (* Part 1: about sext and natToWord *)
  Lemma sext_natToWord0: forall sz1 sz2 n,
    2 * n < pow2 sz1 ->
    sext (natToWord sz1 n) sz2 = natToWord (sz1 + sz2) n.
  Proof.
    induction sz1; intros.
    - simpl. unfold sext. simpl. unfold wzero. unfold pow2 in *.
      assert (n=0) by omega. subst n. reflexivity.
    - unfold sext in *.
      assert (@wmsb (S sz1) (natToWord (S sz1) n) false = false) as E by
        (apply wmsb_0_natToWord; assumption).
      rewrite E. clear E.
      simpl. unfold natToWord. f_equal. fold natToWord.
      specialize (IHsz1 sz2 (Nat.div2 n)).
      rewrite <- IHsz1.
      + assert (@wmsb sz1 (natToWord sz1 (Nat.div2 n)) false = false) as E. {
          destruct sz1.
          - reflexivity.
          - apply wmsb_0_natToWord. unfold pow2 in *. fold pow2 in *.
            assert (2 * Nat.div2 n <= n) by apply two_times_div2. omega.
        }
        rewrite E. clear E. reflexivity.
      + replace (pow2 (S sz1)) with (2 * (pow2 sz1)) in H.
        * assert (2 * Nat.div2 n <= n) by apply two_times_div2. omega.
        * reflexivity.
  Qed.

  Require Import Coq.Program.Equality.

  Lemma nat_cast_eq_rect: forall (P : nat -> Type),
    (forall a, P (S a) -> P a) ->
    forall (n m : nat)  (e: n = m) (pn: P n),
    nat_cast P e pn = eq_rect n P pn m e.
  Proof.
    intros P f. induction n; intros.
    - subst m. simpl. reflexivity.
    - destruct m; [ discriminate |].
      inversion e.
      simpl.
      specialize (IHn _ H0 (f _ pn)).
      simpl.
  Admitted.

  (* Part 2: about nat_cast *)
  Lemma natcast_same: forall (s: nat) (n: word s),
    nat_cast word eq_refl n = n.
  Proof.
    intros. rewrite nat_cast_eq_rect.
    - reflexivity.
    - intros. pose proof (shatter_word_S H). Fail destruct H0 as [b [c E]].
  Admitted.

  (* put it together *)
  Lemma sext_natToWord: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
    2 * n < pow2 sz1 ->
    nat_cast word e (sext (natToWord sz1 n) sz2) = natToWord sz n.
  Proof.
    intros. rewrite sext_natToWord0 by assumption. rewrite e.
    apply natcast_same.
  Qed.

  (*
  Require Import Coq.Program.Equality.

  Lemma natcast_same: forall (s: nat) (n: word s),
    nat_cast word eq_refl n = n.
  Proof.
    induction s; intros.
    - reflexivity.
    - dependent destruction n.
      specialize (IHs n1).
      simpl.
  Admitted.

  Lemma sext_natToWord: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
    2 * n < pow2 sz1 ->
    nat_cast word e (sext (natToWord sz1 n) sz2) = natToWord sz n.
  Proof.
    induction sz2; intros.
    - unfold sext. rewrite combine_n_0. rewrite combine_n_0.
      match goal with
      | |- context C[if ?c then ?A else ?A] => assert ((if c then A else A) = A) as E
        by (destruct c; reflexivity); rewrite E; clear E
      end.
      subst sz. unfold eq_rect.
      replace (match plus_n_O sz1 in (_ = y) return (word y) with
      | eq_refl => $ (n)
      end) with (natToWord (sz1+0) n)
      by (destruct (plus_n_O sz1); reflexivity).
      replace (sz1 + 0) with sz1 by omega.
      apply natcast_same.
    - destruct sz as [|sz]; [omega|].
      assert (sz1 + sz2 = sz) as e' by omega.
      specialize (IHsz2 sz1 sz n e' H).
      unfold sext. unfold Word.combine.
      (* combine matches on its word arg, so we'd need induction on that ?? *)
  Abort.

  Lemma sext_natToWord: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
    2 * n < pow2 sz1 ->
    nat_cast word e (sext (natToWord sz1 n) sz2) = natToWord sz n.
  Proof.
    intros. (* seems to ad-hoc, can we state something more general and simpler? but what? *)
  Admitted.
  *)

   Lemma sext_neg_natToWord: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
     2 * n < pow2 sz1 ->
     nat_cast word e (sext (wneg (natToWord sz1 n)) sz2) = wneg (natToWord sz n).
   Admitted.

  Definition evalH := @eval_stmt w wlit wdiff eq_refl var state stateMap.

  Lemma compile_stmt_correct_aux: forall fuelH s insts initialH finalH initialL finalPc,
    compile_stmt s = insts ->
    stmt_size s < pow2 8 ->
    evalH fuelH initialH s = Success finalH ->
    containsProgram initialL insts initialL.(pc) ->
    containsState initialL initialH ->
    finalPc = initialL.(pc) ^+ $ (4) ^* $ (length insts) ->
    runsToSatisfying initialL (fun finalL => containsState finalL finalH /\
       finalL.(pc) = finalPc).
  Proof.
    induction fuelH; [intros; discriminate |].
    introv C Csz EvH Cp Cs PcEq.
    unfold evalH in EvH.
    invert_eval_stmt.
    - subst *. destruct_containsProgram.
      destruct initialL as [initialProg initialRegs initialPc].
      apply runsToStep. apply runsToDone.
      simpl_run1.
      simpl in Cp0.
      rewrite Cp0. simpl.
      rewrite <- (wmult_comm $1). rewrite wmult_unit. refine (conj _ eq_refl).
      eapply containsState_put; [eassumption|].
      unfold Riscv.signed_lit_to_word, FlatImp.signed_lit_to_word.
      apply wplus_unit.
    - simpl in C. subst *.
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
      split.
      + eapply containsState_put; [ eassumption |].
        unfold Riscv.signed_lit_to_word.
        replace (nat_cast word eq_refl (sext $ (1) wdiff)) with (wone w).
        * apply reduce_eq_to_sub_and_lt.
        * symmetry. apply sext_natToWord. rewrite wlit_eq. unfold pow2. omega.
      + solve_word_eq.
    - simpl in C. subst *.
      destruct initialL as [initialProg initialRegs initialPc].
      destruct_containsProgram.
      apply runsToStep.
      simpl_run1.
      rewrite Cp0.
      apply runsToDone. simpl.
      split.
      + eapply containsState_put; [ eassumption |].
        unfold containsState in Cs. simpl in Cs.
        erewrite Cs by eassumption.
        solve_word_eq.
      + solve_word_eq.
    - simpl in C. subst *.
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
      specializes IHfuelH; [reflexivity|omega|eassumption|eassumption|eassumption|reflexivity|idtac].
      apply runsTo_preserves_instructionMem in IHfuelH. simpl in IHfuelH.
      apply (runsToSatisfying_trans _ _ _ IHfuelH).
      intros middleL [[Cs2 F] E].
      destruct middleL as [middleProg middleRegs middlePc]. simpl in *. subst middleProg middlePc.
      apply runsToStep.
      simpl_run1.
      rewrite Cp2. simpl.
      apply runsToDone.
      refine (conj Cs2 _).
      repeat (rewrite <- natToWord_mult || rewrite <- natToWord_plus).
      unfold Riscv.signed_jimm_to_word.
      rewrite sext_natToWord.
      * solve_word_eq.
      * pose proof (compile_stmt_size s2). unfold pow2. omega.
    - simpl in C. subst *.
      destruct_containsProgram.
      apply runsToStep.
      destruct initialL as [initialProg initialRegs initialPc]; simpl in *.
      simpl_run1.
      rewrite Cp0. simpl.
      pose proof Cs as Cs'.
      unfold containsState in Cs'. simpl in Cs'.
      apply Cs' in H. rewrite H.
      destruct (weq $0 $0); [|contradiction]. simpl.
      eapply (IHfuelH s2); [reflexivity|omega|eassumption|idtac|eassumption|idtac].
      + match goal with
        | H: containsProgram ?st1 ?insts1 ?ofs1 |- containsProgram ?st2 ?insts2 ?ofs2 =>
            unify insts1 insts2;
            assert (ofs1 = ofs2) as OfsEq
        end. {
          simpl.
          repeat (rewrite <- natToWord_mult || rewrite <- natToWord_plus).
          unfold Riscv.signed_lit_to_word.
          rewrite sext_natToWord.
          * solve_word_eq.
          * rewrite wlit_eq at 2. pose proof (compile_stmt_size s1). unfold pow2. omega.
        }
        rewrite <- OfsEq. assumption.
      + simpl.
        repeat (rewrite <- natToWord_mult || rewrite <- natToWord_plus).
        unfold Riscv.signed_lit_to_word.
        rewrite sext_natToWord.
        * solve_word_eq.
        * rewrite wlit_eq at 2. pose proof (compile_stmt_size s1). unfold pow2. omega.
    - simpl in C. subst *.
      destruct_containsProgram.
      destruct initialL as [initialProg initialRegs initialPc]; simpl in *.
      match goal with
      | |- runsToSatisfying ?st _ => specialize IHfuelH with (initialL := st); simpl in IHfuelH
      end.
      specialize (IHfuelH s1).
      specializes IHfuelH; [reflexivity|omega|eassumption|eassumption|eassumption|reflexivity|idtac].
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
      repeat (rewrite <- natToWord_mult || rewrite <- natToWord_plus).
      unfold Riscv.signed_lit_to_word.
      rewrite sext_natToWord.
      * solve_word_eq.
      * rewrite wlit_eq at 2. pose proof (compile_stmt_size s2). unfold pow2. omega.
    - simpl in C. subst *.
      pose proof IHfuelH as IH.
      pose proof (conj I Cp) as CpSaved.
      destruct_containsProgram.
      destruct initialL as [initialProg initialRegs initialPc]; simpl in *.
      match goal with
      | |- runsToSatisfying ?st _ => specialize IHfuelH with (initialL := st); simpl in IHfuelH
      end.
      specialize (IHfuelH s1).
      specializes IHfuelH; [reflexivity|omega|eassumption|eassumption|eassumption|reflexivity|idtac].
      apply runsTo_preserves_instructionMem in IHfuelH. simpl in IHfuelH.
      apply (runsToSatisfying_trans _ _ _ IHfuelH). clear IHfuelH.
      intros middleL [[Cs2 F] E].
      destruct middleL as [middleProg middleRegs middlePc]. simpl in *. subst middleProg middlePc.
      apply runsToStep.
      simpl_run1.
      rewrite Cp1. simpl.
      pose proof Cs2 as Cs2'.
      unfold containsState in Cs2'. simpl in Cs2'.
      apply Cs2' in H0. rewrite H0.
      destruct (weq x1 $0); [contradiction|]. simpl.
      pose proof IH as IHfuelH.
      match goal with
      | |- runsToSatisfying ?st _ => specialize IHfuelH with (initialL := st); simpl in IHfuelH
      end.
      specialize (IHfuelH s2).
      specializes IHfuelH; [reflexivity|omega|eassumption|eassumption|eassumption|reflexivity|idtac].
      apply runsTo_preserves_instructionMem in IHfuelH. simpl in IHfuelH.
      apply (runsToSatisfying_trans _ _ _ IHfuelH). clear IHfuelH.
      intros endL [[Cs3 F] E].
      destruct endL as [endProg endRegs endPc]. simpl in *. subst endProg endPc.
      apply runsToStep.
      simpl_run1.
      rewrite Cp3. simpl.
      eapply (IH (SLoop s1 cond s2)); [reflexivity|eassumption|eassumption|idtac|eassumption|idtac].
      + simpl.
        apply proj2 in CpSaved.
        match goal with
        | H: containsProgram ?st1 ?insts1 ?ofs1 |- containsProgram ?st2 ?insts2 ?ofs2 =>
            unify insts1 insts2;
            assert (ofs1 = ofs2) as OfsEq
        end. {
          repeat (rewrite <- natToWord_mult || rewrite <- natToWord_plus).
          unfold Riscv.signed_jimm_to_word.
          rewrite sext_neg_natToWord.
          {
          clear.
          forget (length (compile_stmt s1)) as L1.
          forget (length (compile_stmt s2)) as L2.
          rewrite <- ? wplus_assoc.
          rewrite <- wplus_unit at 1.
          rewrite wplus_comm at 1.
          f_equal.
          symmetry.
          rewrite? wplus_assoc.
          match goal with
          | |- ?A ^+ ^~ ?B = $0 => replace B with A; [apply wminus_inv|]
          end.
          solve_word_eq.
          } {
          pose proof (compile_stmt_size s1).
          pose proof (compile_stmt_size s2). unfold pow2. omega.
          }
        }
        rewrite <- OfsEq. assumption.
      + simpl.
        unfold Riscv.signed_jimm_to_word.
        repeat (rewrite app_length ||
          match goal with
          | |- context C[length (?h :: ?t)] => let r := context C [S (length t)] in change r
          end).
        repeat (rewrite <- natToWord_mult || rewrite <- natToWord_plus).
        remember (length (compile_stmt s1)) as L1.
        remember (length (compile_stmt s2)) as L2.
        rewrite sext_neg_natToWord.
        {
        rewrite <- ? wplus_assoc.
        f_equal.
        rewrite ? wplus_assoc.
        rewrite <- wplus_unit at 1.
        f_equal.
        symmetry.
        match goal with
        | |- ?A ^+ ^~ ?B = $0 => replace B with A; [apply wminus_inv|]
        end.
        solve_word_eq.
        } {
          pose proof (compile_stmt_size s1).
          pose proof (compile_stmt_size s2).
          unfold pow2. omega.
        }
    - simpl in C. subst *. apply containsProgram_app_inv in Cp. destruct Cp as [Cp1 Cp2].
      rename x into middleH.
      match goal with
      | _: stmt_size (SSeq s1 s2) < ?B |- _ => remember B as bound
      end.
      simpl in Csz.
      eapply runsToSatisfying_trans.
      + specialize (IHfuelH s1).
        specializes IHfuelH; [reflexivity|omega|eassumption|eassumption|eassumption|reflexivity|].
        apply runsTo_preserves_instructionMem in IHfuelH.
        apply IHfuelH.
      + simpl. intros middleL [[Cs2 F] E]. rewrite <- F in Cp2.
        eapply (IHfuelH s2); [reflexivity|omega|eassumption|idtac|eassumption|idtac].
        * unfold containsProgram in *. rewrite E. assumption.
        * rewrite F.
          destruct initialL. simpl. solve_word_eq.
    - simpl in C. subst *. apply runsToDone. split; [assumption|].
      destruct initialL. simpl. solve_word_eq.
  Qed.

End FlatToRiscv.
