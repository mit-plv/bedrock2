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
Require Import compiler.runsToSatisfying.
Require Import Coq.Program.Tactics.

Section FlatToRiscv.

  Context {wlit: nat}. (* bit width of literals *)
  Context {wdiff: nat}. (* bit width difference between literals and words *)
  Notation w := (wlit + wdiff).
  Context {wjimm: nat}. (* bit width of "jump immediates" *)
  Variable w_lbound: w >= wjimm. (* to make sure we can convert a signed jump-immediate to a word
    without loss *)
  Variable wlit_bound: 2 <= wlit <= wjimm.
  Variable wjimm_bound: 2 <= wjimm <= w.
  Context {var: Set}.
  Context {eq_var_dec: DecidableEq var}.
  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.

  Definition var2Register: var -> @Register var := RegS.

  Definition compile_op(res: var)(op: binop)(arg1 arg2: var): list (@Instruction wlit wjimm var) :=
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

  Definition signed_jimm_to_word(v: word wjimm): word w.
    refine (nat_cast word _ (sext v (w - wjimm))). clear -w_lbound. abstract omega.
  Defined.

  (* using the same names (var) in source and target language *)
  Fixpoint compile_stmt(s: @stmt wlit var): list (@Instruction wlit wjimm var) :=
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

  Definition containsProgram(m: RiscvMachine)
    (program: list (@Instruction wlit wjimm var))(offset: word w)
    := forall i inst, nth_error program i = Some inst ->
                      m.(instructionMem) (offset ^+ $4 ^* $i) = inst.

  Definition containsState(m: @RiscvMachine wlit wdiff wjimm var)(s: state)
    := forall x v, get s x = Some v -> m.(registers) x = v.

  (* TODO define type classes in such a way that this is not needed *)
  Definition myRiscvMachine := @IsRiscvMachine wlit wdiff wjimm var _.
  Existing Instance myRiscvMachine.

  Lemma wmult_neut_r: forall (sz : nat) (x : word sz), x ^* $0 = $0.
  Proof.
    intros. unfold wmult. unfold wordBin. do 2 rewrite wordToN_nat.
    rewrite <- Nnat.Nat2N.inj_mul. rewrite roundTrip_0.
    rewrite Nat.mul_0_r. simpl. rewrite wzero'_def. reflexivity.
  Qed.

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

  Lemma mul_div_undo: forall i c,
    c <> 0 ->
    c * i / c = i.
  Proof.
    intros.
    pose proof (Nat.div_mul_cancel_l i 1 c) as P.
    rewrite Nat.div_1_r in P.
    rewrite Nat.mul_1_r in P.
    apply P; auto.
  Qed.

  Lemma initialRiscvMachine_containsProgram: forall p,
    4 * (length p) < pow2 w ->
    containsProgram (initialRiscvMachine p) p (pc (initialRiscvMachine p)).
  Proof.
    intros. unfold containsProgram, initialRiscvMachine.
    intros.
    cbv [pc instructionMem]. apply nth_error_nth.
    match goal with
    | H: nth_error _ ?i1 = _ |- nth_error _ ?i2 = _ => replace i2 with i1; [assumption|]
    end.
    rewrite wplus_unit.
    rewrite <- natToWord_mult.
    rewrite wordToNat_natToWord_idempotent'.
    - symmetry. apply mul_div_undo. auto.
    - assert (i < length p). {
        apply nth_error_Some. intro. congruence.
      }
      omega.
  Qed.

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
    - inverts H1. assumption.
    - simpl in H. apply H. assumption.
  Qed.

  Lemma distr_if_over_app: forall T U P1 P2 (c: sumbool P1 P2) (f1 f2: T -> U) (x: T),
    (if c then f1 else f2) x = if c then f1 x else f2 x.
  Proof. intros. destruct c; reflexivity. Qed.

  Lemma pair_eq_acc: forall T1 T2 (a: T1) (b: T2) t,
    t = (a, b) -> a = fst t /\ b = snd t.
  Proof. intros. destruct t. inversionss. auto. Qed.

  (* alternative way of saying "exists fuel, run fuel initial = final /\ P final" 
  Inductive runsToSatisfying
    (initial: @RiscvMachine wlit wdiff var)
    (P: @RiscvMachine wlit wdiff var -> Prop)
  : Prop :=
    | runsToDone:
       P initial ->
       runsToSatisfying initial P
    | runsToStep:
       runsToSatisfying (execState (run1 (w_lbound := w_lbound)) initial) P ->
       runsToSatisfying initial P.*)

  Definition runsToSatisfying:
    @RiscvMachine wlit wdiff wjimm var -> (@RiscvMachine wlit wdiff wjimm var -> Prop) -> Prop :=
    runsTo (@RiscvMachine wlit wdiff wjimm var) (execState (run1 (w_lbound := w_lbound))).

  Lemma execState_compose{S A: Type}: forall (m1 m2: State S A) (initial: S),
    execState m2 (execState m1 initial) = execState (m1 ;; m2) initial.
  Proof.
    intros. unfold execState. unfold Bind, Return, State_Monad.
    destruct (m1 initial). reflexivity.
  Qed.

  Lemma runsToSatisfying_exists_fuel_old: forall initial P,
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

  Lemma runsToSatisfying_exists_fuel: forall initial P,
    runsToSatisfying initial P ->
    exists fuel, P (execState (run (w_lbound := w_lbound) fuel) initial).
  Proof.
    introv R.
    unfold run.
    pose proof (runsToSatisfying_exists_fuel _ _ initial P R) as F.
  Abort.

(*
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
*)

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
    - apply runsToStep. rewrite run1_preserves_instructionMem in IHrunsTo. assumption.
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

  (* TODO is there a principled way of writing such proofs? *)
  Lemma reduce_eq_to_sub_and_lt: forall (y z: word w) {T: Type} (thenVal elseVal: T),
    (if wlt_dec (y ^- z) $1 then thenVal else elseVal) =
    (if weq y z             then thenVal else elseVal).
  Proof.
    intros. destruct (weq y z).
    - subst z. unfold wminus. rewrite wminus_inv. destruct (wlt_dec (wzero w) $1); [reflexivity|].
      change (wzero w) with (natToWord w 0) in n. unfold wlt in n.
      exfalso. apply n.
      do 2 rewrite wordToN_nat. rewrite roundTrip_0.
      destruct w as [|w1]; [omega|].
      rewrite roundTrip_1.
      simpl. constructor.
    - destruct (@wlt_dec w (y ^- z) $ (1)) as [E|NE]; [|reflexivity].
      exfalso. apply n. apply sub_0_eq.
      unfold wlt in E.
      do 2 rewrite wordToN_nat in E.
      destruct w as [|w1]; [omega|].
      rewrite roundTrip_1 in E.
      simpl in E. apply N.lt_1_r in E. change 0%N with (N.of_nat 0) in E.
      apply Nnat.Nat2N.inj in E. rewrite <- (roundTrip_0 (S w1)) in E.
      apply wordToNat_inj in E.
      exact E.
  Qed.

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

  Lemma wmsb_1: forall sz (m: word (S sz)) default,
    pow2 sz <= # m < 2 * pow2 sz ->
    @wmsb (S sz) m default = true.
  Proof.
    induction sz; intros.
    - simpl in *. assert (#m = 1) as N by omega.
      rewrite <- (roundTrip_1 1) in N.
      apply (wordToNat_inj m ($ 1)) in N. subst m.
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

  Lemma wmsb_1_natToWord: forall sz n default,
    pow2 sz <= n < 2 * pow2 sz ->
    @wmsb (S sz) (natToWord (S sz) n) default = true.
  Proof.
    intros. apply wmsb_1.
    rewrite wordToNat_natToWord_idempotent'; simpl; omega.
  Qed.

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

  Lemma mod2sub: forall a b,
    b <= a ->
    mod2 (a - b) = xorb (mod2 a) (mod2 b).
  Proof.
    intros. remember (a - b) as c. revert dependent b. revert a. revert c.
    change (forall c,
      (fun c => forall a b, b <= a -> c = a - b -> mod2 c = xorb (mod2 a) (mod2 b)) c).
    apply strong.
    intros c IH a b AB N.
    destruct c.
    - assert (a=b) by omega. subst. rewrite Bool.xorb_nilpotent. reflexivity.
    - destruct c.
      + assert (a = S b) by omega. subst a. simpl (mod2 1). rewrite mod2_S_not.
        destruct (mod2 b); reflexivity.
      + destruct a; [omega|].
        destruct a; [omega|].
        simpl.
        apply IH; omega.
  Qed.

  Lemma pow2_nonzero: forall a,
    1 <= pow2 a.
  Proof.
    induction a; simpl; omega.
  Qed.

  Lemma pow2le: forall a b,
    a <= b ->
    pow2 a <= pow2 b.
  Proof.
    induction a; intros.
    - simpl. apply (pow2_nonzero b).
    - destruct b; [omega|]. unfold pow2. fold pow2.
      apply Nat.mul_le_mono_l. apply IHa. omega.
  Qed.

  Lemma div2_compat_lt_l: forall a b, b < 2 * a -> Nat.div2 b < a.
  Proof.
    induction a; intros.
    - omega.
    - destruct b.
      + simpl. omega.
      + destruct b.
        * simpl. omega.
        * simpl. apply lt_n_S. apply IHa. omega.
  Qed.

(*
  Lemma div2_compat_lt_r: forall a b, 2 * a < b -> a <= Nat.div2 b.
  Proof.
    induction a; intros.
    - omega.
  Admitted.

  Goal forall a b, a = 2 -> b = 3 ->
    Nat.div2 (2 * a - b) = a - Nat.div2 b. intros. subst. simpl.
  Abort.

  Lemma div2_2_minus: forall a b,
    Nat.div2 (2 * a - b) = a - Nat.div2 b.
  Proof.
    intros. remember (2 * a - b) as c. revert dependent b. revert a. revert c.
    change (forall c,
      (fun c => forall a b, c = 2 * a - b -> Nat.div2 c = a - Nat.div2 b) c).
    apply strong.
    intros c IH a b E.
    destruct c.
    - simpl. assert (b = 2 * a \/ 2 * a < b) as C by omega.
      destruct C.
      + subst b. rewrite Div2.div2_double. omega.
      + apply div2_compat_r in H. omega.
    - destruct c.
      + simpl. assert (S b = 2 * a \/ 2 * a < b) as C by omega.
        destruct C.
        * destruct a; [discriminate|]. assert (b = 2 * a + 1) by omega. subst b.
    induction a; intros.
  Abort.
*)

  Lemma minus_minus: forall a b c,
    c <= b <= a ->
    a - (b - c) = a - b + c.
  Proof. intros. omega. Qed.

  Lemma wones_natToWord: forall sz,
    wones sz = $ (pow2 sz - 1).
  Proof.
    induction sz.
    - reflexivity.
    - unfold wones. fold wones. rewrite IHsz.
      unfold natToWord at 2. fold natToWord. f_equal.
      + rewrite mod2sub.
        * simpl. rewrite mod2_pow2_twice. reflexivity.
        * apply pow2_nonzero.
      + f_equal. unfold pow2 at 2. fold pow2.
        rewrite <- (div2_S_double (pow2 sz - 1)). f_equal.
        pose proof (pow2_nonzero sz). omega.
  Qed.

  Lemma wneg_zero: forall sz,
    wneg (natToWord sz 0) = natToWord sz 0.
  Proof.
    intros.
    pose proof (wminus_inv (natToWord sz 0)) as P.
    rewrite wplus_unit in P.
    exact P.
  Qed.

  Lemma even_odd_destruct: forall n,
    (exists a, n = 2 * a) \/ (exists a, n = 2 * a + 1).
  Proof.
    induction n.
    - left. exists 0. reflexivity.
    - destruct IHn as [[a E] | [a E]].
      + right. exists a. omega.
      + left. exists (S a). omega.
  Qed.

  Lemma sext_wneg_natToWord00: forall sz1 sz2 n,
    pow2 sz1 <= 2 * n < pow2 (S sz1) ->
    sext (natToWord sz1 n) sz2 = natToWord (sz1 + sz2) (pow2 (sz1+sz2) - (pow2 sz1 - n)).
  Proof.
    induction sz1; intros.
    - unfold pow2 in H. omega. (* contradiction *)
    - unfold sext in *.
      assert (@wmsb (S sz1) (natToWord (S sz1) n) false = true) as E. {
        apply wmsb_1.
        rewrite wordToNat_natToWord_idempotent';
        (unfold pow2 in *; fold pow2 in *; omega).
      }
      rewrite E.
      match goal with
      | |- _ = $ ?a => remember a as b
      end.
      simpl. unfold natToWord. f_equal.
      + subst b. rewrite mod2sub.
        * rewrite mod2sub.
          { replace (S sz1 + sz2) with (S (sz1 + sz2)) by omega.
            simpl.
            do 2 rewrite mod2_pow2_twice.
            do 2 rewrite Bool.xorb_false_l.
            reflexivity.
          }
          simpl in *. omega.
        * rewrite pow2_add_mul in *. unfold pow2 in *. fold pow2 in *.
          apply Nat.le_trans with (m := 2 * pow2 sz1); [omega|].
          rewrite <- mult_assoc.
          apply mult_le_compat_l.
          rewrite <- Nat.mul_1_r at 1.
          apply mult_le_compat_l.
          apply pow2_nonzero.
      + fold natToWord.
        specialize (IHsz1 sz2 (Nat.div2 n)).
        assert (Nat.div2 b = pow2 (sz1 + sz2) - (pow2 sz1 - (Nat.div2 n))) as D2. {
          rewrite minus_minus.
          - subst b. replace (S sz1 + sz2) with (S (sz1 + sz2)) by omega.
            unfold pow2. fold pow2.
            rewrite minus_minus.
            * rewrite <- Nat.mul_sub_distr_l. 
              rewrite <- (Nat.add_comm n).
              rewrite div2_plus_2.
              apply Nat.add_comm.
            * rewrite pow2_add_mul. clear IHsz1. unfold pow2 in *. fold pow2 in *.
              split; [omega|].
              apply mult_le_compat_l.
              rewrite <- Nat.mul_1_r at 1.
              apply mult_le_compat_l.
              apply pow2_nonzero.
          - unfold pow2 in H. fold pow2 in H.
            split.
            * pose proof (div2_compat_lt_l (pow2 sz1) n) as P. omega.
            * rewrite pow2_add_mul. clear IHsz1.
              rewrite <- Nat.mul_1_r at 1.
              apply mult_le_compat_l.
              apply pow2_nonzero.
        }
        rewrite D2.
        destruct sz1 as [|sz1'].
        * simpl in H. assert (n=1) by omega. subst n. simpl in D2. simpl.
          apply wones_natToWord.
        * assert (n <= S (2 * Nat.div2 n)). {
            destruct (even_odd_destruct n) as [[m C]|[m C]]; subst n.
            - rewrite Nat.div2_double. constructor. constructor.
            - replace (2 * m + 1) with (S (2 * m)) by omega. rewrite Nat.div2_succ_double.
              constructor.
          }
         rewrite <- IHsz1.
          { assert (@wmsb (S sz1') (natToWord (S sz1') (Nat.div2 n)) false = true) as F. {
            apply wmsb_1_natToWord.
            unfold pow2 in *. fold pow2 in *.
            assert (2 * Nat.div2 n <= n) by apply two_times_div2.
            clear -H H0 H1.
            omega. }
            { rewrite F. reflexivity. }
          }
          { assert (2 * Nat.div2 n <= n) by apply two_times_div2.
            clear -H H0 H1.
            unfold pow2 in *. fold pow2 in *.
            omega. }
  Qed.

  Lemma sext_neg_natToWord0: forall sz1 sz2 n,
    2 * n < pow2 sz1 ->
    sext (wneg (natToWord sz1 n)) sz2 = wneg (natToWord (sz1 + sz2) n).
  Proof.
    intros. rewrite wneg_alt. unfold wnegN.
    destruct n as [|n].
    - rewrite roundTrip_0. rewrite Nat.sub_0_r. rewrite natToWord_pow2.
      unfold sext.
      assert (wmsb (natToWord sz1 0) false = false) as W. {
        destruct sz1.
        + simpl. reflexivity.
        + apply wmsb_0_natToWord. assumption.
      }
      rewrite W.
      rewrite combine_wzero.
      symmetry.
      apply wneg_zero.
    - rewrite sext_wneg_natToWord00.
      + rewrite wneg_alt. unfold wnegN.
        rewrite wordToNat_natToWord_idempotent' by omega.
        rewrite wordToNat_natToWord_idempotent'.
        * replace (pow2 sz1 - (pow2 sz1 - S n)) with (S n) by omega.
          reflexivity.
        * rewrite pow2_add_mul.
          apply Nat.le_trans with (m := pow2 sz1); [omega|].
          rewrite <- Nat.mul_1_r at 1.
          apply mult_le_compat_l.
          apply pow2_nonzero.
      + rewrite wordToNat_natToWord_idempotent' by omega.
        simpl. omega.
  Qed.

(*
  Lemma wneg_wnot_natToWord: forall sz a,
    wneg (natToWord sz (S a)) = wnot (natToWord sz a).
  Admitted.
*)

  Lemma natcast_same: forall (s: nat) (n: word s),
    nat_cast word eq_refl n = n.
  Proof.
    intros. rewrite nat_cast_eq_rect. reflexivity.
  Qed.

  Lemma sext_natToWord: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
    2 * n < pow2 sz1 ->
    nat_cast word e (sext (natToWord sz1 n) sz2) = natToWord sz n.
  Proof.
    intros. rewrite sext_natToWord0 by assumption. rewrite e.
    apply natcast_same.
  Qed.

   Lemma sext_neg_natToWord: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
     2 * n < pow2 sz1 ->
     nat_cast word e (sext (wneg (natToWord sz1 n)) sz2) = wneg (natToWord sz n).
   Proof.
     intros. rewrite sext_neg_natToWord0 by assumption. rewrite e. apply natcast_same.
   Qed.

  Definition evalH := @eval_stmt w wlit wdiff eq_refl var state stateMap.

  (* separate definition to better guide automation: don't simpl 16, but keep it as a 
     constant to stay in linear arithmetic *)
  Local Definition stmt_not_too_big(s: @stmt wlit var): Prop := stmt_size s * 16 < pow2 wlit.

  Local Ltac solve_stmt_not_too_big :=
    lazymatch goal with
    | H: stmt_not_too_big _ |- stmt_not_too_big _ =>
        unfold stmt_not_too_big in *;
        simpl stmt_size in H;
        omega
    end.

  Local Ltac solve_length_compile_stmt :=
    repeat match goal with
    | s: stmt |- _ => unique pose proof (compile_stmt_size s)
    end;
    lazymatch goal with
    | H: stmt_not_too_big _ |- _ =>
        unfold stmt_not_too_big in *;
        simpl stmt_size in H;
        unfold pow2; fold pow2;
        omega
    end.

  Lemma compile_stmt_correct_aux: forall fuelH s insts initialH finalH initialL finalPc,
    compile_stmt s = insts ->
    stmt_not_too_big s ->
    evalH fuelH initialH s = Success finalH ->
    containsProgram initialL insts initialL.(pc) ->
    containsState initialL initialH ->
    finalPc = initialL.(pc) ^+ $ (4) ^* $ (length insts) ->
    runsToSatisfying initialL (fun finalL => containsState finalL finalH /\
       finalL.(pc) = finalPc).
  Proof.
    pose proof (pow2le wlit wjimm (proj2 wlit_bound)) as WLJ.
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
      remember (runsTo RiscvMachine (execState run1)) as runsToRest.
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
        * symmetry. apply sext_natToWord.
          replace wlit with (S (S (pred (pred wlit)))) by omega. unfold pow2. fold pow2.
          pose proof (pow2_nonzero (pred (pred wlit))). omega.
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
      remember (runsTo RiscvMachine (execState run1)) as runsToRest.
      destruct initialL as [initialProg initialRegs initialPc]; simpl in *.
      simpl_run1.
      rewrite Cp0. simpl.
      pose proof Cs as Cs'.
      unfold containsState in Cs'. simpl in Cs'.
      apply Cs' in H. subst x.
      destruct (weq (initialRegs cond) $ (0)); [contradiction|]. simpl.
      match goal with
      | |- runsToRest ?st _ => specialize IHfuelH with (initialL := st); simpl in IHfuelH
      end.
      specialize (IHfuelH s1).
      specializes IHfuelH; [reflexivity|solve_stmt_not_too_big|
        eassumption|eassumption|eassumption|reflexivity|idtac].
      apply runsTo_preserves_instructionMem in IHfuelH. simpl in IHfuelH.
      subst runsToRest.
      apply (runsToSatisfying_trans _ _ _ _ _ IHfuelH).
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
      * solve_length_compile_stmt.
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
      eapply (IHfuelH s2); [reflexivity|solve_stmt_not_too_big|eassumption|idtac|eassumption|idtac].
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
          * solve_length_compile_stmt.
        }
        rewrite <- OfsEq. assumption.
      + simpl.
        repeat (rewrite <- natToWord_mult || rewrite <- natToWord_plus).
        unfold Riscv.signed_lit_to_word.
        rewrite sext_natToWord.
        * solve_word_eq.
        * solve_length_compile_stmt.
    - simpl in C. subst *.
      destruct_containsProgram.
      destruct initialL as [initialProg initialRegs initialPc]; simpl in *.
      match goal with
      | |- runsToSatisfying ?st _ => specialize IHfuelH with (initialL := st); simpl in IHfuelH
      end.
      specialize (IHfuelH s1).
      specializes IHfuelH; [reflexivity|solve_stmt_not_too_big|
        eassumption|eassumption|eassumption|reflexivity|idtac].
      apply runsTo_preserves_instructionMem in IHfuelH. simpl in IHfuelH.
      apply (runsToSatisfying_trans _ _ _ _ _ IHfuelH).
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
      * solve_length_compile_stmt.
    - simpl in C. subst *.
      pose proof IHfuelH as IH.
      pose proof (conj I Cp) as CpSaved.
      destruct_containsProgram.
      destruct initialL as [initialProg initialRegs initialPc]; simpl in *.
      match goal with
      | |- runsToSatisfying ?st _ => specialize IHfuelH with (initialL := st); simpl in IHfuelH
      end.
      specialize (IHfuelH s1).
      specializes IHfuelH; [reflexivity|solve_stmt_not_too_big|
        eassumption|eassumption|eassumption|reflexivity|idtac].
      apply runsTo_preserves_instructionMem in IHfuelH. simpl in IHfuelH.
      apply (runsToSatisfying_trans _ _ _ _ _ IHfuelH). clear IHfuelH.
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
      | |- runsTo _ _ ?st  _ => specialize IHfuelH with (initialL := st); simpl in IHfuelH
      end.
      specialize (IHfuelH s2).
      specializes IHfuelH; [reflexivity|solve_stmt_not_too_big|
        eassumption|eassumption|eassumption|reflexivity|idtac].
      apply runsTo_preserves_instructionMem in IHfuelH. simpl in IHfuelH.
      apply (runsToSatisfying_trans _ _ _ _ _ IHfuelH). clear IHfuelH.
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
          solve_length_compile_stmt.
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
        solve_length_compile_stmt.
        }
    - simpl in C. subst *. apply containsProgram_app_inv in Cp. destruct Cp as [Cp1 Cp2].
      rename x into middleH.
      eapply runsToSatisfying_trans.
      + specialize (IHfuelH s1).
        specializes IHfuelH; [reflexivity|solve_stmt_not_too_big|
          eassumption|eassumption|eassumption|reflexivity|].
        apply runsTo_preserves_instructionMem in IHfuelH.
        apply IHfuelH.
      + simpl. intros middleL [[Cs2 F] E]. rewrite <- F in Cp2.
        eapply (IHfuelH s2); [reflexivity|solve_stmt_not_too_big|
          eassumption|idtac|eassumption|idtac].
        * unfold containsProgram in *. rewrite E. assumption.
        * rewrite F.
          destruct initialL. simpl. solve_word_eq.
    - simpl in C. subst *. apply runsToDone. split; [assumption|].
      destruct initialL. simpl. solve_word_eq.
  Qed.

  Lemma every_state_contains_empty_state: forall s,
    containsState s empty.
  Proof.
    unfold containsState.
    intros. rewrite empty_is_empty in H. discriminate.
  Qed.

  Lemma compile_stmt_correct: forall resVar fuelH finalH s insts,
    stmt_size s * 16 < pow2 wlit ->
    compile_stmt s = insts ->
    evalH fuelH empty s = Success finalH ->
    get finalH resVar <> None ->
    exists fuelL,
    Some ((execState (run (w_lbound := w_lbound) fuelL) (initialRiscvMachine insts)).(registers) resVar)
    = get finalH resVar.
  Proof.
    introv B C E G.
    change (exists fuel, 
     (fun final => Some (registers final resVar) = (get finalH resVar))
     (execState (run (w_lbound := w_lbound) fuel) (initialRiscvMachine insts))).
    apply runsToSatisfying_exists_fuel_old.
    eapply runsToSatisfying_imp.
    - eapply @compile_stmt_correct_aux with (s := s) (initialH := empty)
        (fuelH := fuelH) (finalH := finalH).
      + reflexivity.
      + assumption.
      + apply E.
      + subst insts. apply initialRiscvMachine_containsProgram.
        pose proof (pow2le wlit wjimm (proj2 wlit_bound)).
        pose proof (pow2le wjimm w (proj2 wjimm_bound)).
        change (stmt_not_too_big s) in B.
        solve_length_compile_stmt.
      + apply every_state_contains_empty_state.
      + reflexivity.
    - intros.
      simpl in H. apply proj1 in H.
      unfold containsState in H.
      specialize (H resVar).
      destruct (Common.get finalH resVar) eqn: Q.
      + specialize (H _ eq_refl).
        simpl in Q. unfold id in Q. simpl in *. congruence.
      + contradiction.
  Qed.

End FlatToRiscv.
