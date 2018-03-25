Require Import lib.LibTacticsMin.
Require Import riscv.util.Monads.
Require Import compiler.Common.
Require Import compiler.FlatImp.
Require Import compiler.StateCalculus.
Require Import bbv.DepEqNat.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import compiler.Op.
Require Import compiler.ResMonad.
Require Import riscv.Riscv.
Require Import compiler.runsToSatisfying.
Require Import riscv.RiscvBitWidths.
Require Import riscv.util.NameWithEq.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.


Section FlatToRiscv.

  Context {Bw: RiscvBitWidths}.

  Context {Name: NameWithEq}.

  (* If we made it a definition instead, destructing an if on "@dec (@eq (@var Name) x x0)"
     (from this file), where a "@dec (@eq (@Reg Name) x x0)" (from another file, Riscv.v)
     is in the context, will not recognize that these two are the same (they both reduce to
     "@dec (@eq (@name Name) x x0)", which is annoying. *)
  Notation var := (@name Name).

  Existing Instance eq_name_dec.

  Context {state: Type}.
  Context {stateMap: Map state var (word wXLEN)}.

  Variable var2Register: var -> Register. (* TODO register allocation *)
  Definition RegO := Register0.

  Definition compile_op(res: var)(op: binop)(arg1 arg2: var): list Instruction :=
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

  Definition split_upper(szU szL : nat): word (szL + szU) -> word szU := split2 szL szU.

  Definition split_lower(szU szL : nat): word (szL + szU) -> word szL := split1 szL szU.

  Definition compile_lit(x: var)(v: Z): list Instruction :=
      let rd := var2Register x in
      let lobits := (v mod (2 ^ (Z.of_nat wimm)))%Z in
      if dec (lobits = v)
      then [Addi rd RegO lobits]
      else
        let hibits := (v - lobits)%Z in
        if Z.testbit v (Z.of_nat wimm)
        (* Xori will sign-extend lobits with 1s, therefore Z.lnot *)
        then [Lui rd (Z.lnot hibits); Xori rd rd lobits]
        (* Xori will sign-extend lobits with 0s *)
        else [Lui rd hibits; Xori rd rd lobits].

  (* using the same names (var) in source and target language *)
  Fixpoint compile_stmt(s: @stmt wXLEN Name): list (Instruction) :=
    match s with
    | SLoad x y => [Lw (var2Register x) (var2Register y) 0]
    | SStore x y => [Sw (var2Register x) (var2Register y) 0]
    | SLit x v => compile_lit x (wordToZ v)
    | SOp x op y z => compile_op x op y z
    | SSet x y => [Add (var2Register x) RegO (var2Register y)]
    | SIf cond bThen bElse =>
        let bThen' := compile_stmt bThen in
        let bElse' := compile_stmt bElse in
        (* only works if branch lengths are < 2^12 *)
        [Beq (var2Register cond) RegO (Z.of_nat (2 * (S (length bThen'))))] ++
        bThen' ++
        [Jal RegO (Z.of_nat (2 * (length bElse')))] ++
        bElse'
    | SLoop body1 cond body2 =>
        let body1' := compile_stmt body1 in
        let body2' := compile_stmt body2 in
        (* only works if branch lengths are < 2^12 *)
        body1' ++
        [Beq (var2Register cond) RegO (Z.of_nat (2 * (S (length body2'))))] ++
        body2' ++
        [Jal RegO (- Z.of_nat (2 * (S (S (length body1' + length body2')))))]
    | SSeq s1 s2 => compile_stmt s1 ++ compile_stmt s2
    | SSkip => nil
    end.

  Lemma compile_stmt_size: forall s,
    length (compile_stmt s) <= 2 * (stmt_size s).
  Proof.
    induction s; simpl; try destruct op; simpl;
    repeat (rewrite app_length; simpl); try omega.
    unfold compile_lit.
    destruct_one_match; simpl; [omega|].
    destruct_one_match; simpl; omega.
  Qed.

  Definition containsProgram(m: RiscvMachine)(program: list Instruction)(offset: word wXLEN) :=
    forall i inst, nth_error program i = Some inst ->
                   m.(machineMem) (offset ^+ $4 ^* $i) = inst.

  Definition containsState(m: RiscvMachine)(s: state) :=
    forall x v, get s x = Some v -> m.(registers) x = v.

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
      rewrite <- wplus_assoc. f_equal. rewrite (natToWord_S wXLEN i).
      replace ($4 ^* ($1 ^+ $i)) with ((($1 ^+ $i) ^* $4): word wXLEN) by apply wmult_comm.
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

  Lemma containsState_put: forall prog1 prog2 pc1 pc2 eh1 eh2 initialH initialRegs x v1 v2,
    containsState (mkRiscvMachine prog1 initialRegs pc1 eh1) initialH ->
    v1 = v2 ->
    containsState (mkRiscvMachine prog2 
      (fun reg2 : var =>
               if dec (x = reg2)
               then v1
               else initialRegs reg2)
       pc2 eh2)
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

  Definition runsToSatisfying: RiscvMachine -> (RiscvMachine -> Prop) -> Prop :=
    runsTo RiscvMachine (execState run1).

  Lemma execState_compose{S A: Type}: forall (m1 m2: State S A) (initial: S),
    execState m2 (execState m1 initial) = execState (m1 ;; m2) initial.
  Proof.
    intros. unfold execState. unfold Bind, Return, State_Monad.
    destruct (m1 initial). reflexivity.
  Qed.

  Lemma runsToSatisfying_exists_fuel_old: forall initial P,
    runsToSatisfying initial P ->
    exists fuel, P (execState (run fuel) initial).
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
    exists fuel, P (execState (run fuel) initial).
  Proof.
    introv R.
    unfold run.
    pose proof (runsToSatisfying_exists_fuel _ _ initial P R) as F.
  Abort.

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
    - apply runsToStep. rewrite run1_preserves_instructionMem in IHrunsTo. assumption.
  Qed.

  Lemma regs_overwrite: forall x v1 v2 (initialRegs: var -> word wXLEN),
      (fun reg2 : var => if dec (x = reg2) then v2 else
                         if dec (x = reg2) then v1 else
                         initialRegs reg2)
    = (fun reg2 : var => if dec (x = reg2) then v2 else initialRegs reg2).
  Proof.
    intros.
    extensionality reg2. destruct_one_match; reflexivity.
  Qed.

  (* TODO is there a principled way of writing such proofs? *)
  Lemma reduce_eq_to_sub_and_lt: forall (y z: word wXLEN) {T: Type} (thenVal elseVal: T),
    (if wlt_dec (y ^- z) $1 then thenVal else elseVal) =
    (if weq y z             then thenVal else elseVal).
  Proof.
    intros. destruct (weq y z).
    - subst z. unfold wminus. rewrite wminus_inv.
      destruct (wlt_dec (wzero wXLEN) $1); [reflexivity|].
      change (wzero wXLEN) with (natToWord wXLEN 0) in n. unfold wlt in n.
      exfalso. apply n.
      do 2 rewrite wordToN_nat. rewrite roundTrip_0.
      destruct wXLEN as [|w1] eqn: E; [bitwidth_omega|].
      rewrite roundTrip_1.
      simpl. constructor.
    - destruct (@wlt_dec wXLEN (y ^- z) $ (1)) as [E|NE]; [|reflexivity].
      exfalso. apply n. apply sub_0_eq.
      unfold wlt in E.
      do 2 rewrite wordToN_nat in E.
      destruct wXLEN as [|w1] eqn: F; [bitwidth_omega|].
      rewrite roundTrip_1 in E.
      simpl in E. apply N.lt_1_r in E. change 0%N with (N.of_nat 0) in E.
      apply Nnat.Nat2N.inj in E. rewrite <- (roundTrip_0 (S w1)) in E.
      apply wordToNat_inj in E.
      exact E.
  Qed.

  Ltac simpl_run1 :=
         cbv [run1 execState StateMonad.put execute instructionMem registers 
             pc getPC loadInst setPC getRegister setRegister IsRiscvMachine gets
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

  Lemma sext_natToWord_nat_cast: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
    2 * n < pow2 sz1 ->
    nat_cast word e (sext (natToWord sz1 n) sz2) = natToWord sz n.
  Proof.
    intros. rewrite nat_cast_eq_rect. apply sext_natToWord. assumption.
  Qed.

  Lemma sext_neg_natToWord_nat_cast: forall sz2 sz1 sz n (e: sz1 + sz2 = sz),
    2 * n < pow2 sz1 ->
    nat_cast word e (sext (wneg (natToWord sz1 n)) sz2) = wneg (natToWord sz n).
  Proof.
    intros. rewrite nat_cast_eq_rect. apply sext_wneg_natToWord. assumption.
  Qed.

  Lemma sext0: forall sz0 sz (v: word sz) (e: sz0 = 0),
    sext v sz0 = nat_cast word (eq_ind_r (fun sz0 : nat => sz = sz + sz0) (plus_n_O sz) e) v.
  Proof.
    intros. subst.
    unfold sext.
    destruct_one_match;
      simpl; rewrite combine_n_0; rewrite <- nat_cast_eq_rect; apply nat_cast_proof_irrel.
  Qed.

  Lemma reassemble_literal_ext0: forall wup1 wlo1 wup2 wlo2 wlo3 wAll (v: word wAll)
    e1 e2 e3 e4,
    wup1 = wup2 ->
    wlo1 = wlo2 ->
    wlo2 = wlo3 ->
    wmsb (split_lower wup2 wlo2 (nat_cast word e3 v)) false = false ->
    wxor (nat_cast word e1 (extz (split_upper wup1 wlo1 (nat_cast word e4 v)) wlo3))
         (nat_cast word e2 (sext (split_lower wup2 wlo2 (nat_cast word e3 v)) wup2)) = v.
  Proof.
    intros.
    unfold extz, sext, wxor.
    rewrite H2.
    subst wlo3 wlo2 wup2.
    rewrite nat_cast_proof_irrel with (e1 := e2) (e2 := e1). clear e2.
    rewrite nat_cast_eq_rect with (e := e1).
    rewrite nat_cast_eq_rect with (e := e1).
    rewrite <- eq_rect_bitwp'.
    rewrite <- combine_bitwp.
    fold wxor. rewrite wxor_wzero. rewrite wxor_comm. rewrite wxor_wzero.
    rewrite nat_cast_proof_irrel with (e1 := e4) (e2 := e3). clear e4.
    unfold split_lower, split_upper.
    rewrite Word.combine_split.
    destruct e1. simpl.
    rewrite nat_cast_proof_irrel with (e1 := e3) (e2 := eq_refl).
    apply nat_cast_same.
  Qed.

  Lemma reassemble_literal_ext1: forall wup1 wlo1 wup2 wlo2 wlo3 wAll (v: word wAll)
    e1 e2 e3 e4,
    wup1 = wup2 ->
    wlo1 = wlo2 ->
    wlo2 = wlo3 ->
    wmsb (split_lower wup2 wlo2 (nat_cast word e3 v)) false = true ->
    wxor (nat_cast word e1 (extz (wnot (split_upper wup1 wlo1 (nat_cast word e4 v))) wlo3))
         (nat_cast word e2 (sext (split_lower wup2 wlo2 (nat_cast word e3 v)) wup2)) = v.
  Proof.
    intros.
    unfold extz, sext, wxor.
    rewrite H2.
    subst wlo3 wlo2 wup2.
    rewrite nat_cast_proof_irrel with (e1 := e2) (e2 := e1). clear e2.
    rewrite nat_cast_eq_rect with (e := e1).
    rewrite nat_cast_eq_rect with (e := e1).
    rewrite <- eq_rect_bitwp'.
    rewrite <- combine_bitwp.
    fold wxor. rewrite wxor_wzero. rewrite wxor_comm.
    rewrite <- wxor_wones.
    rewrite wxor_assoc.
    rewrite wxor_wones.
    rewrite wnot_ones.
    rewrite wxor_wzero.
    rewrite nat_cast_proof_irrel with (e1 := e4) (e2 := e3). clear e4.
    unfold split_lower, split_upper.
    rewrite Word.combine_split.
    destruct e1. simpl.
    rewrite nat_cast_proof_irrel with (e1 := e3) (e2 := eq_refl).
    apply nat_cast_same.
  Qed.

  Definition evalH := eval_stmt (w := wXLEN).

  (* separate definition to better guide automation: don't simpl 16, but keep it as a 
     constant to stay in linear arithmetic *)
  Local Definition stmt_not_too_big(s: @stmt wXLEN Name): Prop := stmt_size s * 16 < pow2 wimm.

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

  (* Needed because simpl will unfold (4 * ...) which is unreadable *)
  Local Ltac simpl_pow2 :=
    repeat match goal with
    | |- context [1 + ?a] => change (1 + a) with (S a)
    | |- context [pow2 (S ?a)] => change (pow2 (S a)) with (2 * pow2 a)
    | |- context [pow2 0] => change (pow2 0) with 1
    end.

  Local Ltac solve_pc_update :=
    rewrite? extz_is_mult_pow2;
    rewrite? sext_natToWord_nat_cast;
    simpl_pow2;
    [ solve_word_eq | solve_length_compile_stmt ].

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
    pose proof (pow2_le (wimm_wupper)) as WLJ.
    induction fuelH; [intros; discriminate |].
    introv C Csz EvH Cp Cs PcEq.
    unfold evalH in EvH.
    invert_eval_stmt.
    - (* SLit *)
      subst *.
      unfold compile_stmt, compile_lit in Cp. destruct_one_match_hyp.
      {
      destruct_containsProgram.
      destruct initialL as [initialProg initialRegs initialPc].
      apply runsToStep. apply runsToDone.
      simpl_run1.
      simpl in Cp0.
      rewrite Cp0. simpl.
      unfold compile_stmt, compile_lit. rewrite E. simpl.
      rewrite <- (wmult_comm $1). rewrite wmult_unit. refine (conj _ eq_refl).
      eapply containsState_put; [eassumption|].
      rewrite wplus_unit.
      unfold signed_imm_to_word.
      etransitivity. 2: exact e.
      apply nat_cast_proof_irrel.
      }
      {
      destruct_one_match_hyp.
      {
      destruct_containsProgram.
      destruct initialL as [initialProg initialRegs initialPc].
      apply runsToStep.
      remember (runsTo RiscvMachine (execState run1)) as runsToRest.
      simpl_run1.
      simpl in Cp0.
      rewrite Cp0. simpl.
      subst runsToRest.
      apply runsToStep.
      simpl_run1.
      simpl in Cp1.
      progress rewrite Cp1. simpl.
      apply runsToDone.
      destruct (dec (x = x)); [|contradiction].
      rewrite regs_overwrite.
      split.
      + eapply containsState_put; [ eassumption |].
        clear -E0 Name state stateMap.
        unfold upper_imm_to_word, signed_imm_to_word.
        assert (wXLEN - wInstr = 0) as Eq0 by (clear; bitwidth_omega).
        rewrite sext0 with (e := Eq0).
        rewrite nat_cast_fuse.
        pose proof reassemble_literal_ext1 as P.
        specialize P with (4 := E0).
        apply P; (clear; bitwidth_omega).
      + unfold compile_lit. rewrite E. rewrite E0. simpl. solve_word_eq.
      }
      {
      destruct_containsProgram.
      destruct initialL as [initialProg initialRegs initialPc].
      apply runsToStep.
      remember (runsTo RiscvMachine (execState run1)) as runsToRest.
      simpl_run1.
      simpl in Cp0.
      rewrite Cp0. simpl.
      subst runsToRest.
      apply runsToStep.
      simpl_run1.
      simpl in Cp1.
      progress rewrite Cp1. simpl.
      apply runsToDone.
      destruct (dec (x = x)); [|contradiction].
      rewrite regs_overwrite.
      split.
      + eapply containsState_put; [ eassumption |].
        clear -E0 Name state stateMap.
        unfold upper_imm_to_word, signed_imm_to_word.
        assert (wXLEN - wInstr = 0) as Eq0 by (clear; bitwidth_omega).
        rewrite sext0 with (e := Eq0).
        rewrite nat_cast_fuse.
        pose proof reassemble_literal_ext0 as P.
        specialize P with (4 := E0).
        apply P; (clear; bitwidth_omega).
 (* Notation "{ pn }" := (@nat_cast word _ _ _ pn). *)
 (* Notation "{ n --> m } pn" := (@nat_cast word n m _ pn) (at level 20). *)
      + unfold compile_lit. rewrite E. rewrite E0. simpl. solve_word_eq.
      }
      }
    - (* SOp *)
      simpl in C. subst *.
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
      (* Case op = OEq *)
      apply runsToStep.
      simpl_run1.
      progress rewrite Cp1. simpl.
      destruct (dec (x = x)); [|contradiction].
      rewrite regs_overwrite.
      apply runsToDone.
      split.
      + eapply containsState_put; [ eassumption |].
        unfold signed_imm_to_word.
        match goal with
        | |- context C[nat_cast word ?n ?e] => replace (nat_cast word n e) with (wone wXLEN)
        end.
        * apply reduce_eq_to_sub_and_lt.
        * symmetry. apply sext_natToWord_nat_cast.
          replace wimm with (S (S (pred (pred wimm)))).
          { unfold pow2. fold pow2.
            pose proof (one_le_pow2 (pred (pred wimm))). omega. }
          { pose proof wimm_lbound. omega. }
      + solve_word_eq.
    - (* SSet *)
      simpl in C. subst *.
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
    - (* SIf/Then *)
      simpl in C. subst *.
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
      unfold signed_jimm_to_word.
      solve_pc_update.
    - (* SIf/Else *)
      simpl in C. subst *.
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
          unfold signed_bimm_to_word.
          solve_pc_update.
        }
        rewrite <- OfsEq. assumption.
      + simpl.
        repeat (rewrite <- natToWord_mult || rewrite <- natToWord_plus).
        unfold signed_bimm_to_word.
        solve_pc_update.
    - (* SLoop/done *)
      simpl in C. subst *.
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
      unfold signed_bimm_to_word.
      solve_pc_update.
    - (* SLoop/again *)
      simpl in C. subst *.
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
          unfold signed_jimm_to_word.
          rewrite extz_is_mult_pow2_neg.
          rewrite sext_neg_natToWord_nat_cast.
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
          simpl_pow2. solve_word_eq.
          } {
          simpl_pow2. solve_length_compile_stmt.
          }
        }
        rewrite <- OfsEq. assumption.
      + simpl.
        unfold signed_jimm_to_word.
        repeat (rewrite app_length ||
          match goal with
          | |- context C[length (?h :: ?t)] => let r := context C [S (length t)] in change r
          end).
        repeat (rewrite <- natToWord_mult || rewrite <- natToWord_plus).
        remember (length (compile_stmt s1)) as L1.
        remember (length (compile_stmt s2)) as L2.
        rewrite extz_is_mult_pow2_neg.
        rewrite sext_neg_natToWord_nat_cast.
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
        simpl_pow2. solve_word_eq.
        } {
        simpl_pow2. solve_length_compile_stmt.
        }
    - (* SSeq *)
      simpl in C. subst *. apply containsProgram_app_inv in Cp. destruct Cp as [Cp1 Cp2].
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
    - (* SSkip *)
      simpl in C. subst *. apply runsToDone. split; [assumption|].
      destruct initialL. simpl. solve_word_eq.
  Qed.

  Lemma every_state_contains_empty_state: forall s,
    containsState s empty.
  Proof.
    unfold containsState.
    intros. rewrite empty_is_empty in H. discriminate.
  Qed.

  Definition evalL(fuel: nat)(insts: list Instruction)(initial: RiscvMachine): RiscvMachine :=
    execState (run fuel) (putProgram insts initial).

  Lemma putProgram_containsProgram: forall p initial,
    4 * (length p) < pow2 wXLEN ->
    containsProgram (putProgram p initial) p (pc (putProgram p initial)).
  Proof.
    intros. unfold containsProgram, putProgram.
    intros.
    destruct initial as [imem regs pc0 eh].
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

  Lemma compile_stmt_correct: forall fuelH finalH s insts initialL,
    stmt_size s * 16 < pow2 wimm ->
    compile_stmt s = insts ->
    evalH fuelH empty s = Success finalH ->
    exists fuelL,
      forall resVar res,
      get finalH resVar = Some res ->
      (evalL fuelL insts initialL).(registers) resVar = res.
  Proof.
    introv B C E.
    pose proof runsToSatisfying_exists_fuel_old as Q.
    specialize (Q (putProgram insts initialL)
      (fun finalL => forall resVar res,
       get finalH resVar = Some res ->
       finalL.(registers) resVar = res)).
    cbv beta in Q.
    apply Q; clear Q.
    eapply runsToSatisfying_imp.
    - eapply @compile_stmt_correct_aux with (s := s) (initialH := empty)
        (fuelH := fuelH) (finalH := finalH).
      + reflexivity.
      + assumption.
      + apply E.
      + subst insts. apply putProgram_containsProgram.
        change (stmt_not_too_big s) in B.
        assert (2 * pow2 wimm < pow2 wXLEN). {
          clear. destruct Bw. unfold RiscvBitWidths.wimm, RiscvBitWidths.wXLEN.
          destruct wXLEN; [omega|].
          simpl_pow2.
          pose proof (@pow2_inc wimm wXLEN).
          omega.
        }
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
      + discriminate.
  Qed.

End FlatToRiscv.
