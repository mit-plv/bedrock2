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
Require Import riscv.Minimal.
Require Import compiler.HarvardMachine.
Require Import riscv.FunctionMemory.
Require Import compiler.runsToSatisfying.
Require Import riscv.RiscvBitWidths.
Require Import compiler.NameWithEq.
Require Import Coq.Program.Tactics.
Require Import Coq.Logic.FunctionalExtensionality.
Require Import riscv.InstructionCoercions.
Require Import riscv.Utility.
Require Import compiler.StateCalculus.

Local Open Scope ilist_scope.

Section FlatToRiscv.

  Context {Bw: RiscvBitWidths}.

  (*
  Context {Name: NameWithEq}.

  (* If we made it a definition instead, destructing an if on "@dec (@eq (@var Name) x x0)"
     (from this file), where a "@dec (@eq (@Reg Name) x x0)" (from another file, Riscv.v)
     is in the context, will not recognize that these two are the same (they both reduce to
     "@dec (@eq (@name Name) x x0)", which is annoying. *)
  Notation var := (@name Name).
  Existing Instance eq_name_dec.
   *)

  Context {state: Type}.
  Context {stateMap: Map state Register (word wXLEN)}.

  Instance State_is_RegisterFile: RegisterFile state Register (word wXLEN) := {|
    getReg rf r := match get rf r with
                   | Some v => v
                   | None => $0
                   end;
    setReg := put;
    initialRegs := empty;
  |}.

  (* assumes generic translate and raiseException functions *)
  Context {RVS: @RiscvState (OState RiscvMachine) (word wXLEN) _ _ IsRiscvMachine}.  

  Definition RiscvMachine := @RiscvMachine Bw (mem wXLEN) state.

  Definition stmt: Set := @stmt wXLEN TestFlatImp.ZName.

  Ltac state_calc := state_calc_generic (@name TestFlatImp.ZName) (word wXLEN).

  (* Note: Register 0 is not considered valid because it cannot be written *)
  Definition valid_register(r: Register): Prop := (0 < r < 32)%Z.

  (* This phase assumes that register allocation has already been done on the FlatImp
     level, and expects the following to hold: *)
  Fixpoint valid_registers(s: stmt): Prop :=
    match s with
    | SLoad x a => valid_register x /\ valid_register a
    | SStore a x => valid_register a /\ valid_register x
    | SLit x _ => valid_register x
    | SOp x _ y z => valid_register x /\ valid_register y /\ valid_register z
    | SSet x y => valid_register x /\ valid_register y
    | SIf c s1 s2 => valid_register c /\ valid_registers s1 /\ valid_registers s2
    | SLoop s1 c s2 => valid_register c /\ valid_registers s1 /\ valid_registers s2
    | SSeq s1 s2 => valid_registers s1 /\ valid_registers s2
    | SSkip => True
    end.

  (*
  Variable var2Register: var -> Register. (* TODO register allocation *)
  Hypothesis no_var_mapped_to_Register0: forall (x: var), x <> Register0.
  Hypothesis var2Register_inj: forall x1 x2, x1 = x2 -> x1 = x2.
   *)
  
  (* Set Printing Projections.
     Uncaught anomaly when stepping through proofs :(
     https://github.com/coq/coq/issues/6257 *)

  Definition compile_op(rd: Register)(op: binop)(rs1 rs2: Register): list Instruction :=
    match op with
    | OPlus => [[Add rd rs1 rs2]]
    | OMinus => [[Sub rd rs1 rs2]]
    | OTimes => [[Mul rd rs1 rs2]]
    | OEq => [[Sub rd rs1 rs2; Seqz rd rd]]
    | OLt => [[Sltu rd rs1 rs2]]
    | OAnd => [[And rd rs1 rs2]]
    end.

  Definition compile_lit_32(rd: Register)(v: Z): list Instruction :=
      let lobits := (v mod (2 ^ 20))%Z in
      if dec (lobits = v)
      then [[Addi rd Register0 lobits]]
      else
        let hibits := (v - lobits)%Z in
        if Z.testbit v 20
        (* Xori will sign-extend lobits with 1s, therefore Z.lnot *)
        then [[Lui rd (Z.lnot hibits); Xori rd rd lobits]]
        (* Xori will sign-extend lobits with 0s *)
        else [[Lui rd hibits; Xori rd rd lobits]].

  Definition compile_lit(rd: Register)(v: Z): list Instruction :=
    match bitwidth with
    | Bitwidth32 => compile_lit_32 rd v
    | Bitwidth64 => compile_lit_32 rd v (* TODO *)
    end.
  
  Fixpoint compile_stmt(s: stmt): list (Instruction) :=
    match s with
    | SLoad x y => [[Lw x y 0]]
    | SStore x y => [[Sw x y 0]]
    | SLit x v => compile_lit x (wordToZ v)
    | SOp x op y z => compile_op x op y z
    | SSet x y => [[Add x Register0 y]]
    | SIf cond bThen bElse =>
        let bThen' := compile_stmt bThen in
        let bElse' := compile_stmt bElse in
        (* only works if branch lengths are < 2^12 *)
        [[Beq cond Register0 (Z.of_nat (2 * (S (length bThen'))))]] ++
        bThen' ++
        [[Jal Register0 (Z.of_nat (2 * (length bElse')))]] ++
        bElse'
    | SLoop body1 cond body2 =>
        let body1' := compile_stmt body1 in
        let body2' := compile_stmt body2 in
        (* only works if branch lengths are < 2^12 *)
        body1' ++
        [[Beq cond Register0 (Z.of_nat (2 * (S (length body2'))))]] ++
        body2' ++
        [[Jal Register0 (- Z.of_nat (2 * (S (S (length body1' + length body2')))))]]
    | SSeq s1 s2 => compile_stmt s1 ++ compile_stmt s2
    | SSkip => nil
    end.

  Lemma compile_stmt_size: forall s,
    length (compile_stmt s) <= 2 * (stmt_size s).
  Proof.
    induction s; simpl; try destruct op; simpl;
    repeat (rewrite app_length; simpl); try omega.
    unfold compile_lit, compile_lit_32.
    repeat destruct_one_match; cbv [length]; omega.
  Qed.

(*  
  Definition containsProgram(m: RiscvMachine)(program: list Instruction)(offset: word wXLEN) :=
    forall i inst, nth_error program i = Some inst ->
                   m.(instructionMem) (offset ^+ $4 ^* $i) = inst.
  
  Definition containsState(regs: Register -> word wXLEN)(s: state) :=
    forall x v, get s x = Some v -> regs x = v.

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
*)
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

  (*
  Lemma containsState_put: forall initialH initialRegs x v1 v2,
    containsState initialRegs initialH ->
    v1 = v2 ->
    containsState
      (fun reg2 =>
               if dec (x = reg2)
               then v1
               else initialRegs reg2)
     (put initialH x v2).
  Proof.
    unfold containsState. intros.
    rewrite get_put in H1.
    destruct_one_match_hyp.
    - clear E. subst. inverts H1.
      destruct_one_match; [reflexivity|].
      exfalso.
      apply n.
      reflexivity.
    - destruct_one_match.
      * clear E0. apply var2Register_inj in e. contradiction.
      * apply H. assumption.
  Qed.
  *)

  Lemma distr_if_over_app: forall T U P1 P2 (c: sumbool P1 P2) (f1 f2: T -> U) (x: T),
    (if c then f1 else f2) x = if c then f1 x else f2 x.
  Proof. intros. destruct c; reflexivity. Qed.

  Lemma pair_eq_acc: forall T1 T2 (a: T1) (b: T2) t,
    t = (a, b) -> a = fst t /\ b = snd t.
  Proof. intros. destruct t. inversionss. auto. Qed.

  Definition runsToSatisfying(imem: InstructionMem):
    RiscvMachine -> (RiscvMachine -> Prop) -> Prop :=
    runsTo RiscvMachine (execState (run1 imem)).

  Lemma execState_compose{S A: Type}: forall (m1 m2: OState S A) (initial: S),
    execState m2 (execState m1 initial) = execState (m1 ;; m2) initial.
  Proof.
    intros. unfold execState. unfold Bind, Return, OState_Monad.
    destruct (m1 initial). simpl. destruct o; try reflexivity.
  Abort.

  Lemma runsToSatisfying_exists_fuel_old: forall imem initial P,
    runsToSatisfying imem initial P ->
    exists fuel, P (execState (run imem fuel) initial).
  Proof.
    introv R. induction R.
    - exists 0. exact H.
    - destruct IHR as [fuel IH]. exists (S fuel).
      unfold run in *.
      (*
      rewrite execState_compose in IH.
      apply IH.
      *)
  Abort.

  Lemma runsToSatisfying_exists_fuel: forall imem initial P,
    runsToSatisfying imem initial P ->
    exists fuel, P (execState (run imem fuel) initial).
  Proof.
    intros *. intro R.
    pose proof (runsToSatisfying_exists_fuel _ _ initial P R) as F.
    unfold run.
    destruct F as [fuel F]. exists fuel.
    replace
      (execState (power_func (fun m => run1 imem;; m) fuel (Return tt)) initial)
    with
      (power_func (execState (run1 imem)) fuel initial);
    [assumption|clear].
    revert initial.
    induction fuel; intros; simpl; [reflexivity|].
    unfold execState. f_equal.
    destruct (run1 imem initial) eqn: E.
    destruct o eqn: Eo.
    (* TODO does that hold? What if optional answer is None and it aborts? *)
  Admitted.

  (* not needed any more because we keep the instruction memory external: 
  Lemma execute_preserves_instructionMem: forall inst initial,
    (snd (execute inst initial)).(instructionMem) = initial.(instructionMem).
  Proof.
    intros. destruct initial as [machine imem]. unfold execute.
    unfold ExecuteI.execute, ExecuteM.execute, ExecuteI64.execute, ExecuteM64.execute.

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
*)

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
      clear.
      destruct wXLEN as [|w1] eqn: E.
      + unfold wXLEN in *. destruct bitwidth; discriminate.
      + rewrite roundTrip_1. simpl. constructor.
    - destruct (@wlt_dec wXLEN (y ^- z) $ (1)) as [E|NE]; [|reflexivity].
      exfalso. apply n. apply sub_0_eq.
      unfold wlt in E.
      do 2 rewrite wordToN_nat in E.
      clear -E.
      destruct wXLEN as [|w1] eqn: F.
      + unfold wXLEN in *. destruct bitwidth; discriminate.
      + rewrite roundTrip_1 in E.
        simpl in E. apply N.lt_1_r in E. change 0%N with (N.of_nat 0) in E.
        apply Nnat.Nat2N.inj in E. rewrite <- (roundTrip_0 (S w1)) in E.
        apply wordToNat_inj in E.
        exact E.
  Qed.

  Ltac simpl_run1 :=
    cbv [run1 execState Monads.put Monads.gets Monads.get Return Bind State_Monad OState_Monad
         execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute
         core machineMem registers pc nextPC exceptionHandlerAddr
         getPC setPC getRegister setRegister IsRiscvMachine gets].

  Ltac simpl_RiscvMachine_get_set :=
    cbn [core machineMem registers pc nextPC exceptionHandlerAddr
         with_registers with_pc with_nextPC with_exceptionHandlerAddr with_machineMem] in *.
  
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
  
  Tactic Notation "log_solved" tactic(t) :=
    match goal with
    | |- ?G => let H := fresh in assert G as H by t; idtac "solved" G; exact H
    | |- ?G => idtac "did not solve" G
    end.
  
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
(*
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
  Qed.*)

  Definition evalH := eval_stmt (w := wXLEN).

  (* separate definition to better guide automation: don't simpl 16, but keep it as a 
     constant to stay in linear arithmetic *)
  Local Definition stmt_not_too_big(s: stmt): Prop := stmt_size s * 16 < pow2 20.

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

  (*
  Local Ltac solve_pc_update :=
    rewrite? extz_is_mult_pow2;
    rewrite? sext_natToWord_nat_cast;
    simpl_pow2;
    [ solve_word_eq | solve_length_compile_stmt ].
   *)

  Definition list2imem(l: list Instruction)(offset: word wXLEN): InstructionMem :=
    fun addr => nth (wordToNat (wdiv (addr ^- offset) $4)) l InvalidInstruction.

  (*
  Definition loadWordH(memH: Memory.mem wXLEN)(addr: word wXLEN): option (word wXLEN).
    clear -addr memH.
    unfold wXLEN in *.
    destruct bitwidth; exact (compiler.Memory.read_mem addr memH).
  Defined.
   *)

  Ltac destruct_RiscvMachine m :=
    let t := type of m in
    unify t RiscvMachine;
    let r := fresh m "_regs" in
    let p := fresh m "_pc" in
    let n := fresh m "_npc" in
    let e := fresh m "_eh" in
    let me := fresh m "_mem" in
    destruct m as [ [r p n e] me ];
    simpl_RiscvMachine_get_set.

  Definition loadWordL(memL: FunctionMemory.mem wXLEN)(addr: word wXLEN): option (word wXLEN).
    clear -addr memL.
    unfold wXLEN in *.
    destruct bitwidth; apply Some.
    - exact (Memory.loadWord memL addr).
    - exact (Memory.loadDouble memL addr).
  Defined.
  
  Definition containsMem(memL: FunctionMemory.mem wXLEN)(memH: Memory.mem wXLEN): Prop :=
    forall addr v, memH addr = Some v -> loadWordL memL addr = Some v.

  (* TODO might not hold if a = 0, but we only use it with a = 4 *)
  Lemma wzero_div: forall sz a, wzero sz ^/ a = wzero sz. Admitted.

  (* TODO might not hold if a = 0, but we only use it with a = 4 *)  
  Lemma mul_div_undo_word: forall {sz} (a b: word sz), a ^* b ^/ a = b. Admitted.
  
  Lemma run1head: forall inst0 insts initialL,
      execState (run1 (list2imem (inst0 :: insts) initialL.(core).(pc))) initialL =
      execState (execute inst0;; step) initialL.
  Proof.
    intros.
    unfold list2imem.
    unfold run1.
    unfold getPC, IsRiscvMachine, OState_Monad.
    destruct_RiscvMachine initialL.
    unfold Bind at 1.
    unfold execState.
    unfold Monads.get.
    unfold Bind at 1.
    unfold Return at 1.
    rewrite wminus_def.
    rewrite wminus_inv.
    rewrite wzero_div.
    rewrite wordToNat_wzero.
    simpl nth.
    reflexivity.
  Qed.

  Lemma run1_in_list: forall n inst insts initialL offset,
      nth_error insts n = Some inst ->
      initialL.(core).(pc) = offset ^+ $4 ^* $n ->
      execState (run1 (list2imem insts offset)) initialL =
      execState (execute inst;; step) initialL.
  Proof.
    intros.
    unfold list2imem.
    unfold run1.
    unfold getPC, IsRiscvMachine, OState_Monad.
    destruct_RiscvMachine initialL.
    unfold Bind at 1.
    unfold execState.
    unfold Monads.get.
    unfold Bind at 1.
    unfold Return at 1.
    subst.
    simpl.
    rewrite wminus_def.
    rewrite wplus_comm.
    rewrite wplus_assoc.
    rewrite (wplus_comm (^~ offset) offset).
    rewrite wminus_inv.
    rewrite wplus_unit.
    rewrite mul_div_undo_word.
    erewrite nth_error_nth; [ reflexivity | ].
  Abort.

  Lemma run1_in_list: forall n inst insts initialL offset,
      nth_error insts (wordToNat n) = Some inst ->
      initialL.(core).(pc) = offset ^+ $4 ^* n ->
      execState (run1 (list2imem insts offset)) initialL =
      execState (execute inst;; step) initialL.
  Proof.
    intros.
    unfold list2imem.
    unfold run1.
    unfold getPC, IsRiscvMachine, OState_Monad.
    destruct_RiscvMachine initialL.
    unfold Bind at 1.
    unfold execState.
    unfold Monads.get.
    unfold Bind at 1.
    unfold Return at 1.
    subst.
    simpl.
    rewrite wminus_def.
    rewrite wplus_comm.
    rewrite wplus_assoc.
    rewrite (wplus_comm (^~ offset) offset).
    rewrite wminus_inv.
    rewrite wplus_unit.
    rewrite mul_div_undo_word.
    erewrite nth_error_nth; [ reflexivity | assumption].
  Qed.
  
  Lemma run1_in_im_0: forall im initialL,
      execState (run1 im) initialL =
      execState (execute (im initialL.(core).(pc));; step) initialL.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma run1_in_im: forall im initialL inst,
      im initialL.(core).(pc) = inst ->
      execState (run1 im) initialL =
      execState (execute inst;; step) initialL.
  Proof.
    intros. subst. reflexivity.
  Qed.
  
  Lemma Bind_getRegister0: forall {A: Type} (f: word wXLEN -> OState RiscvMachine A),
      Bind (getRegister Register0) f = f $0.
  Proof.
    intros. reflexivity.
  Qed.

  Lemma Bind_getRegister: forall {A: Type} x
                                 (f: word wXLEN -> OState RiscvMachine A)
                                 (initialL: RiscvMachine),
      valid_register x ->
      execState (Bind (getRegister x) f) initialL =
      execState (f (getReg initialL.(core).(registers) x)) initialL.
  Proof.
    intros. simpl.
    destruct_one_match.
    - exfalso. unfold valid_register, Register0 in *. omega.
    - reflexivity.
  Qed.

  Lemma Bind_setRegister: forall {A: Type} x (v: word wXLEN)
                                 (f: unit -> OState RiscvMachine A) (initialL: RiscvMachine),
      valid_register x ->
      execState (Bind (setRegister x v) f) initialL =
      execState (f tt) (with_registers (setReg initialL.(core).(registers) x v) initialL).
  Proof.
    intros. simpl.
    destruct_one_match.
    - exfalso. unfold valid_register, Register0 in *. omega.
    - reflexivity.
  Qed.

  Lemma Bind_step: forall {A: Type} (f: unit -> OState RiscvMachine A) m,
      execState (Bind step f) m =
      execState (f tt) (with_nextPC (m.(core).(nextPC) ^+ $4) (with_pc m.(core).(nextPC) m)).
  Proof.
    intros. reflexivity.
  Qed.

  Lemma execState_step: forall m,
      execState step m = with_nextPC (m.(core).(nextPC) ^+ $4) (with_pc m.(core).(nextPC) m).
  Proof.
    intros. reflexivity.
  Qed.
  
  Lemma execState_Return: forall {S A} (s: S) (a: A),
      execState (Return a) s = s.
  Proof. intros. reflexivity. Qed.

  Ltac prove_alu_def :=
    intros; clear; unfold wXLEN in *; unfold MachineWidthInst;
    destruct bitwidth; [unfold MachineWidth32 | unfold MachineWidth64]; reflexivity.
  
  Lemma fromImm_def: forall (a: Z),
      Utility.fromImm a = ZToWord wXLEN a.
  Proof. unfold fromImm. prove_alu_def. Qed.

  Lemma zero_def:
      Utility.zero = $0.
  Proof. unfold zero. prove_alu_def. Qed.
  
  Lemma one_def:
      Utility.one = $1.
  Proof. unfold one. prove_alu_def. Qed.
  
  Lemma add_def: forall (a b: word wXLEN),
      Utility.add a b = wplus a b.
  Proof. unfold add. prove_alu_def. Qed.
  
  Lemma sub_def: forall (a b: word wXLEN),
      Utility.sub a b = wminus a b.
  Proof. unfold sub. prove_alu_def. Qed.
  
  Lemma mul_def: forall (a b: word wXLEN),
      Utility.mul a b = wmult a b.
  Proof. unfold mul. prove_alu_def. Qed.
  
  Lemma div_def: forall (a b: word wXLEN),
      Utility.div a b = ZToWord wXLEN (wordToZ a / wordToZ b).
  Proof. unfold div. prove_alu_def. Qed.
  
  Lemma rem_def: forall (a b: word wXLEN),
      Utility.rem a b = ZToWord wXLEN (wordToZ a mod wordToZ b).
  Proof. unfold rem. prove_alu_def. Qed.
  
  Lemma signed_less_than_def: forall (a b: word wXLEN),
      Utility.signed_less_than a b = if wslt_dec a b then true else false.
  Proof. unfold signed_less_than. prove_alu_def. Qed.
  
  Lemma signed_eqb_def: forall (a b: word wXLEN),
      Utility.signed_eqb a b = weqb a b.
  Proof. unfold signed_eqb. prove_alu_def. Qed.
  
  Lemma aor_def: forall (a b: word wXLEN),
      Utility.xor a b = wxor a b.
  Proof. unfold xor. prove_alu_def. Qed.
  
  Lemma or_def: forall (a b: word wXLEN),
      Utility.or a b = wor a b.
  Proof. unfold or. prove_alu_def. Qed.
  
  Lemma and_def: forall (a b: word wXLEN),
      Utility.and a b = wand a b.
  Proof. unfold and. prove_alu_def. Qed.
  
  Lemma sll_def: forall (a: word wXLEN) (b: Z),
      Utility.sll a b = wlshift a (Z.to_nat b).
  Proof. unfold sll. prove_alu_def. Qed.
  
  Lemma srl_def: forall (a: word wXLEN) (b: Z),
      Utility.srl a b = wrshift a (Z.to_nat b).
  Proof. unfold srl. prove_alu_def. Qed.
  
  Lemma sra_def: forall (a: word wXLEN) (b: Z),
      Utility.sra a b = wrshift a (Z.to_nat b).
  Proof. unfold sra. prove_alu_def. Qed.
  
  Lemma ltu_def: forall (a b: word wXLEN),
      Utility.ltu a b = if wlt_dec a b then true else false.
  Proof. unfold ltu. prove_alu_def. Qed.
  
  Lemma divu_def: forall (a b: word wXLEN),
      Utility.divu a b = wdiv a b.
  Proof. unfold divu. prove_alu_def. Qed.
  
  Lemma remu_def: forall (a b: word wXLEN),
      Utility.remu a b = wmod a b.
  Proof. unfold remu. prove_alu_def. Qed.
  
  
  Hint Unfold
    Nop
    Mov
    Not
    Neg
    Negw
    Sextw
    Seqz
    Snez
    Sltz
    Sgtz
    Beqz
    Bnez
    Blez
    Bgez
    Bltz
    Bgtz
    Bgt
    Ble
    Bgtu
    Bleu
    J
    Jr
  : unf_pseudo.


  Lemma list2imem_head: forall inst insts imemStart,
      (list2imem (inst :: insts) imemStart) imemStart = inst.
  Proof.
    intros.
    unfold list2imem.
    rewrite wminus_def.
    rewrite wminus_inv.
    rewrite wzero_div.
    rewrite wordToNat_wzero.
    reflexivity.
  Qed.

  Lemma list2imem_skip: forall imemStart insts0 insts1 offs pc0,
    imemStart ^+ $4 ^* $(length insts0) ^+ offs = pc0 ->
    (list2imem (insts0 ++ insts1) imemStart) pc0  =
    (list2imem insts1 imemStart) (imemStart ^+ offs).
  Proof.
    intros. subst.
    unfold list2imem.
    rewrite wminus_def.
    rewrite wplus_comm.
    rewrite? wplus_assoc.
    rewrite (wplus_comm (^~ imemStart) imemStart).
    rewrite wminus_inv.
    rewrite wplus_unit.
    rewrite wminus_def.
    rewrite (wplus_comm imemStart).
    rewrite <- wplus_assoc.
    rewrite wminus_inv.
    rewrite <- (wplus_comm (wzero wXLEN)).
    rewrite wplus_unit.
    replace ((($4 ^* $ (length insts0) ^+ offs) ^/ $4)) with
        ($ (length insts0) ^+ (offs ^/ $4)) by admit.
    
    Abort.

  Definition wnth{A}{sz}(n: word sz)(l: list A)(default: A): A. Admitted.

  Definition wlength{A}{sz}(l: list A): word sz. Admitted.
  
  (*
  Lemma wnth_app_2:
    wnth (a ^+ b) (insts0 ++ insts1) InvalidInstruction =
  *)
  Definition list2imem'(l: list Instruction)(offset: word wXLEN): InstructionMem :=
    fun addr => wnth (wdiv (addr ^- offset) $4) l InvalidInstruction.

  Lemma list2imem_skip: forall imemStart insts0 insts1 offs pc0,
    imemStart ^+ $4 ^* (wlength insts0) ^+ offs = pc0 ->
    (list2imem' (insts0 ++ insts1) imemStart) pc0  =
    (list2imem' insts1 imemStart) (imemStart ^+ offs).
  Proof.
    intros. unfold list2imem'. subst pc0.
    rewrite wminus_def.
    rewrite wplus_comm.
    rewrite? wplus_assoc.
    rewrite (wplus_comm (^~ imemStart) imemStart).
    rewrite wminus_inv.
    rewrite wplus_unit.
    rewrite wminus_def.
    rewrite (wplus_comm imemStart).
    rewrite <- wplus_assoc.
    rewrite wminus_inv.
    rewrite <- (wplus_comm (wzero wXLEN)).
    rewrite wplus_unit.
    replace ((($4 ^* (wlength insts0) ^+ offs) ^/ $4)) with
        ((wlength insts0) ^+ (offs ^/ $4)) by admit.
    (* does not hold without additional size constraint assumption! *)

    (*
    rewrite app_nth2. (* stupid overflow of offs possible! *)
     *)
  Abort.
  
  Lemma list2imem_skip: forall imemStart insts0 insts1 offs pc0,
    imemStart ^+ $4 ^* $(length insts0) ^+ $4 ^* $offs = pc0 ->
    (list2imem (insts0 ++ insts1) imemStart) pc0  =
    (list2imem insts1 imemStart) (imemStart ^+ $4 ^* $offs).
  Proof.
    intros. subst.
    unfold list2imem.
    rewrite wminus_def.
    rewrite wplus_comm.
    rewrite? wplus_assoc.
    rewrite (wplus_comm (^~ imemStart) imemStart).
    rewrite wminus_inv.
    rewrite wplus_unit. rewrite app_nth2. (* stupid overflow of offs possible! *)

(* how to simplify this?:
    
list2imem
    (instsBefore ++
     (compile_stmt s1 ++
      Beq cond Register0
        (Z.pos (Pos.of_succ_nat (length (compile_stmt s2) + S (length (compile_stmt s2) + 0))))
      :: compile_stmt s2 ++
         [[Jal Register0
             (Z.neg
                (Pos.succ
                   (Pos.of_succ_nat
                      (length (compile_stmt s1) + length (compile_stmt s2) +
                       S (S (length (compile_stmt s1) + length (compile_stmt s2) + 0))))))]]) ++
     instsAfter) imemStart
    (imemStart ^+ $ (4) ^* $ (length instsBefore) ^+ $ (4) ^* $ (length (compile_stmt s1)))
 *)
    
  Lemma compile_stmt_correct_aux:
    forall fuelH s insts instsBefore instsAfter initialH imemStart
           initialMH finalH finalMH initialL,
    compile_stmt s = insts ->
    stmt_not_too_big s ->
    valid_registers s ->
    evalH fuelH initialH initialMH s = Some (finalH, finalMH) ->
    extends initialL.(core).(registers) initialH ->
    containsMem initialL.(machineMem) initialMH ->
    imemStart ^+ $4 ^* $(length instsBefore) = initialL.(core).(pc) ->
    initialL.(core).(pc) ^+ $4 = initialL.(core).(nextPC) ->
    runsToSatisfying (list2imem (instsBefore ++ insts ++ instsAfter) imemStart)
                     initialL
                     (fun finalL => extends finalL.(core).(registers) finalH /\
                                    containsMem finalL.(machineMem) finalMH /\
                                    finalL.(core).(pc) ^+ $4 = finalL.(core).(nextPC) /\
                                    finalL.(core).(pc) =
                                      initialL.(core).(pc) ^+ $ (4) ^* $ (length insts)).
  Proof.
    induction fuelH; [intros; discriminate |].
    intros *.
    intros C Csz V EvH Cs Cm Ims Pc.
    unfold evalH in EvH.
    invert_eval_stmt.
    - (* SLoad *)
      admit.
    - (* SStore *)
      admit.
    - (* SLit *)
      (*
      destruct_pair_eqs. simpl in V.
      subst *.
      unfold compile_stmt, compile_lit. destruct bitwidth eqn: EBw.
      { (* 32bit *)
      unfold compile_lit_32.
      destruct_one_match.
      {
      apply runsToStep. apply runsToDone.
      rewrite run1head.
      unfold execute, ExecuteI.execute, ExecuteM.execute, ExecuteI64.execute, ExecuteM64.execute.
      rewrite associativity.
      rewrite Bind_getRegister0 by assumption.
      rewrite Bind_setRegister by assumption.
      rewrite <- (right_identity step).
      rewrite Bind_step.
      rewrite (@execState_Return RiscvMachine unit _).
      destruct_RiscvMachine initialL.
      subst.
      simpl.
      rewrite wmult_unit_r.
      repeat split; try assumption; try reflexivity; let n := numgoals in guard n = 1.
      rewrite add_def.
      simpl in e. rewrite e.
      rewrite wplus_wzero_2.
      rewrite fromImm_def.
      rewrite ZToWord_wordToZ.
      clear -Cs.
      state_calc.
      }
      {
        (* TODO 20-32bit literals *)
        admit.
      }
      }
      {
        (* TODO 64-bit literals *)
        admit.
      }
       *)
      admit.
    - (* SOp *)
      (*
      simpl in C. destruct_pair_eqs. subst *. simpl in V. destruct V as [ ? [? ?] ].
      (* destruct_RiscvMachine initialL. *)
      (*
      pose proof Cs as Cs'.
      unfold containsState in Cs. simpl in Cs.
      rename H into Gy, H0 into Gz. apply Cs in Gy. apply Cs in Gz.
      subst x0 x1.
       *)
      clear IHfuelH.
      destruct op. {

      simpl.
      unfold runsToSatisfying.
      
      apply runsToStep.
      rewrite run1head.
      cbn [execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute].
      Close Scope monad_scope.
      rewrite associativity.
      rewrite Bind_getRegister by assumption.
      rewrite associativity.
      rewrite Bind_getRegister by assumption.
      rewrite Bind_setRegister by assumption.
      rewrite <- (right_identity step).
      rewrite Bind_step.
      rewrite (@execState_Return RiscvMachine unit _).
      destruct_RiscvMachine initialL.
      subst.
      apply runsToDone.
      simpl_RiscvMachine_get_set.
      refine (conj _ (conj _ (conj _ _)));
        [ | | log_solved solve_word_eq | log_solved solve_word_eq ].
      + rewrite add_def.
        unfold getReg, setReg, State_is_RegisterFile.
        (* TODO state_calc or something similar should do this automatically *)
        replace (get initialL_regs y) with (Some v1) by admit.
        replace (get initialL_regs z) with (Some v2) by admit.
        state_calc.
      + assumption.
      }
admit. admit.        
      {
        simpl.
        unfold runsToSatisfying.

        Ltac do_1_step :=        
          apply runsToStep;
          rewrite run1head;
          autounfold with unf_pseudo in *;
          cbn [execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute];
          repeat (
              rewrite? associativity;
              ((rewrite Bind_getRegister by assumption) ||
               (rewrite Bind_getRegister0) ||
               (rewrite Bind_setRegister by assumption))
            );
          rewrite execState_step.

      do_1_step.

      Ltac runsTo_done :=
      apply runsToDone;
      refine (conj _ (conj _ (conj _ _))); simpl;
        [ | | log_solved solve_word_eq | log_solved solve_word_eq ];
        let n := numgoals in guard n = 2.
        (* otherwise the pc equality goals were not solved, which means that we cannot
           apply runsToDone *)
      destruct_RiscvMachine initialL; subst *.
      try runsTo_done.
            
      simpl_RiscvMachine_get_set.
      apply runsToStep.
      
      match goal with
      | |- context [execState (run1 (list2imem ?insts _)) _] =>
        let i := eval simpl in (nth 1 insts InvalidInstruction) in
            rewrite run1_in_list with (n := $1) (inst := i)
      end;
        [ | replace (wordToNat (natToWord wXLEN 1)) with 1 by admit; reflexivity
          | simpl; solve_word_eq ].

          autounfold with unf_pseudo in *;
          cbn [execute ExecuteI.execute ExecuteM.execute ExecuteI64.execute ExecuteM64.execute];
          repeat (
              rewrite? associativity;
              ((rewrite Bind_getRegister by assumption) ||
               (rewrite Bind_getRegister0) ||
               (rewrite Bind_setRegister by assumption))
            );
          rewrite execState_step.
          simpl.
          runsTo_done; [|assumption].
          destruct (dec (x = x)); [|contradiction].
          rewrite sub_def.
          rewrite ltu_def.
          rewrite fromImm_def.
          rewrite one_def.
          rewrite zero_def.
          replace (ZToWord wXLEN 1) with (natToWord wXLEN 1) by admit.
      pose proof Cs as Cs'.
      unfold extends in Cs. simpl in Cs.
      apply Cs in EvH0. apply Cs in EvH1.
      rewrite EvH0, EvH1.
      rewrite get_put_same.
      rewrite reduce_eq_to_sub_and_lt.
      repeat destruct_one_match (* 4 subgoals just because stupid *);       
      state_calc.
      }
      admit. admit.      
       *)
      admit.
    - (* SSet *)
      (*
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
       *)
      admit.
    - (* SIf/Then *)
      (*
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
       *)
      admit.
    - (* SIf/Else *)
      (*
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
       *)
      admit.
    - (* SLoop/done *)
      (*
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
       *)
      admit.
    - (* SLoop/again *)
      simpl in C. subst *.
      simpl in V. destruct V as [ ? [? ?] ].
      pose proof IHfuelH as IH.
      destruct_RiscvMachine initialL.
      match goal with
      | |- runsToSatisfying _ ?st _ => specialize IHfuelH with (initialL := st); simpl in IHfuelH
      end.
      specialize (IHfuelH s1).
      specializes IHfuelH; [reflexivity|solve_stmt_not_too_big|eassumption..|].
      unfold runsToSatisfying in *.
      match goal with
      | IH: runsTo _ (execState (run1 (list2imem ?im1 ?ims))) _ _ |-
            runsTo _ (execState (run1 (list2imem ?im2 ?ims))) _ _ =>
        replace im1 with im2 in IH
          by (repeat rewrite <- app_assoc; reflexivity)
      end.
      apply (runsToSatisfying_trans _ _ _ _ _ IHfuelH). clear IHfuelH.
      intros middleL [ E [? [? ?] ] ].
      destruct_RiscvMachine middleL.
      simpl in *. subst *.
      apply runsToStep.
      erewrite run1_in_im.
      admit.

      { simpl.
        (* HERE *)
        }
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
