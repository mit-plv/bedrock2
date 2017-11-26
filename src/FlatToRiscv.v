Require Import lib.LibTactics.
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
  Context {var: Set}. (* var in the source language is the same as Register in the target language *)
  Context {R0: var}. (* register #0 is the read-only constant 0 *)
  Context {eq_var_dec: DecidableEq var}.
  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.
  
  Definition compile_op(rd: var)(op: binop)(rs1 rs2: var): list (@Instruction var) :=
    match op with
    | OPlus => [Add rd rs1 rs2]
    | OMinus => [Sub rd rs1 rs2]
    | OTimes => [Mul rd rs1 rs2]
    | OEq => [Add rd R0 R0; Bne rs1 rs2 $4; Addi rd R0 $1] (* TODO super inefficient *)
    | OLt => [Add rd R0 R0; Bge rs1 rs2 $4; Addi rd R0 $1] (* TODO super inefficient *)
    | OAnd => [And rd rs1 rs2]
    end.

  (* using the same names (var) in source and target language *)
  Fixpoint compile_stmt(s: @stmt w var): list (@Instruction var) :=
    match s with
    | SLit x v => [Addi x R0 (zcast 12 v)] (* only works if literal is < 2^12 *)
    | SOp x op y z => compile_op x op y z
    | SSet x y => [Add x y R0]
    | SIf cond bThen bElse =>
        let bThen' := compile_stmt bThen in
        let bElse' := compile_stmt bElse in
        (* only works if branch lengths are < 2^12 *)
        [Beq cond R0 $(S (length bThen'))] ++ bThen' ++ [Jal R0 $(length bElse')] ++ bElse'
    | SLoop body1 cond body2 =>
        let body1' := compile_stmt body1 in
        let body2' := compile_stmt body2 in
        (* only works if branch lengths are < 2^12 *)
        body1' ++
        [Beq cond R0 $(S (length body2'))] ++
        body2' ++
        [Jal R0 (wneg $(S (length body1' + length body2')))]
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
  Definition myRiscvMachine := @IsRiscvMachine w var R0 _.
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

  Lemma compile_stmt_correct_aux: forall fuelH s insts initialH finalH initialL,
    compile_stmt s = insts ->
    eval_stmt fuelH initialH s = Success finalH ->
    containsProgram initialL insts initialL.(pc) ->
    containsState initialL initialH ->
    exists (fuelL: nat) (finalL: RiscvMachine),
      execState (run fuelL) initialL = finalL /\
      containsState finalL finalH.
  Proof.
    induction fuelH; [intros; discriminate |].
    introv C EvH Cp Cs.
    invert_eval_stmt.
    - subst.
      apply containsProgram_cons_inv in Cp. apply proj1 in Cp.
      destruct initialL as [initialProg initialRegs initialPc].
      exists 1. eexists. simpl.
      split.
      + cbv [execState StateMonad.put execute instructionMem registers pc].
        simpl in Cp.
        rewrite Cp. simpl. reflexivity.
      + eapply containsState_put; [eassumption|].
        (* TODO holds if we add the right assumptions *) admit.
    - simpl in C. subst.
      destruct initialL as [initialProg initialRegs initialPc].
      simpl in Cp.
      unfold containsState in Cs. simpl in Cs.
      rename H into Gy, H0 into Gz. apply Cs in Gy. apply Cs in Gz.
      subst x0 x1.
      destruct op;
      lazymatch goal with
      | Cp: containsProgram ?s ?p ?PC |- _ =>
        let p' := eval simpl in p in
        change (containsProgram s p' PC) in Cp;
        let l := eval cbv in (length p') in exists l;
        eexists; (split;
        [ cbv [run execState StateMonad.put execute instructionMem registers 
               pc getPC loadInst setPC getRegister setRegister myRiscvMachine IsRiscvMachine gets
               StateMonad.get Return Bind State_Monad ];
          repeat (
            apply containsProgram_cons_inv in Cp;
            let Cp' := fresh Cp in 
            destruct Cp as [Cp' Cp];
            simpl in Cp'
          );
          repeat match goal with
          | E: ?t = ?rhs |- context [?t] => rewrite E
          end;
          simpl;
          lazymatch goal with
          | |- mkRiscvMachine _ _ _ = _ => reflexivity
          | |- _ => idtac
          end
        | try (unify l 1; eapply containsState_put; [eassumption|reflexivity]) ])
      end.
      { assert (initialRegs R0 ^+ initialRegs R0 = $0) as ER0 by admit. (* TODO *)
        rewrite ER0.
        match goal with
        | |- context [weq ?a ?b] => destruct (weq a b) eqn: E
        end.
        - rewrite Cp2. simpl. reflexivity.
        - (* problem: here we should only have made 2 steps instead of 3 *)


  Abort.


End FlatToRiscv.
