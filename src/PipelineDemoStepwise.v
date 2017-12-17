Require Import Coq.Lists.List.
Import ListNotations.
Require Import bbv.Word.
Require Import compiler.Decidable.
Require Import compiler.Op.
Require Import compiler.member.
Require Import compiler.ForWord.
Require Import compiler.LLG.
Require        compiler.LLG2FlatImp.
Require Import compiler.FlatImp.
Require Import compiler.ResMonad.
Require        compiler.FlatToRiscv.
Require Import compiler.Riscv.
Require Import compiler.Machine.
Require Import compiler.StateMonad.

Definition myvar := nat.
Definition var_x1: myvar := 3.
Definition var_x2: myvar := 4.
Definition var_i: myvar := 5.
Definition w := 8. (* bit width *)


Definition empty_types: member (@nil myvar) -> type. intro. inversion H. Defined.
Definition empty_vals: forall m : member (@nil myvar), @interp_type w (empty_types m).
  intro. inversion m. Defined.

Definition p1_LLG(n: word w): word w :=
  let x1 := $0 in
  for i from 0 to n updating (x1) {{
     let x2 := x1 ^+ i ^* i in
     x2
  }} ;;
  x1.

Goal [p1_LLG $1; p1_LLG $2; p1_LLG $3; p1_LLG $4] = [$0; $1; $5; $14]. reflexivity. Qed.

Definition x1_in_ix1: member [var_i; var_x1]. apply member_there. apply member_here. Defined.
Definition i_in_ix1: member [var_i; var_x1]. apply member_here. Defined.
Definition x1_in_x1: member [var_x1]. apply member_here. Defined.
Definition x2_in_x2ix1: member [var_x2; var_i; var_x1]. apply member_here. Defined.

Definition p1_LLG_ast(n: word w): expr (@nil myvar) empty_types TInt :=
  ELet var_x1 (ELit $0)
  (EFor var_i (ELit n) x1_in_x1
     (ELet var_x2 (EOp (EVar x1_in_ix1) OPlus (EOp (EVar i_in_ix1) OTimes (EVar i_in_ix1)))
     (EVar x2_in_x2ix1))
  (EVar x1_in_x1)).

Definition interp_expr'{t}(e: expr (@nil myvar) empty_types t): interp_type t :=
  interp_expr e empty_vals.

Goal forall n, p1_LLG n = interp_expr' (p1_LLG_ast n). intros. reflexivity. Qed.

Goal forall n, p1_LLG n = interp_expr' (p1_LLG_ast n).
  intros. unfold p1_LLG. unfold interp_expr', interp_expr. cbn. reflexivity.
Qed.

Definition nameGenState_initial: myvar := 10. (* should be bigger than all vars used in source *)

Definition compileLLG2FlatImp{l G t}(e: expr l G t): @stmt w myvar * myvar :=
  fst (LLG2FlatImp.compile nameGenState_initial e).

Definition p1_FlatImp(n: word w): @stmt w myvar * myvar := compileLLG2FlatImp (p1_LLG_ast n).

Definition p1_FlatImp'(n: word w): @stmt w myvar * myvar :=
  ltac:(let r := eval cbv -[natToWord] in (p1_FlatImp n) in exact r).

Definition p1_FlatImp_stmt(n: word w): @stmt w myvar := 
  ltac:(let r := eval cbv -[natToWord] in (fst (p1_FlatImp n)) in exact r).

Definition p1_FlatImp_resVar(n: word w): myvar := 
  ltac:(let r := eval cbv -[natToWord] in (snd (p1_FlatImp n)) in exact r).

Definition lotsOfFuel := 100.

Definition mystate := myvar -> option (word w).

Definition empty_state: mystate := fun _ => None.

Definition eval_FlatImp_stmt(s: @stmt w myvar * myvar): option (word w) :=
  match eval_stmt lotsOfFuel empty_state (fst s) with
  | Success final => final (snd s)
  | _ => None
  end.

Transparent wlt_dec.

Goal eval_FlatImp_stmt (p1_FlatImp $4) = Some $14. reflexivity. Qed.

Definition compileFlat2Riscv(f: @stmt w myvar): list (@Instruction myvar) :=
  compiler.FlatToRiscv.compile_stmt f.

Definition p1_riscv(n: word w): list (@Instruction myvar) := compileFlat2Riscv (p1_FlatImp_stmt n).

Goal False. set (r := p1_riscv $3). cbv in *. Abort.

Definition lotsOfFuel_lowlevel := 100.

Definition myInst := (@IsRiscvMachine w nat _).
Existing Instance myInst.

Definition runThenGet(resVar: myvar): State RiscvMachine (word w) :=
  run lotsOfFuel_lowlevel;;
  getRegister (RegS resVar).

Definition go(p: list (@Instruction myvar))(resVar: myvar): word w :=
  evalState (runThenGet resVar) (initialRiscvMachine p).

Import compiler.FlatToRiscv.

Lemma nth_error_nth: forall {T: Type} (l: list T) (e d: T) (i: nat),
  nth_error l i = Some e ->
  nth i l d = e.
Proof.
  intros T l. induction l; intros.
  - destruct i; simpl in H; discriminate.
  - destruct i; simpl in H; inversion H; subst.
    + reflexivity.
    + simpl. auto.
Qed.

Lemma initialRiscvMachine_containsProgram: forall w var p,
  @containsProgram w var (initialRiscvMachine p) p (pc (initialRiscvMachine p)).
Proof.
  intros. unfold containsProgram, initialRiscvMachine. simpl.
  intros. apply nth_error_nth.
  match goal with
  | H: nth_error _ ?i1 = _ |- nth_error _ ?i2 = _ => replace i2 with i1; [assumption|]
  end.
  unfold wdiv, wordBin.
  rewrite wplus_unit.
  rewrite <- natToWord_mult.
  rewrite? wordToN_nat.
  rewrite? wordToNat_natToWord_idempotent'.
Admitted.

Lemma every_state_contains_empty_state: forall s,
  containsState s empty_state.
Proof.
  unfold containsState.
  intros. inversion H.
Qed.

(*
Axiom flat_src_correct: forall n, exists fuelH finalH,
  eval_stmt fuelH empty_state (p1_FlatImp_stmt $ (n)) = Success finalH.
*)

Require Import Omega.

Lemma p1_runs_correctly_1: forall n resVar fuelH finalH,
  eval_stmt fuelH empty_state (p1_FlatImp_stmt $ (n)) = Success finalH ->
  Common.get finalH resVar <> None ->
  exists fuelL,
  Some ((execState (run fuelL) (initialRiscvMachine (p1_riscv $n))).(registers) resVar)
  = Common.get finalH resVar.
Proof.
  intro n. intros resVar fuelH finalH E G.
  change (exists fuel, 
   (fun final => Some (registers final resVar) = finalH resVar)
   (execState (run fuel) (initialRiscvMachine (p1_riscv $n)))).
  apply runsToSatisfying_exists_fuel.
  eapply runsToSatisfying_imp.
  - eapply compile_stmt_correct_aux with
     (s := (p1_FlatImp_stmt $n)) (initialH := empty_state) (fuelH0 := fuelH) (finalH0 := finalH).
    + reflexivity.
    + simpl. omega.
    + apply E.
    + unfold p1_riscv.
      unfold compileFlat2Riscv in *.
      remember (compile_stmt (p1_FlatImp_stmt $n)) as p.
      apply initialRiscvMachine_containsProgram.
    + apply every_state_contains_empty_state.
    + reflexivity.
  - intros.
    simpl in H. apply proj1 in H.
    unfold containsState in H.
    specialize (H resVar).
    destruct (Common.get finalH resVar) eqn: Q.
    + specialize (H _ eq_refl).
      simpl in Q. unfold id in Q. congruence.
    + contradiction.
Qed.

Goal exists fuel, 
  (execState (run fuel) (initialRiscvMachine (p1_riscv $4))).(registers)
    (p1_FlatImp_resVar $4)
  = $14.
Proof.
  pose proof p1_runs_correctly_1 as P.
  specialize (P 4 (p1_FlatImp_resVar $4) 20).
  edestruct P as [fuelL Q].
  - reflexivity.
  - intro. cbv in H. discriminate.
  - match goal with
    | Q: ?A = ?B |- _ => let B' := eval cbv in B in change (A = B') in Q
    end.
    exists fuelL.
    inversion Q.
    assumption.
Qed.

Goal (execState (run 100) (initialRiscvMachine (p1_riscv $4))).(registers) (p1_FlatImp_resVar $4)
= $14. reflexivity. Qed.

Goal go (p1_riscv $4) (p1_FlatImp_resVar $4) = $14.
  (* Note: go depends on lotsOfFuel_lowlevel, not lotsOfFuel *)
  reflexivity.
Qed.
