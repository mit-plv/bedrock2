Require Import Coq.Lists.List.
Import ListNotations.
Require Import lib.LibTacticsMin.
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
Require Import compiler.runsToSatisfying.

Definition myvar := nat.
Definition var_x1: myvar := 3.
Definition var_x2: myvar := 4.
Definition var_i: myvar := 5.
Definition w := 12. (* bit width *)
Definition wlit := 12. (* bit width of literals *)
Definition wdiff := 0. (* difference between literals width and full width *)

(*
Too big for evaluation inside Coq:
Definition w := 32. (* bit width *)
Definition wlit := 12. (* bit width of literals *)
Definition wdiff := 20. (* difference between literals width and full width *)
*)

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

Definition p1_FlatImp(n: word wlit): @stmt w myvar * myvar := compileLLG2FlatImp (p1_LLG_ast n).

Definition p1_FlatImp'(n: word wlit): @stmt w myvar * myvar :=
  ltac:(let r := eval cbv -[natToWord] in (p1_FlatImp n) in exact r).

Definition p1_FlatImp_stmt(n: word wlit): @stmt w myvar := 
  ltac:(let r := eval cbv -[natToWord] in (fst (p1_FlatImp n)) in exact r).

Definition p1_FlatImp_resVar(n: word wlit): myvar := 
  ltac:(let r := eval cbv -[natToWord] in (snd (p1_FlatImp n)) in exact r).

Definition lotsOfFuel := 100.

Definition mystate := myvar -> option (word w).

Definition empty_state: mystate := fun _ => None.

Definition eval_FlatImp_stmt(s: @stmt wlit myvar * myvar): option (word w) :=
  match eval_stmt (wlit:=wlit) (wdiff:=wdiff) (w_eq:=eq_refl) lotsOfFuel empty_state (fst s) with
  | Success final => final (snd s)
  | _ => None
  end.

Transparent wlt_dec.

Goal eval_FlatImp_stmt (p1_FlatImp $4) = Some $14. reflexivity. Qed.

Definition compileFlat2Riscv(f: @stmt w myvar): list (@Instruction wlit myvar) :=
  compiler.FlatToRiscv.compile_stmt f.

Definition p1_riscv(n: word w): list (@Instruction wlit myvar) :=
  compileFlat2Riscv (p1_FlatImp_stmt n).

Goal False. set (r := p1_riscv $3). cbv in *. Abort.

Definition lotsOfFuel_lowlevel := 100.

Definition myInst := (@IsRiscvMachine wlit wdiff nat _).
Existing Instance myInst.

Axiom bound_doesnt_hold: wlit + wdiff >= 20.

Definition runThenGet(resVar: myvar): State RiscvMachine (word (wlit+wdiff)) :=
  run (w_lbound := bound_doesnt_hold) lotsOfFuel_lowlevel;;
  getRegister (RegS resVar).

Definition go(p: list (@Instruction wlit myvar))(resVar: myvar): word w :=
  evalState (runThenGet resVar) (initialRiscvMachine p).

Import compiler.FlatToRiscv.

Lemma every_state_contains_empty_state: forall s,
  @containsState wlit wdiff _ _ _ s empty_state.
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
  eval_stmt (wdiff:=wdiff) (wlit:=wlit) (w_eq:=eq_refl) fuelH empty_state (p1_FlatImp_stmt $ (n)) = Success finalH ->
  Common.get finalH resVar <> None ->
  exists fuelL,
  Some ((execState (run (w_lbound := bound_doesnt_hold) fuelL) (initialRiscvMachine (p1_riscv $n))).(registers) resVar)
  = Common.get finalH resVar.
Proof.
  introv E G.
  apply (@compile_stmt_correct wlit wdiff eq_refl bound_doesnt_hold _ _ _ _ _
    fuelH _ (p1_FlatImp_stmt $ (n))).
  - simpl. omega.
  - reflexivity.
  - exact E.
  - exact G.
Qed.

Goal exists fuel, 
  (execState (run (w_lbound := bound_doesnt_hold) fuel) (initialRiscvMachine (p1_riscv $4))).(registers)
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

(* TODO *)
(* runs out of memory
Eval cbv in ((execState (run (w_lbound := bound_doesnt_hold) 32) (initialRiscvMachine (p1_riscv $4))).(registers) (p1_FlatImp_resVar $4)).
*)

(* doesn't work:
Goal (execState (run (w_lbound := bound_doesnt_hold) 100) (initialRiscvMachine (p1_riscv $4))).(registers) (p1_FlatImp_resVar $4)
= $14. reflexivity. Qed.

Goal go (p1_riscv $4) (p1_FlatImp_resVar $4) = $14.
  (* Note: go depends on lotsOfFuel_lowlevel, not lotsOfFuel *)
  reflexivity.
Qed.
*)
