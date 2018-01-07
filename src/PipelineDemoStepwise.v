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
Require Import compiler.MyOmega.
Require Import compiler.zcast.

Definition myvar := nat.
Definition var_x1: myvar := 3.
Definition var_x2: myvar := 4.
Definition var_i: myvar := 5.
Definition wlit := 12. (* bit width of literals *)
Definition wjimm := 12. (* bit width of jump-immediates *)
Definition wdiff := 20. (* difference between literals width and full width *)
Notation w := (wlit + wdiff). (* bit width *)

Lemma my_bound: wlit + wdiff >= wjimm. cbv. omega. Qed.

(* Otherwise "Eval cbv" and "reflexivity" take forever *)
Opaque wlit wjimm wdiff.

Definition empty_types: member (@nil myvar) -> type. intro. inversion H. Defined.
Definition empty_vals: forall m : member (@nil myvar), @interp_type w (empty_types m).
  intro. inversion m. Defined.

Definition signed_lit_to_word(v: word wlit): word w := nat_cast word eq_refl (sext v wdiff).

Definition p1_LLG(n: word wlit): word w :=
  let n' := signed_lit_to_word n in
  let x1 := $0 in
  for i from 0 to n' updating (x1) {{
     let x2 := x1 ^+ i ^* i in
     x2
  }} ;;
  x1.

Goal [p1_LLG $1; p1_LLG $2; p1_LLG $3; p1_LLG $4] = [$0; $1; $5; $14]. reflexivity. Qed.

Definition x1_in_ix1: member [var_i; var_x1]. apply member_there. apply member_here. Defined.
Definition i_in_ix1: member [var_i; var_x1]. apply member_here. Defined.
Definition x1_in_x1: member [var_x1]. apply member_here. Defined.
Definition x2_in_x2ix1: member [var_x2; var_i; var_x1]. apply member_here. Defined.

Definition p1_LLG_ast(n: word wlit): @expr w myvar [] empty_types TInt :=
  let n' := signed_lit_to_word n in
  ELet var_x1 (ELit $0)
  (EFor var_i (ELit n') x1_in_x1
     (ELet var_x2 (EOp (EVar x1_in_ix1) OPlus (EOp (EVar i_in_ix1) OTimes (EVar i_in_ix1)))
     (EVar x2_in_x2ix1))
  (EVar x1_in_x1)).

Definition interp_expr'{t}(e: expr (@nil myvar) empty_types t): interp_type t :=
  interp_expr e empty_vals.

Goal forall (n: word wlit), p1_LLG n = interp_expr' (p1_LLG_ast n).
Proof. intros. reflexivity. Qed.

Definition nameGenState_initial: myvar := 10. (* should be bigger than all vars used in source *)

(* TODO this is a stmt where each literal is cast from wlit to w, so the its literal width is
   already w instead of wlit *)
Definition compileLLG2FlatImp{l G t}(e: expr l G t): @stmt w myvar * myvar :=
  fst (LLG2FlatImp.compile nameGenState_initial e).

Definition p1_FlatImp(n: word wlit): @stmt w myvar * myvar := compileLLG2FlatImp (p1_LLG_ast n).

Definition p1_FlatImp'(n: word wlit): @stmt wlit myvar * myvar.
  set (r := compileLLG2FlatImp (p1_LLG_ast n)).
  cbv -[natToWord signed_lit_to_word Nat.add] in r.
  (* copy-pasting and removing signed_lit_to_word changes implicit argument for literal bit width *)
  exact (SSeq (SLit 10 $ (0))
        (SSeq (SSet 3 10)
           (SSeq (SLit 20 $ (1))
              (SSeq (SLit 11 n)
                 (SSeq (SLit 5 $ (0))
                    (SSeq
                       (SLoop (SOp 12 OLt 5 11) 12
                          (SSeq
                             (SSeq
                                (SSeq (SSet 13 3)
                                   (SSeq (SSeq (SSet 14 5) (SSeq (SSet 15 5) (SOp 16 OTimes 14 15)))
                                      (SOp 17 OPlus 13 16))) (SSeq (SSet 4 17) (SSet 18 4)))
                             (SSeq (SSet 3 18) (SOp 5 OPlus 5 20)))) (SSet 19 3)))))), 19).
Defined.

Definition p1_FlatImp_stmt(n: word wlit): @stmt wlit myvar := 
  ltac:(let r := eval cbv [fst p1_FlatImp'] in (fst (p1_FlatImp' n)) in exact r).

Definition p1_FlatImp_resVar(n: word wlit): myvar := 
  ltac:(let r := eval cbv [snd p1_FlatImp'] in (snd (p1_FlatImp' n)) in exact r).

Definition lotsOfFuel := 100.

Definition mystate := myvar -> option (word w).

Definition empty_state: mystate := fun _ => None.

Definition eval_FlatImp_stmt(s: @stmt wlit myvar * myvar): option (word w) :=
  match eval_stmt (wlit:=wlit) (wdiff:=wdiff) (w_eq:=eq_refl) lotsOfFuel empty_state (fst s) with
  | Success final => final (snd s)
  | _ => None
  end.

Transparent wlt_dec.

Goal eval_FlatImp_stmt (p1_FlatImp' $4) = Some $14. reflexivity. Qed.

Definition compileFlat2Riscv(f: @stmt wlit myvar): list (@Instruction wlit wjimm myvar) :=
  compiler.FlatToRiscv.compile_stmt f.

Definition p1_riscv(n: word wlit): list (@Instruction wlit wjimm myvar) :=
  compileFlat2Riscv (p1_FlatImp_stmt n).

Goal False. set (r := p1_riscv $3). cbv in *. Abort.

Definition lotsOfFuel_lowlevel := 100.

Definition myInst := (@IsRiscvMachine wlit wdiff wjimm myvar _).
Existing Instance myInst.

Definition runThenGet(resVar: myvar):
  State (@RiscvMachine wlit wdiff wjimm myvar) (word (wlit+wdiff)) :=
  @run wlit wdiff wjimm my_bound _ _ _ _ lotsOfFuel_lowlevel;;
  getRegister (RegS resVar).

Definition go(p: list (@Instruction wlit wjimm myvar))(resVar: myvar): word w :=
  evalState (runThenGet resVar) (initialRiscvMachine p).

Import compiler.FlatToRiscv.

Lemma every_state_contains_empty_state: forall s,
  @containsState wlit wdiff wjimm _ _ _ s empty_state.
Proof.
  unfold containsState.
  intros. inversion H.
Qed.

Transparent wlit wjimm wdiff.

Lemma p1_runs_correctly_1: forall n resVar fuelH finalH,
  eval_stmt (wdiff:=wdiff) (wlit:=wlit) (w_eq:=eq_refl) fuelH empty_state (p1_FlatImp_stmt $ (n)) = Success finalH ->
  Common.get finalH resVar <> None ->
  exists fuelL,
  Some ((execState (run (w_lbound := my_bound) fuelL) (initialRiscvMachine (p1_riscv $n))).(registers) resVar)
  = Common.get finalH resVar.
Proof.
  introv E G.
  apply compile_stmt_correct with (fuelH0 := fuelH) (s := (p1_FlatImp_stmt $ (n))).
  - Omega.
  - Omega.
  - simpl. omega.
  - reflexivity.
  - exact E.
  - exact G.
Qed.

Goal exists fuel, 
  (execState (run (w_lbound := my_bound) fuel) (initialRiscvMachine (p1_riscv $4))).(registers)
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

Eval cbv in ((execState (run (w_lbound := my_bound) 60) (initialRiscvMachine (p1_riscv $4))).(registers) (p1_FlatImp_resVar $4)).

Goal (execState (run (w_lbound := my_bound) 100) (initialRiscvMachine (p1_riscv $4))).(registers) (p1_FlatImp_resVar $4)
= $14. reflexivity. Qed.

Goal go (p1_riscv $1) (p1_FlatImp_resVar $1) = $0. reflexivity. Qed.
Goal go (p1_riscv $2) (p1_FlatImp_resVar $2) = $1. reflexivity. Qed.
Goal go (p1_riscv $3) (p1_FlatImp_resVar $3) = $5. reflexivity. Qed.
Goal go (p1_riscv $4) (p1_FlatImp_resVar $4) = $14. reflexivity. Qed.
Goal go (p1_riscv $5) (p1_FlatImp_resVar $5) = $30. reflexivity. Qed.
Goal go (p1_riscv $6) (p1_FlatImp_resVar $6) = $55. reflexivity. Qed.
