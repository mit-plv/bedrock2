Require Import Coq.Lists.List.
Import ListNotations.
Require Import bbv.Word.
Require Import compiler.Decidable.
Require Import compiler.Op.
Require Import compiler.member.
Require Import compiler.ForWord.
Require Import compiler.LLG.
Require compiler.LLG2FlatImp.
Require Import compiler.FlatImp.
Require Import compiler.ResMonad.

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

