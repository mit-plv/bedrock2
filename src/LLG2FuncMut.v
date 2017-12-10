Require Import Coq.Lists.List.
Import ListNotations.
Require Import compiler.Decidable.
Require compiler.LLG_untyped_vars.
From compiler Require Import LLG_untyped_vars.
Require compiler.FuncMut.


Section LLG2FuncMut.

  Context {var: Set}.
  Context {eq_var_dec: DecidableEq var}.

  (* only correct if source expression never updates the same array twice *)
  Fixpoint compile{l: list var}{n: nat}(e: LLG_untyped_vars.expr l n){struct e}: FuncMut.expr :=
    match e with
    | LLG_untyped_vars.ELit n => FuncMut.ELit n
    | LLG_untyped_vars.EVar n x => FuncMut.EVar x
    | LLG_untyped_vars.EOp e1 op e2 => FuncMut.EOp (compile e1) op (compile e2)
    | LLG_untyped_vars.ELet x e1 e2 => FuncMut.ELet x (compile e1) (compile e2)
    | LLG_untyped_vars.ENewArray dim es => FuncMut.ENewArray (compile es)
    | LLG_untyped_vars.EGet ea ei => FuncMut.EGet (compile ea) (compile ei)
    | LLG_untyped_vars.EUpdate ea ei ev => FuncMut.EUpdate (compile ea) (compile ei) (compile ev)
    end.

End LLG2FuncMut.

Definition test2b(i v: nat): FuncMut.expr := compile (compiler.LLG_untyped_vars.test2a i v).

Definition test2b'(i v: nat): FuncMut.expr :=
  ltac:(let r := eval cbv -[compiler.LLG_untyped_vars.var_x1 compiler.LLG_untyped_vars.var_x2] in (test2b i v) in exact r).

Definition empty_ctx{var: Type}: var -> option FuncMut.val := fun _ => None.

Definition empty_Store: FuncMut.Store := nil.

Eval cbv in (compiler.FuncMut.interp_expr empty_ctx (test2b' 1 11) empty_Store).

