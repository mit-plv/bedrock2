Require Import Coq.Lists.List.
Import ListNotations.
Require Import compiler.Decidable.
Require compiler.LLG.
Require compiler.FuncMut.


Section LLG2FuncMut.

  Context {var: Set}.
  Context {eq_var_dec: DecidableEq var}.

  (* only correct if source expression never updates the same array twice *)
  Fixpoint compile{l: list var}{n: nat}(e: LLG.expr l n){struct e}: FuncMut.expr :=
    match e with
    | LLG.ELit n => FuncMut.ELit n
    | LLG.EVar n x => FuncMut.EVar x
    | LLG.EOp e1 op e2 => FuncMut.EOp (compile e1) op (compile e2)
    | LLG.ELet x e1 e2 => FuncMut.ELet x (compile e1) (compile e2)
    | LLG.ENewArray dim es => FuncMut.ENewArray (compile es)
    | LLG.EGet ea ei => FuncMut.EGet (compile ea) (compile ei)
    | LLG.EUpdate ea ei ev => FuncMut.EUpdate (compile ea) (compile ei) (compile ev)
    end.

End LLG2FuncMut.

Definition test2b(i v: nat): FuncMut.expr := compile (compiler.LLG.test2a i v).

Definition test2b'(i v: nat): FuncMut.expr :=
  ltac:(let r := eval cbv -[compiler.LLG.var_x1 compiler.LLG.var_x2] in (test2b i v) in exact r).

Definition empty_ctx{var: Type}: var -> option FuncMut.val := fun _ => None.

Definition empty_Store: FuncMut.Store := nil.

Eval cbv in (compiler.FuncMut.interp_expr empty_ctx (test2b' 1 11) empty_Store).

