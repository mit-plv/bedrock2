(* Since FuncMut is not what we want, we don't need this currently

Require Import Coq.Lists.List.
Import ListNotations.
Require Import compiler.Decidable.
Require compiler.LLG.
Require compiler.FuncMut.
Require Import compiler.member.

Section LLG2FuncMut.

  Context {var: Set}.
  Context {eq_var_dec: DecidableEq var}.

  (* only correct if source expression never updates the same array twice and doesn't keep
     references to outdated arrays *)
  Fixpoint compile{l G t}(e: LLG.expr l G t){struct e}: (@FuncMut.expr var) :=
    match e with
    | LLG.ELit n => FuncMut.ELit n
    | LLG.EVar x => FuncMut.EVar (member_get x)
    | LLG.EOp e1 op e2 => FuncMut.EOp (compile e1) op (compile e2)
    | LLG.ELet x e1 e2 => FuncMut.ELet x (compile e1) (compile e2)
    | LLG.ENewArray t es => FuncMut.ENewArray (compile es)
    | LLG.EGet ea ei => FuncMut.EGet (compile ea) (compile ei)
    | LLG.EUpdate ea ei ev => FuncMut.EUpdate (compile ea) (compile ei) (compile ev)
    | LLG.EFor i eto upd ebody erest => FuncMut.EVar i (* <--- TODO *)
    end.

End LLG2FuncMut.

Definition test2b(i v: nat): FuncMut.expr := compile (compiler.LLG.LLG_Tests.test2a i v).

Definition test2b'(i v: nat): FuncMut.expr :=
  ltac:(let r := eval cbv -[
    compiler.LLG.LLG_Tests.var_x1 compiler.LLG.LLG_Tests.var_x2
  ] in (test2b i v) in exact r).

Definition empty_ctx{var: Type}: var -> option FuncMut.val := fun _ => None.

Definition empty_Store: FuncMut.Store := nil.

Eval cbv in (compiler.FuncMut.interp_expr empty_ctx (test2b' 1 11) empty_Store).
*)
