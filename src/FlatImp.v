Require Import compiler.Common.
Require Import compiler.Tactics.
Require Import compiler.ResMonad.

Section FlatImp.

  Context {w: nat}. (* bit width *)
  Context {var: Set}.
  Context {state: Type}.
  Context {varEqDec: DecidableEq var}.
  Context {stateMap: Map state var (word w)}.

  Inductive stmt: Set :=
    | SLit(x: var)(v: word w): stmt
    | SOp(x: var)(op: binop)(y z: var): stmt
    | SSet(x y: var): stmt
    | SIf(cond: var)(bThen bElse: stmt): stmt
    | SLoop(body1: stmt)(cond: var)(body2: stmt): stmt
    | SSeq(s1 s2: stmt): stmt
    | SSkip: stmt.

  Definition eval_binop(op: binop)(v1 v2: word w): word w :=
    match op with
    | OPlus => v1 ^+ v2
    | OMinus => v1 ^- v2
    | OTimes => v1 ^* v2
    end.

  (* If we want a bigstep evaluation relation, we either need to put
     fuel into the SLoop constructor, or give it as argument to eval *)

  Fixpoint eval_stmt(f: nat)(st: state)(s: stmt): Res state :=
    match f with
    | 0 => OutOfFuel
    | S f' => match s with
      | SLit x v =>
          Success (put st x v)
      | SOp x op y z =>
          v1 <- option2res (get st y);
          v2 <- option2res (get st z);
          Success (put st x (eval_binop op v1 v2))
      | SSet x y =>
          v <- option2res (get st y);
          Success (put st x v)
      | SIf cond bThen bElse =>
          vcond <- option2res (get st cond);
          eval_stmt f' st (if dec (vcond = $0) then bElse else bThen)
      | SLoop body1 cond body2 =>
          st' <- eval_stmt f' st body1;
          vcond <- option2res (get st' cond);
          if dec (vcond = $0) then Success st' else
            st'' <- eval_stmt f' st' body2;
            eval_stmt f' st'' (SLoop body1 cond body2)
      | SSeq s1 s2 =>
          st' <- eval_stmt f' st s1;
          eval_stmt f' st' s2
      | SSkip => Success st
      end
    end.

End FlatImp.

Definition _n := 0.
Definition _a := 1.
Definition _b := 2.
Definition _s := 3.
Definition _one := 4.
(*
one = 1
n = input()
a = 0
b = 1
loop:
  stay in loop only if n nonzero
  s = a+b
  a = b
  b = s
  n = n - one
*)
Example fib(n: word 8) :=
  SSeq (SLit _one $1) (
  SSeq (SLit _n n) (
  SSeq (SLit _a $0) (
  SSeq (SLit _b $1) (
  SLoop SSkip
        _n
        (SSeq (SOp _s OPlus _a _b) (
         SSeq (SSet _a _b) (
         SSeq (SSet _b _s) (
              (SOp _n OMinus _n _one)))))
  )))).

Example finalFibState(n: nat): Res (nat -> option (word 8)) := (eval_stmt 100 empty (fib $n)).
Example finalFibVal(n: nat): option (word 8) := match finalFibState n with
| Success s => get s _b
| _ => None
end.

Goal finalFibVal 0 = Some $1. reflexivity. Qed.
Goal finalFibVal 1 = Some $1. reflexivity. Qed.
Goal finalFibVal 2 = Some $2. reflexivity. Qed.
Goal finalFibVal 3 = Some $3. reflexivity. Qed.
Goal finalFibVal 4 = Some $5. reflexivity. Qed.
Goal finalFibVal 5 = Some $8. reflexivity. Qed.
Goal finalFibVal 6 = Some $13. reflexivity. Qed.
