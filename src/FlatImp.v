Require Import bbv.Word.
Require Import compiler.Decidable.
Require Import compiler.StateMonad.

Inductive Res(A: Type): Type :=
| Success(a: A): Res A
| Fail: Res A
| OutOfFuel: Res A.

Arguments Success {A}.
Arguments Fail {A}.
Arguments OutOfFuel {A}.

Ltac destruct_one_match :=
  match goal with
  | [ |- context[match ?e with _ => _ end] ] =>
      is_var e; destruct e
  | [ |- context[match ?e with _ => _ end] ] =>
      let E := fresh "E" in destruct e eqn: E
  end.

Instance Res_Monad: Monad Res := {| 
  Bind := fun {A B: Type} (r: Res A) (f: A -> Res B) => match r with
          | Success a => f a
          | Fail => Fail
          | OutOfFuel => OutOfFuel
          end;
  Return := fun {A: Type} (a: A) => Success a
|}.
- intros; reflexivity.
- intros; destruct_one_match; reflexivity.
- intros; repeat destruct_one_match; reflexivity.
Defined.

Definition option2res{A: Type}(o: option A): Res A :=
  match o with
  | Some a => Success a
  | None => Fail
  end.

Class Map(T K V: Type) := mMap {
  empty: T;
  get: T -> K -> option V;
  put: T -> K -> V -> T;
  (* TODO probably needs some properties *)
}.

Instance Function_Map(K V: Type){decK: DecidableEq K}: Map (K -> option V) K V := {|
  empty := fun _ => None;
  get := id;
  put := fun (m: K -> option V) (k: K) (v: V) =>
           fun (k': K) => if dec (k = k') then Some v else m k'
|}.

Global Instance dec_eq_word : forall sz, DecidableEq (word sz) := weq.

Inductive binop: Set := OPlus | OMinus | OTimes.

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
Definition _one := 1.
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
Goal finalFibVal 3 = Some $3.
  unfold finalFibVal, finalFibState, fib.
  remember 95 as Num.
  unfold eval_stmt.
  match goal with
  | [ |- match ?e with _ => _ end = _ ] => remember e as M
  end.

  Ltac step := match goal with
  | [ H: context G[y <- Success ?a; (@?f y)] |- _ ] =>
     let old := context G[y <- Success a; (f y)] in
     let new := context G[f a] in
     let new' := eval cbv beta in new in
     change new' in H
  end.
  step. step. step. step.
  remember 94 as Num2. subst Num. rename Num2 into Num. step.
  simpl option2res in *.
  step.
  Ltac dodec := match goal with
  | [ H: ?M = (if ?E then ?T else ?B) |- _ ] => let E' := eval cbv in E in
      change (M = if E' then T else B) in H
  end;   cbv beta iota in *.
  dodec. (* 3 = 0 *)
  remember 90 as Num2. subst Num. rename Num2 into Num.
  simpl option2res in *.
  Ltac step2 := simpl option2res in *; step; simpl option2res in *.
  step2. step2. step2. step2. step2. step2. step2. step2.
  do 10 step2.
  dodec. (* 3 - 1 = 0 *)
  do 10 step2.
  dodec. (* 3 - 1 - (0 + 1) = 0 *)
  do 1 step2.
  remember 85 as Num2. subst Num. rename Num2 into Num.
  do 10 step2.
   match goal with
  | [ H: ?M = (if ?E then ?T else ?B) |- _ ] => let E' := eval cbv in E in
      change (M = if E' then T else B) in H
  end.
  dodec. (* 3 - 1 - (0 + 1) - (1 + 0 + 1) *)
  step2. step2.
  simpl (@Success (word 8) _) in *.
  step. step. step. simpl option2res in *. step. step.
  remember 85 as Num2. subst Num. rename Num2 into Num. step.
  remember 80 as Num2. subst Num. rename Num2 into Num. step.
 
  step. step.
  Ltac step := match goal with
  | [ H: context G[y <- Success ?a; (@?f y)] |- _ ] =>
     let old := constr:(G (y <- Success a; (f y))) in
     let new := constr:(G (f a)) in
     let new' := eval cbv beta in new in
     change new' in H
  end.
  step.

