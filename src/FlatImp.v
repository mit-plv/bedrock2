Require Import lib.LibTactics.
Require Import compiler.Common.
Require Import compiler.Tactics.
Require Import compiler.ResMonad.
Require Import compiler.Op.
Require Import compiler.StateCalculus.

Section FlatImp.

  Context {w: nat}. (* bit width *)
  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.

  Inductive stmt: Set :=
    | SLit(x: var)(v: word w): stmt
    | SOp(x: var)(op: binop)(y z: var): stmt
    | SSet(x y: var): stmt
    | SIf(cond: var)(bThen bElse: stmt): stmt
    | SLoop(body1: stmt)(cond: var)(body2: stmt): stmt
    | SSeq(s1 s2: stmt): stmt
    | SSkip: stmt.

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

  Lemma invert_eval_SLoop: forall fuel st1 body1 cond body2 st4,
    eval_stmt (S fuel) st1 (SLoop body1 cond body2) = Success st4 ->
    eval_stmt fuel st1 body1 = Success st4 /\ get st4 cond = Some $0 \/
    exists st2 st3 cv, eval_stmt fuel st1 body1 = Success st2 /\
                       get st2 cond = Some cv /\ cv <> $0 /\
                       eval_stmt fuel st2 body2 = Success st3 /\
                       eval_stmt fuel st3 (SLoop body1 cond body2) = Success st4.
  Proof.
    introv Ev. simpl in Ev. unfold option2res in *.
    repeat (destruct_one_match_hyp; try discriminate); inversionss; eauto 10.
  Qed.

  Lemma invert_eval_SSeq: forall fuel initial s1 s2 final,
    eval_stmt (S fuel) initial (SSeq s1 s2) = Success final ->
    exists mid, eval_stmt fuel initial s1 = Success mid /\
                eval_stmt fuel mid s2 = Success final.
  Proof.
    introv Ev. simpl in Ev. destruct_one_match_hyp; try discriminate. eauto.
  Qed.

  Definition vars_one(x: var): vars := singleton_set x.

  (* returns the set of modified vars *)
  Fixpoint modVars(s: stmt): vars :=
    match s with
    | SLit x v => vars_one x
    | SOp x op y z => vars_one x
    | SSet x y => vars_one x
    | SIf cond bThen bElse =>
        union (modVars bThen) (modVars bElse)
    | SLoop body1 cond body2 =>
        union (modVars body1) (modVars body2)
    | SSeq s1 s2 =>
        union (modVars s1) (modVars s2)
    | SSkip => empty_set
    end.

  Lemma modVarsSound: forall fuel s initial final,
    eval_stmt fuel initial s = Success final ->
    only_differ initial (modVars s) final.
  Proof.
    induction fuel; introv Ev.
    - discriminate.
    - destruct s.
      + simpl in *. inversionss. state_calc.
      + simpl in Ev. unfold option2res in *.
        repeat (destruct_one_match_hyp_of_type (option (word w)); try discriminate).
        inversionss. state_calc.
      + simpl in Ev. unfold option2res in *.
        repeat (destruct_one_match_hyp_of_type (option (word w)); try discriminate).
        inversionss. state_calc.
      + Opaque union. simpl in *. unfold option2res in *.
        repeat (destruct_one_match_hyp_of_type (option (word w)); try discriminate).
        destruct fuel; [ inversion Ev | ].
        specializes IHfuel; [ eassumption |].
        destruct_one_match_hyp; state_calc.
      + apply invert_eval_SLoop in Ev. destruct Ev as [Ev | Ev]. 
        * destruct Ev as [Ev C]. 
          simpl. specializes IHfuel; [eassumption|]. state_calc.
        * destruct Ev as [mid2 [mid3 [cv [Ev1 [C1 [C2 [Ev2 Ev3]]]]]]].
          simpl.
          pose proof (IHfuel _ _ _ Ev1) as IH1.
          pose proof (IHfuel _ _ _ Ev2) as IH2.
          pose proof (IHfuel _ _ _ Ev3) as IH3.
          clear - IH1 IH2 IH3. state_calc.
      + apply invert_eval_SSeq in Ev.
        destruct Ev as [mid [Ev1 Ev2]]. simpl.
        pose proof (IHfuel _ _ _ Ev1) as IH1.
        pose proof (IHfuel _ _ _ Ev2) as IH2.
        clear - IH1 IH2. state_calc.
      + simpl. inversionss. state_calc.
  Qed.

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
