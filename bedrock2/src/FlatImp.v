Require Import lib.LibTacticsMin.
Require Import riscv.util.BitWidths.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import compiler.Op.
Require Import compiler.StateCalculus.
Require Import compiler.Memory.
Require Import compiler.NameWithEq.

Section FlatImp1.

  Context {Bw: BitWidths}.

  Context {Name: NameWithEq}.
  Notation var := (@name Name).
  Context {FName : NameWithEq}.
  Notation func := (@name FName).
  Existing Instance eq_name_dec.

  Context {stateMap: MapFunctions var (word wXLEN)}.
  Notation state := (map var (word wXLEN)).
  Context {varset: SetFunctions var}.
  Notation vars := (set var).

  Ltac state_calc := state_calc_generic (@name Name) (word wXLEN).

  Inductive stmt: Set :=
    | SLoad(x: var)(a: var): stmt
    | SStore(a: var)(v: var): stmt
    | SLit(x: var)(v: word wXLEN): stmt
    | SOp(x: var)(op: binop)(y z: var): stmt
    | SSet(x y: var): stmt
    | SIf(cond: var)(bThen bElse: stmt): stmt
    | SLoop(body1: stmt)(cond: var)(body2: stmt): stmt
    | SSeq(s1 s2: stmt): stmt
    | SSkip: stmt
    | SCall(binds: list var)(f: func)(args: list var).

  Section WithEnv.
    Context {funcMap: MapFunctions func (list var * list var * stmt)}.
    Notation env := (map func (list var * list var * stmt)).
    Context (e: env).

    (* If we want a bigstep evaluation relation, we either need to put
       fuel into the SLoop constructor, or give it as argument to eval *)
    Fixpoint eval_stmt(f: nat)(st: state)(m: mem)(s: stmt): option (state * mem) :=
      match f with
      | 0 => None (* out of fuel *)
      | S f => match s with
        | SLoad x a =>
            a <- get st a;
            v <- read_mem a m;
            Return (put st x v, m)
        | SStore a v =>
            a <- get st a;
            v <- get st v;
            m <- write_mem a v m;
            Return (st, m)
        | SLit x v =>
            Return (put st x v, m)
        | SOp x op y z =>
            y <- get st y;
            z <- get st z;
            Return (put st x (eval_binop op y z), m)
        | SSet x y =>
            v <- get st y;
            Return (put st x v, m)
        | SIf cond bThen bElse =>
            vcond <- get st cond;
            eval_stmt f st m (if dec (vcond = $0) then bElse else bThen)
        | SLoop body1 cond body2 =>
            p <- eval_stmt f st m body1;
            let '(st, m) := p in
            vcond <- get st cond;
            if dec (vcond = $0) then Return (st, m) else
              q <- eval_stmt f st m body2;
              let '(st, m) := q in
              eval_stmt f st m (SLoop body1 cond body2)
        | SSeq s1 s2 =>
            p <- eval_stmt f st m s1;
            let '(st, m) := p in
            eval_stmt f st m s2
        | SSkip => Return (st, m)
        | SCall binds fname args =>
          fimpl <- get e fname;
          let '(params, rets, fbody) := fimpl in
          argvs <- option_all (List.map (get st) args);
          st0 <- putmany params argvs empty_map;
          st1m' <- eval_stmt f st0 m fbody;
          let '(st1, m') := st1m' in
          retvs <- option_all (List.map (get st1) rets);
          st' <- putmany binds retvs st;
          Return (st', m')
        end
      end.

    Local Ltac inversion_lemma :=
      intros;
      simpl in *;
      repeat (destruct_one_match_hyp; try discriminate);
      inversionss;
      eauto 16.

    Lemma invert_eval_SLoad: forall fuel initialSt initialM x y final,
      eval_stmt (S fuel) initialSt initialM (SLoad x y) = Some final ->
      exists a v, get initialSt y = Some a /\
                  read_mem a initialM = Some v /\
                  final = (put initialSt x v, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SStore: forall fuel initialSt initialM x y final,
      eval_stmt (S fuel) initialSt initialM (SStore x y) = Some final ->
      exists a v finalM, get initialSt x = Some a /\
                         get initialSt y = Some v /\
                         write_mem a v initialM = Some finalM /\
                         final = (initialSt, finalM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SLit: forall fuel initialSt initialM x v final,
      eval_stmt (S fuel) initialSt initialM (SLit x v) = Some final ->
      final = (put initialSt x v, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SOp: forall fuel x y z op initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM (SOp x op y z) = Some final ->
      exists v1 v2,
        get initialSt y = Some v1 /\
        get initialSt z = Some v2 /\
        final = (put initialSt x (eval_binop op v1 v2), initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SSet: forall fuel x y initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM (SSet x y) = Some final ->
      exists v,
        get initialSt y = Some v /\ final = (put initialSt x v, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SIf: forall fuel cond bThen bElse initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM (SIf cond bThen bElse) = Some final ->
      exists vcond,
        get initialSt cond = Some vcond /\
        (vcond <> $0 /\ eval_stmt fuel initialSt initialM bThen = Some final \/
         vcond =  $0 /\ eval_stmt fuel initialSt initialM bElse = Some final).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SLoop: forall fuel st1 m1 body1 cond body2 p4,
      eval_stmt (S fuel) st1 m1 (SLoop body1 cond body2) = Some p4 ->
      eval_stmt fuel st1 m1 body1 = Some p4 /\ get (fst p4) cond = Some $0 \/
      exists st2 m2 st3 m3 cv, eval_stmt fuel st1 m1 body1 = Some (st2, m2) /\
                               get st2 cond = Some cv /\ cv <> $0 /\
                               eval_stmt fuel st2 m2 body2 = Some (st3, m3) /\
                               eval_stmt fuel st3 m3 (SLoop body1 cond body2) = Some p4.
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SSeq: forall fuel initialSt initialM s1 s2 final,
      eval_stmt (S fuel) initialSt initialM (SSeq s1 s2) = Some final ->
      exists midSt midM, eval_stmt fuel initialSt initialM s1 = Some (midSt, midM) /\
                         eval_stmt fuel midSt midM s2 = Some final.
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SSkip: forall fuel initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM SSkip = Some final ->
      final = (initialSt, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SCall : forall st m1 p2 f binds fname args,
      eval_stmt (S f) st m1 (SCall binds fname args) = Some p2 ->
      exists params rets fbody argvs st0 st1 m' retvs st',
        get e fname = Some (params, rets, fbody) /\
        option_all (List.map (get st) args) = Some argvs /\
        putmany params argvs empty_map = Some st0 /\
        eval_stmt f st0 m1 fbody = Some (st1, m') /\
        option_all (List.map (get st1) rets) = Some retvs /\
        putmany binds retvs st = Some st' /\
        p2 = (st', m').
    Proof. inversion_lemma. Qed.
  End WithEnv.

  Fixpoint stmt_size(s: stmt): nat :=
    match s with
    | SLoad x a => 1
    | SStore a v => 1
    | SLit x v => 8
    | SOp x op y z => 2
    | SSet x y => 1
    | SIf cond bThen bElse => 1 + (stmt_size bThen) + (stmt_size bElse)
    | SLoop body1 cond body2 => 1 + (stmt_size body1) + (stmt_size body2)
    | SSeq s1 s2 => 1 + (stmt_size s1) + (stmt_size s2)
    | SSkip => 1
    | SCall binds f args => S (length binds + length args)
    end.

  (* returns the set of modified vars *)
  Fixpoint modVars(s: stmt): vars :=
    match s with
    | SLoad x y => singleton_set x
    | SStore x y => empty_set
    | SLit x v => singleton_set x
    | SOp x op y z => singleton_set x
    | SSet x y => singleton_set x
    | SIf cond bThen bElse =>
        union (modVars bThen) (modVars bElse)
    | SLoop body1 cond body2 =>
        union (modVars body1) (modVars body2)
    | SSeq s1 s2 =>
        union (modVars s1) (modVars s2)
    | SSkip => empty_set
    | SCall binds func args => of_list binds
    end.

  Fixpoint accessedVars(s: stmt): vars :=
    match s with
    | SLoad x y => union (singleton_set x) (singleton_set y)
    | SStore x y => union (singleton_set x) (singleton_set y)
    | SLit x v => singleton_set x
    | SOp x op y z => union (singleton_set x) (union (singleton_set y) (singleton_set z))
    | SSet x y => union (singleton_set x) (singleton_set y)
    | SIf cond bThen bElse =>
        union (singleton_set cond) (union (accessedVars bThen) (accessedVars bElse))
    | SLoop body1 cond body2 =>
        union (singleton_set cond) (union (accessedVars body1) (accessedVars body2))
    | SSeq s1 s2 =>
        union (accessedVars s1) (accessedVars s2)
    | SSkip => empty_set
    | SCall binds func args => union (of_list binds) (of_list args)
    end.

  Lemma modVars_subset_accessedVars: forall s,
    subset (modVars s) (accessedVars s).
  Proof.
    intro s. induction s; simpl; unfold singleton_set; state_calc.
  Qed.
End FlatImp1.


Ltac invert_eval_stmt :=
  lazymatch goal with
  | E: eval_stmt _ (S ?fuel) _ _ ?s = Some _ |- _ =>
    destruct s;
    [ apply invert_eval_SLoad in E
    | apply invert_eval_SStore in E
    | apply invert_eval_SLit in E
    | apply invert_eval_SOp in E
    | apply invert_eval_SSet in E
    | apply invert_eval_SIf in E
    | apply invert_eval_SLoop in E
    | apply invert_eval_SSeq in E
    | apply invert_eval_SSkip in E
    | apply invert_eval_SCall in E ];
    deep_destruct E;
    [ let x := fresh "Case_SLoad" in pose proof tt as x; move x at top
    | let x := fresh "Case_SStore" in pose proof tt as x; move x at top
    | let x := fresh "Case_SLit" in pose proof tt as x; move x at top
    | let x := fresh "Case_SOp" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSet" in pose proof tt as x; move x at top
    | let x := fresh "Case_SIf_Then" in pose proof tt as x; move x at top
    | let x := fresh "Case_SIf_Else" in pose proof tt as x; move x at top
    | let x := fresh "Case_SLoop_Done" in pose proof tt as x; move x at top
    | let x := fresh "Case_SLoop_NotDone" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSeq" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSkip" in pose proof tt as x; move x at top
    | let x := fresh "Case_SCall" in pose proof tt as x; move x at top ]
  end.


Section FlatImp2.

  Context {Bw: BitWidths}.

  Context {Name: NameWithEq}.
  Notation var := (@name Name).
  Existing Instance eq_name_dec.
  Context {FName : NameWithEq}.
  Notation func := (@name FName).

  Context {stateMap: MapFunctions var (word wXLEN)}.
  Notation state := (map var (word wXLEN)).
  Context {varset: SetFunctions var}.
  Notation vars := (set var).

  Context {funcMap: MapFunctions func (list var * list var * @stmt Bw Name FName)}.
  Notation env := (map func (list var * list var * stmt)).

  Ltac state_calc := state_calc_generic (@name Name) (word wXLEN).

  Lemma increase_fuel_still_Success: forall fuel1 fuel2 (e: env) initialSt initialM s final,
    fuel1 <= fuel2 ->
    eval_stmt e fuel1 initialSt initialM s = Some final ->
    eval_stmt e fuel2 initialSt initialM s = Some final.
  Proof.
    induction fuel1; introv L Ev.
    - inversions Ev.
    - destruct fuel2; [omega|].
      assert (fuel1 <= fuel2) as F by omega. specialize IHfuel1 with (1 := F).
      destruct final as [finalSt finalM].
      invert_eval_stmt; cbn in *;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          ensure_new IH'
      end;
      repeat match goal with
      | H: _ = Some _ |- _ => rewrite H
      end;
      try congruence;
      try simpl_if;
      eauto.
  Qed.

  Lemma modVarsSound: forall fuel e s initialSt initialM finalSt finalM,
    eval_stmt e fuel initialSt initialM s = Some (finalSt, finalM) ->
    only_differ initialSt (modVars s) finalSt.
  Proof.
    induction fuel; introv Ev.
    - discriminate.
    - invert_eval_stmt; simpl in *; inversionss;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          simpl in IH';
          ensure_new IH'
      end;
      state_calc.
      refine (only_differ_putmany _ _ _ _ _ _); eassumption.
  Qed.
End FlatImp2.

Require riscv.util.BitWidth32.

Module TestFlatImp.

Import riscv.util.BitWidth32.
  
Instance ZName: NameWithEq := {| name := Z |}.

Definition var: Set := (@name ZName). (* only inside this test module *)

Definition _n := 0%Z.
Definition _a := 1%Z.
Definition _b := 2%Z.
Definition _s := 3%Z.
Definition _one := 4%Z.
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


Example fib(n: word 32) :=
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
Set Printing Implicit.

Definition annoying_eq: DecidableEq
  (list (@name ZName) * list (@name ZName) * @stmt BitWidth32 ZName ZName). Admitted.
Existing Instance annoying_eq.

Definition eval_stmt_test fuel initialSt := @eval_stmt BitWidth32 ZName ZName _ (List_Map _ _ (List_Set _)_) empty_map fuel initialSt no_mem.

Example finalFibState(n: nat) := (eval_stmt_test 100 empty_map (fib $n)).
Example finalFibVal(n: nat): option (word 32) := match finalFibState n with
| Some (s, _) => get s _b
| _ => None
end.

Goal finalFibVal 0 = Some $1. reflexivity. Qed.
Goal finalFibVal 1 = Some $1. reflexivity. Qed.
Goal finalFibVal 2 = Some $2. reflexivity. Qed.
Goal finalFibVal 3 = Some $3. reflexivity. Qed.
Goal finalFibVal 4 = Some $5. reflexivity. Qed.
Goal finalFibVal 5 = Some $8. reflexivity. Qed.
Goal finalFibVal 6 = Some $13. reflexivity. Qed.

End TestFlatImp.
