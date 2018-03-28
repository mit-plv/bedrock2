Require Import Coq.Lists.List.
Import ListNotations.
Require Import lib.LibTacticsMin.
Require Import compiler.Common.
Require Import compiler.Tactics.
Require Import compiler.Op.
Require Import compiler.StateCalculus.
Require Import bbv.DepEqNat.
Require Import compiler.NameWithEq.
Require Import Coq.Program.Tactics.
Require Import compiler.Memory.

Section ExprImp1.

  Context {w: nat}. (* bit width *)

  Context {Name: NameWithEq}.
  Notation var := (@name Name).
  Existing Instance eq_name_dec.


  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.
  Context {vars: Type}.
  Context {varset: set vars var}.

  Ltac state_calc := state_calc_generic (@name Name) (word w).
  Ltac set_solver := set_solver_generic (@name Name).

  Inductive expr: Set :=
    | ELit(v: word w): expr
    | EVar(x: var): expr
    | EOp(op: binop)(e1 e2: expr): expr.

  Inductive stmt: Set :=
    | SLoad(x: var)(addr: expr): stmt
    | SStore(addr val: expr): stmt
    | SSet(x: var)(e: expr): stmt
    | SIf(cond: expr)(bThen bElse: stmt): stmt
    | SWhile(cond: expr)(body: stmt): stmt
    | SSeq(s1 s2: stmt): stmt
    | SSkip: stmt.

  Fixpoint eval_expr(st: state)(e: expr): option (word w) :=
    match e with
    | ELit v => Return v
    | EVar x => get st x
    | EOp op e1 e2 =>
        v1 <- eval_expr st e1;
        v2 <- eval_expr st e2;
        Return (eval_binop op v1 v2)
    end.

  Fixpoint eval_stmt(f: nat)(st: state)(m: mem w)(s: stmt): option (state * mem w) :=
    match f with
    | 0 => None (* out of fuel *)
    | S f => match s with
      | SLoad x a =>
          a <- eval_expr st a;
          v <- read_mem a m;
          Return (put st x v, m)
      | SStore a v =>
          a <- eval_expr st a;
          v <- eval_expr st v;
          m <- write_mem a v m;
          Return (st, m)
      | SSet x e =>
          v <- eval_expr st e;
          Return (put st x v, m)
      | SIf cond bThen bElse =>
          v <- eval_expr st cond;
          eval_stmt f st m (if weq v $0 then bElse else bThen)
      | SWhile cond body =>
          v <- eval_expr st cond;
          if weq v $0 then Return (st, m) else
            p <- eval_stmt f st m body;
            let '(st, m) := p in
            eval_stmt f st m (SWhile cond body)
      | SSeq s1 s2 =>
          p <- eval_stmt f st m s1;
          let '(st, m) := p in
          eval_stmt f st m s2
      | SSkip => Return (st, m)
      end
    end.

  Fixpoint expr_size(e: expr): nat :=
    match e with
    | ELit _ => 1
    | EVar _ => 1
    | EOp op e1 e2 => S (expr_size e1 + expr_size e2)
    end.

  Fixpoint stmt_size(s: stmt): nat :=
    match s with
    | SLoad x a => S (expr_size a)
    | SStore a v => S (expr_size a + expr_size v)
    | SSet x e => S (expr_size e)
    | SIf cond bThen bElse => S (expr_size cond + stmt_size bThen + stmt_size bElse)
    | SWhile cond body => S (expr_size cond + stmt_size body)
    | SSeq s1 s2 => S (stmt_size s1 + stmt_size s2)
    | SSkip => 1
    end.

  Local Ltac inversion_lemma :=
    intros;
    simpl in *;
    repeat (destruct_one_match_hyp; try discriminate);
    inversionss;
    eauto 15.

  Lemma invert_eval_SLoad: forall fuel initialSt initialM x e final,
    eval_stmt (S fuel) initialSt initialM (SLoad x e) = Some final ->
    exists a v, eval_expr initialSt e = Some a /\
                read_mem a initialM = Some v /\
                final = (put initialSt x v, initialM).
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SStore: forall fuel initialSt initialM a v final,
    eval_stmt (S fuel) initialSt initialM (SStore a v) = Some final ->
    exists av vv finalM, eval_expr initialSt a = Some av /\
                         eval_expr initialSt v = Some vv /\
                         write_mem av vv initialM = Some finalM /\
                         final = (initialSt, finalM).
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SSet: forall f st1 m1 p2 x e,
    eval_stmt (S f) st1 m1 (SSet x e) = Some p2 ->
    exists v, eval_expr st1 e = Some v /\ p2 = (put st1 x v, m1).
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SIf: forall f st1 m1 p2 cond bThen bElse,
    eval_stmt (S f) st1 m1 (SIf cond bThen bElse) = Some p2 ->
    exists cv,
      eval_expr st1 cond = Some cv /\ 
      (cv <> $0 /\ eval_stmt f st1 m1 bThen = Some p2 \/
       cv = $0  /\ eval_stmt f st1 m1 bElse = Some p2).
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SWhile: forall st1 m1 p3 f cond body,
    eval_stmt (S f) st1 m1 (SWhile cond body) = Some p3 ->
    exists cv,
      eval_expr st1 cond = Some cv /\
      (cv <> $0 /\ (exists st2 m2, eval_stmt f st1 m1 body = Some (st2, m2) /\ 
                                   eval_stmt f st2 m2 (SWhile cond body) = Some p3) \/
       cv = $0  /\ p3 = (st1, m1)).
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SSeq: forall st1 m1 p3 f s1 s2,
    eval_stmt (S f) st1 m1 (SSeq s1 s2) = Some p3 ->
    exists st2 m2, eval_stmt f st1 m1 s1 = Some (st2, m2) /\ eval_stmt f st2 m2 s2 = Some p3.
  Proof. inversion_lemma. Qed.

  Lemma invert_eval_SSkip: forall st1 m1 p2 f,
    eval_stmt (S f) st1 m1 SSkip = Some p2 ->
    p2 = (st1, m1).
  Proof. inversion_lemma. Qed.

  (* Returns a list to make it obvious that it's a finite set. *)
  Fixpoint allVars_expr(e: expr): list var :=
    match e with
    | ELit v => []
    | EVar x => [x]
    | EOp op e1 e2 => (allVars_expr e1) ++ (allVars_expr e2)
    end.

  Fixpoint allVars_stmt(s: stmt): list var := 
    match s with
    | SLoad v e => v :: allVars_expr e
    | SStore a e => (allVars_expr a) ++ (allVars_expr e)
    | SSet v e => v :: allVars_expr e
    | SIf c s1 s2 => (allVars_expr c) ++ (allVars_stmt s1) ++ (allVars_stmt s2)
    | SWhile c body => (allVars_expr c) ++ (allVars_stmt body)
    | SSeq s1 s2 => (allVars_stmt s1) ++ (allVars_stmt s2)
    | SSkip => []
    end.

  (* Returns a static approximation of the set of modified vars.
     The returned set might be too big, but is guaranteed to include all modified vars. *)
  Fixpoint modVars(s: stmt): vars := 
    match s with
    | SLoad v _ => singleton_set v
    | SStore _ _ => empty_set
    | SSet v _ => singleton_set v
    | SIf _ s1 s2 => union (modVars s1) (modVars s2)
    | SWhile _ body => modVars body
    | SSeq s1 s2 => union (modVars s1) (modVars s2)
    | SSkip => empty_set
    end.

  Lemma modVars_subset_allVars: forall x s,
    x \in modVars s ->
    In x (allVars_stmt s).
  Proof.
    intros.
    induction s; simpl in *.
    - set_solver.
    - set_solver.
    - apply singleton_set_spec in H. auto.
    - apply union_spec in H.
      apply in_or_app. right. apply in_or_app.
      destruct H as [H|H]; auto.
    - apply in_or_app. right. auto.
    - apply union_spec in H.
      apply in_or_app.
      destruct H as [H|H]; auto.
    - eapply empty_set_spec. eassumption.
  Qed.

End ExprImp1.


Ltac invert_eval_stmt :=
  lazymatch goal with
  | E: eval_stmt (S ?fuel) _ _ ?s = Some _ |- _ =>
    destruct s;
    [ apply invert_eval_SLoad in E
    | apply invert_eval_SStore in E
    | apply invert_eval_SSet in E
    | apply invert_eval_SIf in E
    | apply invert_eval_SWhile in E
    | apply invert_eval_SSeq in E
    | apply invert_eval_SSkip in E ];
    deep_destruct E;
    [ let x := fresh "Case_SLoad" in pose proof tt as x; move x at top
    | let x := fresh "Case_SStore" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSet" in pose proof tt as x; move x at top
    | let x := fresh "Case_SIf_Then" in pose proof tt as x; move x at top
    | let x := fresh "Case_SIf_Else" in pose proof tt as x; move x at top
    | let x := fresh "Case_SWhile_Done" in pose proof tt as x; move x at top
    | let x := fresh "Case_SWhile_NotDone" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSeq" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSkip" in pose proof tt as x; move x at top ]
  end.


Section ExprImp2.

  Context {w: nat}. (* bit width *)

  Context {Name: NameWithEq}.
  Notation var := (@name Name).
  Existing Instance eq_name_dec.

  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.
  Context {vars: Type}.
  Context {varset: set vars var}.

  Ltac state_calc := state_calc_generic (@name Name) (word w).

  Lemma modVarsSound: forall fuel s initialS initialM finalS finalM,
    eval_stmt fuel initialS initialM s = Some (finalS, finalM) ->
    only_differ initialS (modVars s) finalS.
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
  Qed.

End ExprImp2.


Module TestExprImp.

Instance ZName: NameWithEq := {| name := Z |}.

Definition var: Set := (@name ZName). (* only inside this test module *)

(*
given x, y, z

if y < x and z < x then
  c = x
  a = y
  b = z
else if x < y and z < y then
  c = y
  a = x
  b = z
else
  c = z
  a = x
  b = y
isRight = a*a + b*b == c*c
*)
Definition _a := 0%Z.
Definition _b := 1%Z.
Definition _c := 2%Z.
Definition _isRight := 3%Z.

Definition isRight(x y z: word 16) :=
  SSeq (SIf (EOp OAnd (EOp OLt (ELit y) (ELit x)) (EOp OLt (ELit z) (ELit x)))
            (SSeq (SSet _c (ELit x)) (SSeq (SSet _a (ELit y)) (SSet _b (ELit z))))
            ((SIf (EOp OAnd (EOp OLt (ELit x) (ELit y)) (EOp OLt (ELit z) (ELit y)))
                  (SSeq (SSet _c (ELit y)) (SSeq (SSet _a (ELit x)) (SSet _b (ELit z))))
                  (SSeq (SSet _c (ELit z)) (SSeq (SSet _a (ELit x)) (SSet _b (ELit y)))))))
       (SSet _isRight (EOp OEq (EOp OPlus (EOp OTimes (EVar _a) (EVar _a))
                                          (EOp OTimes (EVar _b) (EVar _b)))
                               (EOp OTimes (EVar _c) (EVar _c)))).

Definition run_isRight(x y z: word 16): option (word 16) :=
  final <- (eval_stmt 10 empty (no_mem 16) (isRight x y z));
  let '(finalSt, finalM) := final in
  get finalSt _isRight.

Goal run_isRight $3 $4 $5 = Some $1. reflexivity. Qed.
Goal run_isRight $3 $7 $5 = Some $0. reflexivity. Qed.
Goal run_isRight $4 $3 $5 = Some $1. reflexivity. Qed.
Goal run_isRight $5 $3 $5 = Some $0. reflexivity. Qed.
Goal run_isRight $5 $3 $4 = Some $1. reflexivity. Qed.
Goal run_isRight $12 $13 $5 = Some $1. reflexivity. Qed.

End TestExprImp.
