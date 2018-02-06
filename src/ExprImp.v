Require Import Coq.Lists.List.
Import ListNotations.
Require Import lib.LibTacticsMin.
Require Import compiler.Common.
Require Import compiler.Tactics.
Require Import compiler.Op.
Require Import compiler.StateCalculus.
Require Import bbv.DepEqNat.
Require Import riscv.NameWithEq.
Require Import Coq.Program.Tactics.

Section ExprImp.

  Context {w: nat}. (* bit width *)

  Context {Name: NameWithEq}.
  Notation var := (@name Name).
  Existing Instance eq_name_dec.


  Context {state: Type}.
  Context {stateMap: Map state var (word w)}.
  Context {vars: Type}.
  Context {varset: set vars var}.

  Ltac state_calc := state_calc_generic (@name Name) (word w).

  Inductive expr: Set :=
    | ELit(v: word w): expr
    | EVar(x: var): expr
    | EOp(op: binop)(e1 e2: expr): expr.

  Inductive stmt: Set :=
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

  Fixpoint eval_stmt(f: nat)(st: state)(s: stmt): option state :=
    match f with
    | 0 => None (* out of fuel *)
    | Datatypes.S f' => match s with
      | SSet x e =>
          v <- eval_expr st e;
          Return (put st x v)
      | SIf cond bThen bElse =>
          v <- eval_expr st cond;
          eval_stmt f' st (if weq v $0 then bElse else bThen)
      | SWhile cond body =>
          v <- eval_expr st cond;
          if weq v $0 then Return st else
            st' <- eval_stmt f' st body;
            eval_stmt f' st' (SWhile cond body)
      | SSeq s1 s2 =>
          st' <- eval_stmt f' st s1;
          eval_stmt f' st' s2
      | SSkip => Return st
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
    | SSet x e => S (expr_size e)
    | SIf cond bThen bElse => S (expr_size cond + stmt_size bThen + stmt_size bElse)
    | SWhile cond body => S (expr_size cond + stmt_size body)
    | SSeq s1 s2 => S (stmt_size s1 + stmt_size s2)
    | SSkip => 1
    end.

  Lemma invert_eval_SSet: forall f st1 st2 x e,
    eval_stmt f st1 (SSet x e) = Some st2 ->
    exists v, eval_expr st1 e = Some v /\ st2 = put st1 x v.
  Proof.
    introv E. destruct f; [ discriminate |].
    simpl in E. destruct_one_match_hyp; [ | discriminate ].
    inversions E. eauto.
  Qed.

  Lemma invert_eval_SIf: forall f st1 st2 cond bThen bElse,
    eval_stmt (Datatypes.S f) st1 (SIf cond bThen bElse) = Some st2 ->
    exists cv,
      eval_expr st1 cond = Some cv /\ 
      (cv <> $0 /\ eval_stmt f st1 bThen = Some st2 \/
       cv = $0  /\ eval_stmt f st1 bElse = Some st2).
  Proof.
    introv E. simpl in E. destruct_one_match_hyp; [|discriminate].
    destruct_one_match_hyp; subst *; eexists; eapply (conj eq_refl); [right|left]; auto.
  Qed.

  Lemma invert_eval_SWhile: forall st1 st3 f cond body,
    eval_stmt (Datatypes.S f) st1 (SWhile cond body) = Some st3 ->
    exists cv,
      eval_expr st1 cond = Some cv /\
      (cv <> $0 /\ (exists st2, eval_stmt f st1 body = Some st2 /\ 
                               eval_stmt f st2 (SWhile cond body) = Some st3) \/
       cv = $0  /\ st1 = st3).
  Proof.
    introv E. simpl in E. destruct_one_match_hyp; [|discriminate].
    destruct_one_match_hyp.
    - inversion E. subst st3. clear E. eexists. eapply (conj eq_refl). right. auto.
    - destruct_one_match_hyp; [|discriminate]. eauto 10.
  Qed.

  Lemma invert_eval_SSeq: forall st1 st3 f s1 s2,
    eval_stmt (Datatypes.S f) st1 (SSeq s1 s2) = Some st3 ->
    exists st2, eval_stmt f st1 s1 = Some st2 /\ eval_stmt f st2 s2 = Some st3.
  Proof.
    introv E. simpl in E. destruct_one_match_hyp; [|discriminate]. eauto.
  Qed.

  Lemma invert_eval_SSkip: forall st1 st2 f,
    eval_stmt f st1 SSkip = Some st2 ->
    st1 = st2.
  Proof.
    introv E. destruct f; [discriminate|].
    simpl in E. inversions E. reflexivity.
  Qed.

  (* Returns a list to make it obvious that it's a finite set. *)
  Fixpoint allVars_expr(e: expr): list var :=
    match e with
    | ELit v => []
    | EVar x => [x]
    | EOp op e1 e2 => (allVars_expr e1) ++ (allVars_expr e2)
    end.

  Fixpoint allVars_stmt(s: stmt): list var := 
    match s with
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
    | SSet v _ => singleton_set v
    | SIf _ s1 s2 => union (modVars s1) (modVars s2)
    | SWhile _ body => modVars body
    | SSeq s1 s2 => union (modVars s1) (modVars s2)
    | SSkip => empty_set
    end.

  Lemma modVars_subset_allVars: forall x s,
    x \in ExprImp.modVars s ->
    In x (ExprImp.allVars_stmt s).
  Proof.
    intros.
    induction s; simpl in *.
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

  Lemma modVarsSound: forall fuel s initial final,
    eval_stmt fuel initial s = Some final ->
    only_differ initial (modVars s) final.
  Proof.
    induction fuel; introv Ev.
    - discriminate.
    - destruct s.
      + simpl in *. destruct_one_match_hyp; [|discriminate]. inversionss. state_calc.
      + simpl in *. destruct_one_match_hyp; [|discriminate].
        destruct_one_match_hyp.
        * subst *. specializes IHfuel; [ eassumption |]. state_calc.
        * subst *. specializes IHfuel; [ eassumption |]. state_calc.
      + apply invert_eval_SWhile in Ev.
        destruct Ev as [cv [Evcond [Ev | Ev]]].
        * destruct Ev as [Ne [mid2 [Ev2 Ev3]]].
          simpl.
          pose proof (IHfuel _ _ _ Ev2) as IH2.
          pose proof (IHfuel _ _ _ Ev3) as IH3.
          clear - IH2 IH3. state_calc.
        * destruct Ev as [? ?]. subst *. clear. state_calc.
      + apply invert_eval_SSeq in Ev.
        destruct Ev as [mid [Ev1 Ev2]]. simpl.
        pose proof (IHfuel _ _ _ Ev1) as IH1.
        pose proof (IHfuel _ _ _ Ev2) as IH2.
        clear - IH1 IH2. state_calc.
      + simpl. inversionss. state_calc.
  Qed.

End ExprImp.



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
  finalSt <- (eval_stmt 10 empty (isRight x y z));
  get finalSt _isRight.

Goal run_isRight $3 $4 $5 = Some $1. reflexivity. Qed.
Goal run_isRight $3 $7 $5 = Some $0. reflexivity. Qed.
Goal run_isRight $4 $3 $5 = Some $1. reflexivity. Qed.
Goal run_isRight $5 $3 $5 = Some $0. reflexivity. Qed.
Goal run_isRight $5 $3 $4 = Some $1. reflexivity. Qed.
Goal run_isRight $12 $13 $5 = Some $1. reflexivity. Qed.

End TestExprImp.
