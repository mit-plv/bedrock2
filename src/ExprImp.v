Ltac typeof x := match type of x with ?T => T end.
Notation "'typeof!' x" := (ltac:(let T := typeof x in exact T)) (at level 10).
Local Notation "'bind_Some' x <- a ; f" :=
  (match a with
   | Some x => f
   | None => None
   end)
    (right associativity, at level 60, x pattern).


Require compiler.Common.

Module Imp. (* TODO: file *)

Module Type ImpParameters.
  Parameter mword : Type.
  Parameter mword_nonzero : mword -> bool.

  Parameter varname : Type.
  Parameter funname : Type.
  Parameter actname : Type.
  Parameter bopname : Type.
  Parameter mem : Type.

  Parameter varmap : Type.
  Parameter varmap_operations : Common.Map varmap varname mword.

  Parameter interp_binop : bopname -> mword -> mword -> mword.
  Parameter load : mword -> mem -> option mword.
  Parameter store : mword -> mword -> mem -> option mem.
End ImpParameters.

Module Imp (P : ImpParameters).
  Import P.
  Existing Instance varmap_operations.
  Inductive expr  : Type :=
  | ELit(v: mword)
  | EVar(x: varname)
  | EOp(op: bopname) (e1 e2: expr).

  Inductive stmt :=
  | SLoad(x: varname) (addr: expr)
  | SStore(addr val: expr)
  | SSet(x: varname)(e: expr)
  | SIf(cond: expr)(bThen bElse: stmt)
  | SWhile(cond: expr)(body: stmt)
  | SSeq(s1 s2: stmt)
  | SSkip
  | SCall(binds: list varname)(f: funname)(args: list expr)
  | SIO(binds: list varname)(io : actname)(args: list expr).

  Section cont.
    Context {T : Type}.
    Inductive cont : Type :=
    | CSuspended(_:T)
    | CSeq(s1:cont) (s2: stmt)
    | CStack(st: varmap)(c: cont)(binds rets: list varname).
  End cont. Global Arguments cont : clear implicits.

  Definition ioact : Type := (list varname * actname * list mword).
  Definition ioret : Type := (list varname * list mword).

  Fixpoint interp_expr st e : option mword :=
    match e with
    | ELit v => Some v
    | EVar x => Common.get st x
    | EOp op e1 e2 =>
      bind_Some v1 <- interp_expr st e1;
        bind_Some v2 <- interp_expr st e2;
        Some (interp_binop op v1 v2)
    end.

  Section WithFunctions.
    Context (lookupFunction : funname -> option (list varname * list varname * stmt)).
    Fixpoint interp_stmt(f: nat)(st: varmap)(m: mem)(s: stmt): option (varmap*mem*option(cont ioact)) :=
      match f with
      | 0 => None (* out of fuel *)
      | S f => match s with
               | SLoad x a =>
                 bind_Some a <- interp_expr st a;
                   bind_Some v <- load a m;
                   Some (Common.put st x v, m, None)
               | SStore a v =>
                 bind_Some a <- interp_expr st a;
                   bind_Some v <- interp_expr st v;
                   bind_Some m <- store a v m;
                   Some (st, m, None)
               | SSet x e =>
                 bind_Some v <- interp_expr st e;
                   Some (Common.put st x v, m, None)
               | SIf cond bThen bElse =>
                 bind_Some v <- interp_expr st cond;
                   interp_stmt f st m (if mword_nonzero v then bThen else bElse)
               | SWhile cond body =>
                 bind_Some v <- interp_expr st cond;
                   if mword_nonzero v
                   then
                     bind_Some (st, m, c) <- interp_stmt f st m body;
                       match c with
                       | Some c => Some (st, m, Some (CSeq c (SWhile cond body)))
                       | None => interp_stmt f st m (SWhile cond body)
                       end
                   else Some (st, m, None)
               | SSeq s1 s2 =>
                 bind_Some (st, m, c) <- interp_stmt f st m s1;
                   match c with
                   | Some c => Some (st, m, Some (CSeq c s2))
                   | None => interp_stmt f st m s2
                   end
               | SSkip => Some (st, m, None)
               | SCall binds fname args =>
                 bind_Some (params, rets, fbody) <- lookupFunction fname;
                   bind_Some argvs <- Common.option_all (List.map (interp_expr st) args);
                   bind_Some st0 <- Common.putmany params argvs Common.empty;
                   bind_Some (st1, m', oc) <- interp_stmt f st0 m fbody;
                   match oc with
                   | Some c => Some (st, m', Some (CStack st1 c binds rets))
                   | None => 
                     bind_Some retvs <- Common.option_all (List.map (Common.get st1) rets);
                       bind_Some st' <- Common.putmany binds retvs st;
                       Some (st', m', None)
                   end
               | SIO binds ionum args =>
                 bind_Some argvs <- Common.option_all (List.map (interp_expr st) args);
                   Some (st, m, Some (CSuspended (binds, ionum, argvs)))
               end
      end.

    Fixpoint interp_cont(f: nat)(st: varmap)(m: mem)(s: cont ioret): option (varmap*mem*option(cont ioact)) :=
      match f with
      | 0 => None (* out of fuel *)
      | S f => match s with
               | CSuspended (binds, retvs) =>
                 bind_Some st' <- Common.putmany binds retvs st;
                   Some (st', m, None)
               | CSeq c s2 =>
                 bind_Some (st, m, oc) <- interp_cont f st m c;
                   match oc with
                   | Some c => Some (st, m, Some (CSeq c s2))
                   | None => interp_stmt f st m s2
                   end
               | CStack stf cf binds rets =>
                 bind_Some (stf', m', oc) <- interp_cont f stf m cf;
                   match oc with
                   | Some c => Some (st, m', Some (CStack stf' c binds rets))
                   | None => 
                     bind_Some retvs <- Common.option_all (List.map (Common.get stf') rets);
                       bind_Some st' <- Common.putmany binds retvs st;
                       Some (st', m', None)
                   end
               end
      end.
  End WithFunctions.
End Imp.

End Imp. (* TODO: file *)



Require riscv.util.BitWidths.
Require compiler.Memory.
Require compiler.Op.

Module RISCVImp. (* TODO: file *)

Module Type RISCVImpParameters.
  Parameter bw : riscv.util.BitWidths.BitWidths.
  Parameter varname : Type.
  Parameter funname : Type.
  Parameter actname : Type.
  Parameter varmap : Type.
  Parameter varmap_operations : Common.Map varmap varname (bbv.Word.word (@riscv.util.BitWidths.wXLEN bw)).
End RISCVImpParameters.

Module ImpParameters_of_RISCVImpParameters (P : RISCVImpParameters) <: Imp.ImpParameters.
  Import P.
  Definition mword := bbv.Word.word (@riscv.util.BitWidths.wXLEN bw).
  Definition mword_nonzero := fun v => if bbv.Word.weq v (bbv.Word.wzero _ : mword) then false else true.
  Definition varname := varname.
  Definition funname := funname.
  Definition actname := actname.
  Definition bopname := compiler.Op.binop.
  Definition mem := @compiler.Memory.mem bw.

  Definition interp_binop := @compiler.Op.eval_binop (@riscv.util.BitWidths.wXLEN bw).
  Definition load := @Memory.read_mem bw.
  Definition store := @Memory.write_mem bw.

  Definition varmap := varmap.
  Definition varmap_operations := varmap_operations.
End ImpParameters_of_RISCVImpParameters.

End RISCVImp. (* TODO: file *)



Require Import compiler.Common.
Require Import Coq.Lists.List.
Import ListNotations.
Require Import lib.LibTacticsMin.
Require Import riscv.util.BitWidths.
Require Import compiler.Tactics.
Require Import compiler.Op.
Require Import compiler.StateCalculus.
Require Import bbv.DepEqNat.
Require Import compiler.NameWithEq.
Require Import Coq.Program.Tactics.
Require Import compiler.Memory.

Module ImpInversion (P : Imp.ImpParameters).
  Import P.
  Module Imp := Imp.Imp P.
  Import Imp.
  
  Lemma cont_uninhabited (T:Set) (_:T -> False) (X : cont T) : False. Proof. induction X; auto 2. Qed.

  Fixpoint expr_size(e: expr): nat :=
    match e with
    | ELit _ => 8
    | EVar _ => 1
    | EOp op e1 e2 => S (S (expr_size e1 + expr_size e2))
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
    | SCall binds _ args | SIO binds _ args =>
                           S (length binds + length args + List.fold_right Nat.add O (List.map expr_size args))
    end.

  Local Ltac inversion_lemma :=
    intros;
    simpl in *;
    repeat (destruct_one_match_hyp; try discriminate);
    inversionss;
    eauto 99.

  Lemma invert_interp_SLoad: forall env fuel initialSt initialM x e final,
      interp_stmt env (S fuel) initialSt initialM (SLoad x e) = Some final ->
      exists a v, interp_expr initialSt e = Some a /\
                  load a initialM = Some v /\
                  final = (put initialSt x v, initialM, None).
  Proof. inversion_lemma. Qed.

  Lemma invert_interp_SStore: forall env fuel initialSt initialM a v final,
    interp_stmt env (S fuel) initialSt initialM (SStore a v) = Some final ->
    exists av vv finalM, interp_expr initialSt a = Some av /\
                         interp_expr initialSt v = Some vv /\
                         store av vv initialM = Some finalM /\
                         final = (initialSt, finalM, None).
  Proof. inversion_lemma. Qed.

  Lemma invert_interp_SSet: forall env f st1 m1 p2 x e,
    interp_stmt env (S f) st1 m1 (SSet x e) = Some p2 ->
    exists v, interp_expr st1 e = Some v /\ p2 = (put st1 x v, m1, None).
  Proof. inversion_lemma. Qed.

  Lemma invert_interp_SIf: forall env f st1 m1 p2 cond bThen bElse,
    interp_stmt env (S f) st1 m1 (SIf cond bThen bElse) = Some p2 ->
    exists cv,
      interp_expr st1 cond = Some cv /\ 
      (mword_nonzero cv = true /\ interp_stmt env f st1 m1 bThen = Some p2 \/
       mword_nonzero cv = false /\ interp_stmt env f st1 m1 bElse = Some p2).
  Proof. inversion_lemma. Qed.

  Lemma invert_interp_SSkip: forall env st1 m1 p2 f,
    interp_stmt env (S f) st1 m1 SSkip = Some p2 ->
    p2 = (st1, m1, None).
  Proof. inversion_lemma. Qed.

  Lemma invert_interp_SSeq: forall env st1 m1 p3 f s1 s2,
    interp_stmt env (S f) st1 m1 (SSeq s1 s2) = Some p3 ->
    exists st2 m2 oc, interp_stmt env f st1 m1 s1 = Some (st2, m2, oc) /\ (
        (oc = None /\ interp_stmt env f st2 m2 s2 = Some p3)
     \/ (exists c, oc = Some c /\ p3 = (st2, m2, Some (CSeq c s2)))).
  Proof. inversion_lemma. Qed.

  Lemma invert_interp_SWhile: forall env st1 m1 p3 f cond body,
    interp_stmt env (S f) st1 m1 (SWhile cond body) = Some p3 ->
    exists cv,
      interp_expr st1 cond = Some cv /\
      (mword_nonzero cv = true /\
       (exists st2 m2 oc, interp_stmt env f st1 m1 body = Some (st2, m2, oc) /\ (
              ( oc = None /\ interp_stmt env f st2 m2 (SWhile cond body) = Some p3)
           \/ ( exists c, oc = Some c /\ p3 = (st2, m2, Some (CSeq c (SWhile cond body))))))
       \/ mword_nonzero cv = false /\ p3 = (st1, m1, None)).
  Proof. inversion_lemma. Qed.

  Lemma invert_interp_SCall : forall env st m1 p2 f binds fname args,
    interp_stmt env (S f) st m1 (SCall binds fname args) = Some p2 ->
    exists params rets fbody argvs st0 st1 m' oc,
      env fname = Some (params, rets, fbody) /\
      option_all (map (interp_expr st) args) = Some argvs /\
      putmany params argvs empty = Some st0 /\
      interp_stmt env f st0 m1 fbody = Some (st1, m', oc) /\ (
       ( oc = None /\ exists retvs st',
         option_all (map (get st1) rets) = Some retvs /\
         putmany binds retvs st = Some st' /\
         p2 = (st', m', None)
       ) \/
       ( exists c, oc = Some c /\
         p2 = (st, m', Some (CStack st1 c binds rets)) ) ).
  Proof. inversion_lemma. Qed.

  Lemma invert_interp_SIO : forall env st m1 p2 f binds ioname args,
    interp_stmt env (S f) st m1 (SIO binds ioname args) = Some p2 ->
    exists argvs, option_all (map (interp_expr st) args) = Some argvs /\
                  p2 = (st, m1, Some (CSuspended (binds, ioname, argvs))).
  Proof. inversion_lemma. Qed.

  Local Tactic Notation "marker" ident(s) := let x := fresh s in pose proof tt as x; move x at top.
  Ltac invert_interp_stmt :=
    lazymatch goal with
    | E: interp_stmt _ _ (S ?fuel) _ _ ?s = Some _ |- _ =>
      destruct s;
      [ apply invert_interp_SLoad in E; deep_destruct E; marker SLoad
      | apply invert_interp_SStore in E; deep_destruct E; marker SStore
      | apply invert_interp_SSet in E; deep_destruct E; marker SSet
      | apply invert_interp_SIf in E; deep_destruct E; [marker SIf_true | marker SIf_false]
      | apply invert_interp_SWhile in E; deep_destruct E; [marker SWhile_true | marker SWhile_blocked | marker SWhile_false ]
      | apply invert_interp_SSeq in E; deep_destruct E; [marker SSeq | marker SSeq_blocked ]
      | apply invert_interp_SSkip in E; deep_destruct E; marker SSkip
      | apply invert_interp_SCall in E; deep_destruct E; [marker SCall | marker SCall_blocked]
      | apply invert_interp_SIO in E; deep_destruct E; [marker SIO ]
      ] end.
End ImpInversion.

Module ImpVars (P : Imp.ImpParameters). (* TODO: file *)
  Import P.
  Module Imp := Imp.Imp P.
  Import Imp.
  Module ImpInversion := ImpInversion P.
  Import ImpInversion.
  Goal Top.ImpVars.ImpInversion.Imp.expr = Top.ImpVars.Imp.expr.
    Fail reflexivity.
  Abort.
    (* 
  Module Imp := Imp.Imp P.
  Import Imp.
  Context {p:ImpParameters}.
  (* RecordImport p (* COQBUG(https://github.com/coq/coq/issues/7808) *) *)
  Local Notation mword := p.(mword).
  Local Notation mword_nonzero := p.(mword_nonzero).
  Local Notation varname := p.(varname).
  Local Notation funname := p.(funname).
  Local Notation actname := p.(actname).
  Local Notation bopname := p.(bopname).
  Local Notation varmap := p.(varmap).
  Local Notation mem := p.(mem).
  Local Notation interp_binop := p.(interp_binop).
  Local Notation load := p.(load).
  Local Notation store := p.(store).
  Let Imp : Imp.ImpInterface p := Imp.Imp p.
  (* RecordImport Imp (* COQBUG(https://github.com/coq/coq/issues/7808) *) *)
  Local Notation expr := Imp.(expr).
  Local Notation stmt := Imp.(stmt).
  Local Notation cont := Imp.(cont).
  Local Notation interp_expr := Imp.(interp_expr).
  Local Notation interp_stmt := Imp.(interp_stmt).
  Local Notation interp_cont := Imp.(interp_cont).

  (* TODO: record ImpParametersOK *)
  Context {mword_eq_dec : DecidableEq (Imp.varname p)}.

  (* Returns a list to make it obvious that it's a finite set. *)
  Fixpoint allVars_expr(e: expr): list varname :=
    match e with
    | Imp_.ELit v => []
    | Imp_.EVar x => [x]
    | Imp_.EOp op e1 e2 => (allVars_expr e1) ++ (allVars_expr e2)
    end.

  Fixpoint allVars_stmt(s: stmt): list varname := 
    match s with
    | Imp_.SLoad v e => v :: allVars_expr e
    | Imp_.SStore a e => (allVars_expr a) ++ (allVars_expr e)
    | Imp_.SSet v e => v :: allVars_expr e
    | Imp_.SIf c s1 s2 => (allVars_expr c) ++ (allVars_stmt s1) ++ (allVars_stmt s2)
    | Imp_.SWhile c body => (allVars_expr c) ++ (allVars_stmt body)
    | Imp_.SSeq s1 s2 => (allVars_stmt s1) ++ (allVars_stmt s2)
    | Imp_.SSkip => []
    | Imp_.SCall binds _ args | Imp_.SIO binds _ args => binds ++ List.fold_right (@List.app _) nil (List.map allVars_expr args)
    end.

  Context {set_varname: Type}.
  Context {varset: set set_varname varname}.

  (* Returns a static approximation of the set of modified vars.
     The returned set might be too big, but is guaranteed to include all modified vars. *)
  Fixpoint modVars(s: stmt): set_varname := 
    match s with
    | Imp_.SLoad v _ => singleton_set v
    | Imp_.SStore _ _ => empty_set
    | Imp_.SSet v _ => singleton_set v
    | Imp_.SIf _ s1 s2 => union (modVars s1) (modVars s2)
    | Imp_.SWhile _ body => modVars body
    | Imp_.SSeq s1 s2 => union (modVars s1) (modVars s2)
    | Imp_.SSkip => empty_set
    | Imp_.SCall binds _ _ | Imp_.SIO binds _ _ => of_list binds
    end.

  Ltac set_solver := set_solver_generic constr:(varname).
  
  Lemma modVars_subset_allVars: forall x s,
    x \in modVars s ->
    In x (allVars_stmt s).
  Proof.
    intros.
    induction s; simpl in *.
    { set_solver. }
    { set_solver. }
    { apply singleton_set_spec in H. auto. }
    { apply union_spec in H.
      apply in_or_app. right. apply in_or_app.
      destruct H as [H|H]; auto. }
    { apply in_or_app. right. auto. }
    { apply union_spec in H.
      apply in_or_app.
      destruct H as [H|H]; auto. }
    { eapply empty_set_spec. eassumption. }
    1,2 : generalize dependent binds; induction binds; intros H; cbn in *;
      [ apply empty_set_spec in H; destruct H
      | apply union_spec in H; destruct H;
        [ left; apply singleton_set_spec in H; auto
        | right; auto ] ].
  Qed.

  Ltac state_calc := state_calc_generic constr:(varname) constr:(mword).

  Lemma modVarsSound: forall env fuel s initialS initialM finalS finalM oc,
    interp_stmt env fuel initialS initialM s = Some (finalS, finalM, oc) ->
    only_differ initialS (modVars s) finalS.
  Proof.
    induction fuel; introv Ev.
    - discriminate.
    - invert_interp_stmt; cbn [modVars] in *; inversionss;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          cbn [modVars] in IH';
          ensure_new IH'
      end;
      state_calc.
      (* SCall *)
      refine (only_differ_putmany _ _ _ _ _ _); eassumption.
  Qed.
*)
    
End ImpVars. (* TODO: file *)


Require riscv.util.BitWidth32.
Module TestExprImp.
  Module TestParameters <: RISCVImp.RISCVImpParameters.
    Definition bw := riscv.util.BitWidth32.BitWidth32.
    Definition varname := Z.
    Definition funname := Empty_set.
    Definition actname := Empty_set.
    Definition varmap := varname -> option (bbv.Word.word (@riscv.util.BitWidths.wXLEN bw)). 
    Definition varmap_operations : Common.Map varmap varname (bbv.Word.word (@riscv.util.BitWidths.wXLEN bw)).
      eapply Function_Map.
      eapply Z.eq_dec.
    Defined.
  End TestParameters.

  Module TestParameters' := RISCVImp.ImpParameters_of_RISCVImpParameters TestParameters.
  Module Imp := Imp.Imp TestParameters'.
  Import Imp.

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

Definition isRight(x y z: word 32) : stmt :=
  SSeq (SIf (EOp OAnd (EOp OLt (ELit y) (ELit x)) (EOp OLt (ELit z) (ELit x)))
            (SSeq (SSet _c (ELit x)) (SSeq (SSet _a (ELit y)) (SSet _b (ELit z))))
            ((SIf (EOp OAnd (EOp OLt (ELit x) (ELit y)) (EOp OLt (ELit z) (ELit y)))
                  (SSeq (SSet _c (ELit y)) (SSeq (SSet _a (ELit x)) (SSet _b (ELit z))))
                  (SSeq (SSet _c (ELit z)) (SSeq (SSet _a (ELit x)) (SSet _b (ELit y)))))))
       (SSet _isRight (EOp OEq (EOp OPlus (EOp OTimes (EVar _a) (EVar _a))
                                          (EOp OTimes (EVar _b) (EVar _b)))
                               (EOp OTimes (EVar _c) (EVar _c)))).

Definition run_isRight(x y z: word 32): option (word 32) :=
  bind_Some (finalSt, finalM, oc) <- interp_stmt (fun _ => None) 10 empty no_mem (isRight x y z);
  match oc with Some _ => None | None =>
  get finalSt _isRight end.

Goal run_isRight $3 $4 $5 = Some $1. reflexivity. Qed.
Goal run_isRight $3 $7 $5 = Some $0. reflexivity. Qed.
Goal run_isRight $4 $3 $5 = Some $1. reflexivity. Qed.
Goal run_isRight $5 $3 $5 = Some $0. reflexivity. Qed.
Goal run_isRight $5 $3 $4 = Some $1. reflexivity. Qed.
Goal run_isRight $12 $13 $5 = Some $1. reflexivity. Qed.

End TestExprImp.