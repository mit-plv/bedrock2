Set Primitive Projections.
Unset Printing Primitive Projection Parameters.
Set Printing Projections.

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

Record ImpParameters :=
  {
    mword : Type;
    mword_nonzero : mword -> bool;

    varname : Type;
    funname : Type;
    actname : Type;
    bopname : Type;
    mem : Type;

    varmap : Type;
    varmap_operations : Common.Map varmap varname mword;

    interp_binop : bopname -> mword -> mword -> mword;
    load : mword -> mem -> option mword;
    store : mword -> mword -> mem -> option mem;
  }.

Module Imp_.
  Section Imp_.
    Context {p : ImpParameters}.
    (* RecordImport p (* COQBUG(https://github.com/coq/coq/issues/7808) *) *)
    Local Notation mword := p.(mword).
    Local Notation mword_nonzero := p.(mword_nonzero).
    Local Notation varname := p.(varname).
    Local Notation funname := p.(funname).
    Local Notation actname := p.(actname).
    Local Notation bopname := p.(bopname).
    Local Notation varmap := p.(varmap).
    Local Notation mem := p.(mem).
    Local Definition varmap_operations_ : Common.Map _ _ _ := p.(varmap_operations). Global Existing Instance varmap_operations_.
    Local Notation interp_binop := p.(interp_binop).
    Local Notation load := p.(load).
    Local Notation store := p.(store).
    Local Inductive expr  : Type :=
    | ELit(v: mword)
    | EVar(x: varname)
    | EOp(op: bopname) (e1 e2: expr).

    Local Inductive stmt :=
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
      Local Inductive cont : Type :=
      | CSuspended(_:T)
      | CSeq(s1:cont) (s2: stmt)
      | CStack(st: varmap)(c: cont)(binds rets: list varname).
    End cont. Global Arguments cont : clear implicits.

    Local Definition ioact : Type := (actname * list mword * list varname).
    Local Definition ioret : Type := (list mword * list varname).

    Local Fixpoint interp_expr st e : option mword :=
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
      Local Fixpoint interp_stmt(f: nat)(st: varmap)(m: mem)(s: stmt): option (varmap*mem*option(cont ioact)) :=
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
            Some (st, m, Some (CSuspended (ionum, argvs, binds)))
          end
        end.

      Local Fixpoint interp_cont(f: nat)(st: varmap)(m: mem)(s: cont ioret): option (varmap*mem*option(cont ioact)) :=
        match f with
        | 0 => None (* out of fuel *)
        | S f => match s with
          | CSuspended (retvs, binds) =>
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
  End Imp_.
  Global Arguments expr : clear implicits.
  Global Arguments stmt : clear implicits.
  Global Arguments cont : clear implicits.
End Imp_.

(* type of the following record value... COQBUG(https://github.com/coq/coq/issues/7810) *)
Record ImpInterface {p:ImpParameters} :=
  {
    expr : typeof! (@Imp_.expr p);
    ELit : typeof! (@Imp_.ELit p);
    EVar : typeof! (@Imp_.EVar p);
    EOp : typeof! (@Imp_.EOp p);
    expr_rect : typeof! (@Imp_.expr_rect p);

    stmt : typeof! (@Imp_.stmt p);
    SLoad : typeof! (@Imp_.SLoad p);
    SStore : typeof! (@Imp_.SStore p);
    SSet : typeof! (@Imp_.SSet p);
    SIf : typeof! (@Imp_.SIf p);
    SWhile : typeof! (@Imp_.SWhile p);
    SSeq : typeof! (@Imp_.SSeq p);
    SSkip : typeof! (@Imp_.SSkip p);
    SCall : typeof! (@Imp_.SCall p);
    SIO : typeof! (@Imp_.SIO p);
    stmt_rect : typeof! (@Imp_.stmt_rect p);

    cont : typeof! (@Imp_.cont p);
    CSuspended : typeof! (@Imp_.CSuspended p);
    CSeq : typeof! (@Imp_.CSeq p);
    CStack : typeof! (@Imp_.CStack p);
    cont_rect : typeof! (@Imp_.cont_rect p);

    ioact : typeof! (@Imp_.ioact p);
    ioret : typeof! (@Imp_.ioret p);

    interp_expr : typeof! (@Imp_.interp_expr p);
    interp_stmt : typeof! (@Imp_.interp_stmt p);
    interp_cont : typeof! (@Imp_.interp_cont p);
  }.
Global Arguments ImpInterface : clear implicits.
Global Arguments CSuspended {_} _ [_].
Global Arguments CSeq {_} _ [_].
Global Arguments CSeq {_} _ [_].

Definition Imp (p : ImpParameters) : ImpInterface p :=
  {|
    expr := @Imp_.expr p;
    ELit := @Imp_.ELit p;
    EVar := @Imp_.EVar p;
    EOp := @Imp_.EOp p;
    expr_rect := @Imp_.expr_rect p;
    
    stmt := @Imp_.stmt p;
    SLoad := @Imp_.SLoad p;
    SStore := @Imp_.SStore p;
    SSet := @Imp_.SSet p;
    SIf := @Imp_.SIf p;
    SWhile := @Imp_.SWhile p;
    SSeq := @Imp_.SSeq p;
    SSkip := @Imp_.SSkip p;
    SCall := @Imp_.SCall p;
    SIO := @Imp_.SIO p;
    stmt_rect := @Imp_.stmt_rect p;

    cont := Imp_.cont p;
    CSuspended := @Imp_.CSuspended p;
    CSeq := @Imp_.CSeq p;
    CStack := @Imp_.CStack p;
    cont_rect := @Imp_.cont_rect p;
    
    ioact := @Imp_.ioact p;
    ioret := @Imp_.ioret p;

    interp_expr := @Imp_.interp_expr p;
    interp_stmt := @Imp_.interp_stmt p;
    interp_cont := @Imp_.interp_cont p;
  |}.

End Imp. (* TODO: file *)



Require riscv.util.BitWidths.
Require compiler.Memory.
Require compiler.Op.

Module RISCVImp. (* TODO: file *)

Record RISCVImpParameters :=
  {
    bw : riscv.util.BitWidths.BitWidths;
    varname : Type;
    funname : Type;
    actname : Type;
    varmap : Type;
    varmap_operations : Common.Map varmap varname (bbv.Word.word (riscv.util.BitWidths.wXLEN));
  }.

Definition ImpParameters_of_RISCVImpParameters (p:RISCVImpParameters): Imp.ImpParameters :=
  {|
    Imp.mword := bbv.Word.word (@riscv.util.BitWidths.wXLEN p.(bw));
    Imp.mword_nonzero := fun v => if bbv.Word.weq v (bbv.Word.wzero _) then false else true;
    Imp.varname := p.(varname);
    Imp.funname := p.(funname);
    Imp.actname := p.(actname);
    Imp.bopname := compiler.Op.binop;
    Imp.mem := compiler.Memory.mem;

    Imp.interp_binop := compiler.Op.eval_binop;
    Imp.load := Memory.read_mem;
    Imp.store := Memory.write_mem;

    Imp.varmap := p.(varmap);
    Imp.varmap_operations := p.(varmap_operations);
  |}.
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

Module ImpInversion. (* TODO: file*)
Section ImpInversion.
  Import Imp.
  Context (p:ImpParameters).
  Let Imp : Imp.ImpInterface p := Imp.Imp p.
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
  (* RecordImport Imp (* COQBUG(https://github.com/coq/coq/issues/7808) *) *)
  Local Notation expr := Imp.(expr).
  Local Notation ELit := Imp.(ELit).
  Local Notation EVar := Imp.(EVar).
  Local Notation EOp := Imp.(EOp).
  Local Notation expr_rect := Imp.(expr_rect).
  Local Notation stmt := Imp.(stmt).
  Local Notation SLoad := Imp.(SLoad).
  Local Notation SStore := Imp.(SStore).
  Local Notation SSet := Imp.(SSet).
  Local Notation SIf := Imp.(SIf).
  Local Notation SWhile := Imp.(SWhile).
  Local Notation SSeq := Imp.(SSeq).
  Local Notation SSkip := Imp.(SSkip).
  Local Notation SCall := Imp.(SCall).
  Local Notation SIO := Imp.(SIO).
  Local Notation stmt_rect := Imp.(stmt_rect).
  Local Notation cont := Imp.(cont).
  Local Notation CSuspended := Imp.(CSuspended).
  Local Notation CSeq := Imp.(CSeq).
  Local Notation CStack := Imp.(CStack).
  Local Notation cont_rect := Imp.(cont_rect).
  Local Notation ioact := Imp.(ioact).
  Local Notation ioret := Imp.(ioret).
  Local Notation interp_expr := Imp.(interp_expr).
  Local Notation interp_stmt := Imp.(interp_stmt).
  Local Notation interp_cont := Imp.(interp_cont).
  
  Lemma cont_uninhabited (T:Set) (_:T -> False) (X : cont T) : False. Proof. induction X; auto 2. Qed.

  Fixpoint expr_size(e: expr): nat :=
    match e with
    | Imp_.ELit _ => 8
    | Imp_.EVar _ => 1
    | Imp_.EOp op e1 e2 => S (S (expr_size e1 + expr_size e2))
    end.

  Fixpoint stmt_size(s: stmt): nat :=
    match s with
    | Imp_.SLoad x a => S (expr_size a)
    | Imp_.SStore a v => S (expr_size a + expr_size v)
    | Imp_.SSet x e => S (expr_size e)
    | Imp_.SIf cond bThen bElse => S (expr_size cond + stmt_size bThen + stmt_size bElse)
    | Imp_.SWhile cond body => S (expr_size cond + stmt_size body)
    | Imp_.SSeq s1 s2 => S (stmt_size s1 + stmt_size s2)
    | Imp_.SSkip => 1
    | Imp_.SCall binds _ args | Imp_.SIO binds _ args =>
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
         p2 = (st, m', Some (CStack _ st1 c binds rets)) ) ).
  Proof. inversion_lemma. Qed.

  Lemma invert_interp_SIO : forall env st m1 p2 f binds ioname args,
    interp_stmt env (S f) st m1 (SIO binds ioname args) = Some p2 ->
    exists argvs, option_all (map (interp_expr st) args) = Some argvs /\
                  p2 = (st, m1, Some (CSuspended (ioname, argvs, binds))).
  Proof. inversion_lemma. Qed.
End ImpInversion.

Local Tactic Notation "marker" ident(s) := let x := fresh s in pose proof tt as x; move x at top.
Ltac invert_interp_stmt :=
  lazymatch goal with
  | E: Imp.interp_stmt _ _ (S ?fuel) _ _ ?s = Some _ |- _ =>
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
End ImpInversion. (* TODO: file *)

Module ImpVars. (* TODO: file *)
Import ImpInversion.
Section ImpVars.
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
  Local Notation ELit := Imp.(ELit).
  Local Notation EVar := Imp.(EVar).
  Local Notation EOp := Imp.(EOp).
  Local Notation expr_rect := Imp.(expr_rect).
  Local Notation stmt := Imp.(stmt).
  Local Notation SLoad := Imp.(SLoad).
  Local Notation SStore := Imp.(SStore).
  Local Notation SSet := Imp.(SSet).
  Local Notation SIf := Imp.(SIf).
  Local Notation SWhile := Imp.(SWhile).
  Local Notation SSeq := Imp.(SSeq).
  Local Notation SSkip := Imp.(SSkip).
  Local Notation SCall := Imp.(SCall).
  Local Notation SIO := Imp.(SIO).
  Local Notation stmt_rect := Imp.(stmt_rect).
  Local Notation cont := Imp.(cont).
  Local Notation CSuspended := Imp.(CSuspended).
  Local Notation CSeq := Imp.(CSeq).
  Local Notation CStack := Imp.(CStack).
  Local Notation cont_rect := Imp.(cont_rect).
  Local Notation ioact := Imp.(ioact).
  Local Notation ioret := Imp.(ioret).
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

End ImpVars.
End ImpVars. (* TODO: file *)


Require riscv.util.BitWidth32.
Module TestExprImp.
Import Imp compiler.Op.
Local Definition ImpParameters :=
  RISCVImp.ImpParameters_of_RISCVImpParameters
  {|
    RISCVImp.bw := riscv.util.BitWidth32.BitWidth32;
    RISCVImp.varname := Z;
    RISCVImp.funname := Empty_set;
    RISCVImp.actname := Empty_set;
  |}.
Local Definition Imp := Imp ImpParameters.

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

(* RecordImport Imp (* COQBUG(https://github.com/coq/coq/issues/7808) *) *)
Local Notation expr := Imp.(expr).
Local Notation ELit := Imp.(ELit).
Local Notation EVar := Imp.(EVar).
Local Notation EOp := Imp.(EOp).
Local Notation expr_rect := Imp.(expr_rect).
Local Notation stmt := Imp.(stmt).
Local Notation SLoad := Imp.(SLoad).
Local Notation SStore := Imp.(SStore).
Local Notation SSet := Imp.(SSet).
Local Notation SIf := Imp.(SIf).
Local Notation SWhile := Imp.(SWhile).
Local Notation SSeq := Imp.(SSeq).
Local Notation SSkip := Imp.(SSkip).
Local Notation SCall := Imp.(SCall).
Local Notation SIO := Imp.(SIO).
Local Notation stmt_rect := Imp.(stmt_rect).
Local Notation cont := Imp.(cont).
Local Notation CSuspended := Imp.(CSuspended).
Local Notation CSeq := Imp.(CSeq).
Local Notation CStack := Imp.(CStack).
Local Notation cont_rect := Imp.(cont_rect).
Local Notation ioact := Imp.(ioact).
Local Notation ioret := Imp.(ioret).
Local Notation interp_expr := Imp.(interp_expr).
Local Notation interp_stmt := Imp.(interp_stmt).
Local Notation interp_cont := Imp.(interp_cont).

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


Module TRC.
  Local Set Universe Polymorphism.
  Section TRC.
    Context {T : Type} {R : T -> T -> Type}.
    Inductive trc : T -> T -> Prop :=
    | nil x : trc x x
    | cons x y z (head:R x y) (tail:trc y z) : trc x z.
    Definition singleton x y (r:R x y) : trc x y := cons x y y r (nil _).
    Definition app x y z (xy:trc x y) (yz:trc y z) : trc x z.
    Proof.
      revert dependent z; revert dependent xy; induction 1;
        eauto using nil, cons, singleton.
    Qed.
  End TRC.
  Arguments trc {T} R.
End TRC.

Module InteractionSemantics.
  Import Imp.

  (** Template for quantifying over semantics of possible environments. *)

  Module ContStep.
    Section ContStep.
      Context {p : Imp.ImpParameters}.
      Let Imp : Imp.ImpInterface p := Imp.Imp p.
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
      (* RecordImport Imp (* COQBUG(https://github.com/coq/coq/issues/7808) *) *)
      Local Notation expr := Imp.(expr).
      Local Notation ELit := Imp.(ELit).
      Local Notation EVar := Imp.(EVar).
      Local Notation EOp := Imp.(EOp).
      Local Notation expr_rect := Imp.(expr_rect).
      Local Notation stmt := Imp.(stmt).
      Local Notation SLoad := Imp.(SLoad).
      Local Notation SStore := Imp.(SStore).
      Local Notation SSet := Imp.(SSet).
      Local Notation SIf := Imp.(SIf).
      Local Notation SWhile := Imp.(SWhile).
      Local Notation SSeq := Imp.(SSeq).
      Local Notation SSkip := Imp.(SSkip).
      Local Notation SCall := Imp.(SCall).
      Local Notation SIO := Imp.(SIO).
      Local Notation stmt_rect := Imp.(stmt_rect).
      Local Notation cont := Imp.(cont).
      Local Notation CSuspended := Imp.(CSuspended).
      Local Notation CSeq := Imp.(CSeq).
      Local Notation CStack := Imp.(CStack).
      Local Notation cont_rect := Imp.(cont_rect).
      Local Notation ioact := Imp.(ioact).
      Local Notation ioret := Imp.(ioret).
      Local Notation interp_expr := Imp.(interp_expr).
      Local Notation interp_stmt := Imp.(interp_stmt).
      Local Notation interp_cont := Imp.(interp_cont).

      Fixpoint lift_cont {A B : Type} (a : cont A) (b : cont B) (P : A -> B -> Prop) {struct a} :=
        match a with
        | Imp_.CSuspended a => exists b', b = Imp_.CSuspended b' /\ P a b'
        | Imp_.CSeq a sa => exists b', b = Imp_.CSeq b' sa /\ lift_cont a b' P
        | Imp_.CStack sta a ba ra => exists b', b = Imp_.CStack sta b' ba ra /\ lift_cont a b' P
        end.
      
      Definition lift_option_cont {A B : Type} (a : option (cont A)) (b : option (cont B)) (P : A -> B -> Prop) :=
        match a with None => b = None | Some a => exists b', b = Some b' /\ lift_cont a b' P end.

      Context
        (e : funname -> option (list varname * list varname * stmt))
        (sys : Type) (external : (actname * list mword * mem * sys) -> (list mword * mem * sys) -> Prop).
      Let state : Type := varmap * mem * option (cont ioret) * sys.
      Definition step : state -> state -> Prop :=
        fun '(l0, m0, oc0, s0) S' =>
          exists c0, oc0 = Some c0 /\
          exists l1 m1 oc1 s1, S' = (l1, m1, oc1, s1) /\
          exists m' oc',
          ( (exists f, interp_cont e f l0 m0 c0 = Some (l1, m', oc'))
            ->
            lift_option_cont oc' oc1 (fun b' b1 =>
                                        exists av rb, b' = (av, rb) /\
                                        exists rv, b1 = (rv, rb) /\ external (av, m', s0) (rv, m1, s1))).
      Definition steps := TRC.trc step.

      (*
      Lemma step_CSeq l0 m0 c0 s0 l1 m1 c1 s1 s :
        step (l0, m0, Some (CSeq c0 s), s0) (l1, m1, Some (CSeq c1 s), s1)
        <-> step (l0, m0, Some c0, s0) (l1, m1, Some c1, s1).
      Proof.
        split.
        admit.
        { cbn; intros.
          repeat match goal with
                 | H: exists _, _ |- _ => destruct H
                 | H: _ /\ _ |- _ => destruct H
                 end.
          repeat eexists.
       *)
    End ContStep.
  End ContStep.

  (* TODO: file module? *)
  Record ContStepInterface {p} :Type :=
    {
      step : typeof! (@ContStep.step p);
      steps : typeof! (@ContStep.steps p)
    }.
  Definition ContStep p : ContStepInterface (p:=p) :=
    {|
      step := @ContStep.step p;
      steps := @ContStep.steps p;
    |}.

  Module ContTrace.
    Section ContTrace.
      Context {p : Imp.ImpParameters}.
      Let Imp : Imp.ImpInterface p := Imp.Imp p.
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
      (* RecordImport Imp (* COQBUG(https://github.com/coq/coq/issues/7808) *) *)
      Local Notation expr := Imp.(expr).
      Local Notation ELit := Imp.(ELit).
      Local Notation EVar := Imp.(EVar).
      Local Notation EOp := Imp.(EOp).
      Local Notation expr_rect := Imp.(expr_rect).
      Local Notation stmt := Imp.(stmt).
      Local Notation SLoad := Imp.(SLoad).
      Local Notation SStore := Imp.(SStore).
      Local Notation SSet := Imp.(SSet).
      Local Notation SIf := Imp.(SIf).
      Local Notation SWhile := Imp.(SWhile).
      Local Notation SSeq := Imp.(SSeq).
      Local Notation SSkip := Imp.(SSkip).
      Local Notation SCall := Imp.(SCall).
      Local Notation SIO := Imp.(SIO).
      Local Notation stmt_rect := Imp.(stmt_rect).
      Local Notation cont := Imp.(cont).
      Local Notation CSuspended := Imp.(CSuspended).
      Local Notation CSeq := Imp.(CSeq).
      Local Notation CStack := Imp.(CStack).
      Local Notation cont_rect := Imp.(cont_rect).
      Local Notation ioact := Imp.(ioact).
      Local Notation ioret := Imp.(ioret).
      Local Notation interp_expr := Imp.(interp_expr).
      Local Notation interp_stmt := Imp.(interp_stmt).
      Local Notation interp_cont := Imp.(interp_cont).
      Let ContStep := ContStep p.

      Definition cont_of_stmt (s : stmt) : cont ioret := CSeq (CSuspended (nil, nil)) s.
      Lemma interp_cont_of_stmt' e f l m s : interp_cont e (S f) l m (cont_of_stmt s) = interp_stmt e f l m s.
      Proof. destruct f; reflexivity. Qed.

      Definition event : Type := actname * (mem * list mword) * (mem * list mword).
      Context (e : funname -> option (list varname * list varname * stmt)).
      Let state : Type := varmap * mem * option ((Imp.Imp p).(Imp.cont) (Imp.Imp p).(Imp.ioret)) * list event.
      Definition init (l : varmap) (m : mem) (s:stmt) : state := (l, m, Some (cont_of_stmt s), nil).
      Definition update_log : actname * list mword * mem * list event -> list mword * mem * list event -> Prop
        := fun '(action, argvs, m0, l0) '(retvs, m1, l1) => cons (action, (m0, argvs), (m1, retvs)) l0 = l1.
      Definition step := ContStep.(step) e (list event) update_log.
      Definition steps := ContStep.(steps) e (list event) update_log.
      Goal False. unify steps (TRC.trc step). Abort.
      Let may_have_trace_prefix (s : state) (t : list event) := exists _s, steps s (_s, t).
      Let may_terminate_with_trace (s : state) (t : list event) := exists _s, steps s (_s, None, t).
      Let always_terminates_weak (s : state) := exists N, forall t, may_have_trace_prefix s t -> length t < N.
    End ContTrace.
  End ContTrace.

  Module ContTraceTest.
    Import Imp compiler.Op.

    Local Set Decidable Equality Schemes.
    Inductive varname := a | b | c.
    Local Instance DecidableEq_varname : DecidableEq varname := varname_eq_dec.

    Variant actname := mmap | munmap.
    Local Definition p :=
      RISCVImp.ImpParameters_of_RISCVImpParameters
        {|
          RISCVImp.bw := riscv.util.BitWidth32.BitWidth32;
          RISCVImp.varname := varname;
          RISCVImp.funname := Empty_set;
          RISCVImp.actname := actname;
        |}.
    Let Imp : Imp.ImpInterface p := Imp.Imp p.
    (* RecordImport p (* COQBUG(https://github.com/coq/coq/issues/7808) *) *)
    Local Notation mword := p.(mword).
    Local Notation mword_nonzero := p.(mword_nonzero).
    (* Local Notation varname := p.(varname). (*TODO: shadow*) *)
    Local Notation funname := p.(funname).
    (* Local Notation actname := p.(actname). (*TODO: shadow*) *)
    Local Notation bopname := p.(bopname).
    Local Notation varmap := p.(varmap).
    Local Notation mem := p.(mem).
    Local Notation interp_binop := p.(interp_binop).
    Local Notation load := p.(load).
    Local Notation store := p.(store).
    (* RecordImport Imp (* COQBUG(https://github.com/coq/coq/issues/7808) *) *)
    Local Notation expr := Imp.(expr).
    Local Notation ELit := Imp.(ELit).
    Local Notation EVar := Imp.(EVar).
    Local Notation EOp := Imp.(EOp).
    Local Notation expr_rect := Imp.(expr_rect).
    Local Notation stmt := Imp.(stmt).
    Local Notation SLoad := Imp.(SLoad).
    Local Notation SStore := Imp.(SStore).
    Local Notation SSet := Imp.(SSet).
    Local Notation SIf := Imp.(SIf).
    Local Notation SWhile := Imp.(SWhile).
    Local Notation SSeq := Imp.(SSeq).
    Local Notation SSkip := Imp.(SSkip).
    Local Notation SCall := Imp.(SCall).
    Local Notation SIO := Imp.(SIO).
    Local Notation stmt_rect := Imp.(stmt_rect).
    Local Notation cont := Imp.(cont).
    Local Notation CSuspended := Imp.(CSuspended).
    Local Notation CSeq := Imp.(CSeq).
    Local Notation CStack := Imp.(CStack).
    Local Notation cont_rect := Imp.(cont_rect).
    Local Notation ioact := Imp.(ioact).
    Local Notation ioret := Imp.(ioret).
    Local Notation interp_expr := Imp.(interp_expr).
    Local Notation interp_stmt := Imp.(interp_stmt).
    Local Notation interp_cont := Imp.(interp_cont).

    Definition inbounds : mword -> mword -> mword -> Prop. Admitted.
    
    (* TODO: how to use this? *)
    Definition syscall_spec : ContTrace.event (p:=p) -> Prop :=
      fun '(action, (m0, argvs), (m1, retvs)) =>
        match action with
        | mmap =>
          exists adr len, argvs = [adr; len]
                          /\ retvs = [wzero wXLEN]
                          /\ (forall a, inbounds adr len a -> load a m0 = None)
                          /\ (forall a,
                                 (inbounds adr len a /\ exists v, load a m1 = Some v) \/
                                 (~ inbounds adr len a /\ load a m1 = load a m0))
        | munmap =>
          exists adr len, argvs = [adr; len]
                          /\ retvs = [wzero wXLEN]
                          /\ (forall a, inbounds adr len a -> exists v, load a m0 = Some v)
                          /\ (forall a,
                                 (inbounds adr len a /\ load a m1 = None) \/
                                 (~ inbounds adr len a /\ load a m1 = load a m0))
        end.

    Definition SFail := SWhile (ELit ($1)) SSkip.
    Definition prog :=
      SSeq (SIO [a] mmap [ELit ($0); ELit ($4096)]) (
             SIf (EVar a) (
                   SSeq (SStore (ELit ($1234)) (ELit ($42))) (
                          SSeq (SLoad b (ELit ($1234))) (
                                 SIf (EOp OEq (EVar b) (ELit ($42))) (
                                       (SIO [c] munmap [ELit ($0); ELit ($4096)])
                                     ) (
                                       SFail  )))
                 ) (
                   SFail)).
    Check ContTrace.steps (p:=p) _ _ _.
    Lemma prog_ok e l0 l m c t :
      List.Forall syscall_spec t ->
      ContTrace.steps (p:=p) e (l0, (fun _ => None), prog (l, m, c, t) ->
      c.
    Proof.
      intros. eexists. intros.
      do 5 match goal with
      | _ => progress (cbv [ContTrace.steps ContStep.steps ContTrace.has_trace] in * )
      | _ => progress subst
      | H: exists _, _ |- _ => destruct H
      | H: TRC.trc _ _ _ |- _ => inversion H
      end.
      subst.
      admit.

      eapply TRC.cons.
      { repeat first [ split; [reflexivity|] | exists 99 | eexists ]. }

    Abort.
  End ContTraceTest.

  Module BigStep.
    Section BigStep.
      Context {p : Imp.ImpParameters}.
      Let Imp : Imp.ImpInterface p := Imp.Imp p.
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
      (* RecordImport Imp (* COQBUG(https://github.com/coq/coq/issues/7808) *) *)
      Local Notation expr := Imp.(expr).
      Local Notation ELit := Imp.(ELit).
      Local Notation EVar := Imp.(EVar).
      Local Notation EOp := Imp.(EOp).
      Local Notation expr_rect := Imp.(expr_rect).
      Local Notation stmt := Imp.(stmt).
      Local Notation SLoad := Imp.(SLoad).
      Local Notation SStore := Imp.(SStore).
      Local Notation SSet := Imp.(SSet).
      Local Notation SIf := Imp.(SIf).
      Local Notation SWhile := Imp.(SWhile).
      Local Notation SSeq := Imp.(SSeq).
      Local Notation SSkip := Imp.(SSkip).
      Local Notation SCall := Imp.(SCall).
      Local Notation SIO := Imp.(SIO).
      Local Notation stmt_rect := Imp.(stmt_rect).
      Local Notation cont := Imp.(cont).
      Local Notation CSuspended := Imp.(CSuspended).
      Local Notation CSeq := Imp.(CSeq).
      Local Notation CStack := Imp.(CStack).
      Local Notation cont_rect := Imp.(cont_rect).
      Local Notation ioact := Imp.(ioact).
      Local Notation ioret := Imp.(ioret).
      Local Notation interp_expr := Imp.(interp_expr).
      Local Notation interp_stmt := Imp.(interp_stmt).
      Local Notation interp_cont := Imp.(interp_cont).
      Context
        (e : funname -> option (list varname * list varname * stmt))
        (sys : Type) (external : (actname * list mword * mem * sys) -> (list mword * mem * sys) -> Prop).
      Definition state : Type := varmap * mem * sys.
      Inductive exec : state -> stmt -> state -> Prop :=
      | skip s : exec s SSkip s
      | io binds action args argvs retvs l0 m0 s0 l1 m1 s1
           (_:Common.option_all (List.map (interp_expr l0) args) = Some argvs)
           (_:Common.putmany binds retvs l0 = Some l1)
           (_:external (action, argvs, m0, s0) (retvs, m1, s1))
        : exec (l0, m0, s0) (SIO binds action args) (l1, m1, s1)
      | FIXME_MORE_CASES s : exec s SSkip s.

(* ContStep.steps =  *)
(* fun p : ImpParameters => *)
(* let Imp := Imp.Imp p in *)
(* fun (e : p.(funname) -> option (list p.(varname) * list p.(varname) * Imp.(stmt)))  *)
(*   (sys : Type) *)
(*   (external : p.(actname) * list p.(mword) * p.(mem) * sys -> list p.(mword) * p.(mem) * sys -> Prop) => *)
(* let state := (p.(varmap) * p.(mem) * option (Imp.(cont) Imp.(ioret)) * sys)%type in *)
(* TRC.trc (ContStep.step e sys external) *)
(*      : forall p : ImpParameters, *)
(*        (p.(funname) -> option (list p.(varname) * list p.(varname) * (Imp.Imp p).(stmt))) -> *)
(*        forall sys : Type, *)
(*        (p.(actname) * list p.(mword) * p.(mem) * sys -> list p.(mword) * p.(mem) * sys -> Prop) -> *)
(*        p.(varmap) * p.(mem) * option ((Imp.Imp p).(cont) (Imp.Imp p).(ioret)) * sys -> *)
(*        p.(varmap) * p.(mem) * option ((Imp.Imp p).(cont) (Imp.Imp p).(ioret)) * sys -> Prop *)

(* Argument p is implicit and maximally inserted *)
(* Argument scopes are [_ function_scope type_scope function_scope _ _] *)

      Let contsteps := @ContStep.steps p e sys external.
     (* : varmap * mem * option ((Imp.Imp p).(Imp.cont) (Imp.Imp p).(Imp.ioret)) * sys -> *)
     (*   varmap * mem * option ((Imp.Imp p).(Imp.cont) (Imp.Imp p).(Imp.ioret)) * sys -> Prop *)

      Lemma iff_bigstep_contstep l0 m0 oc0 s0
    End BigStep.
  End BigStep.
End InteractionSemantics.


(* RecordImport.py
record =\
"""
    expr : typeof! (@Imp_.expr p);
    ELit : typeof! (@Imp_.ELit p);
    EVar : typeof! (@Imp_.EVar p);
    EOp : typeof! (@Imp_.EOp p);
    expr_rect : typeof! (@Imp_.expr_rect p);

    stmt : typeof! (@Imp_.stmt p);
    SLoad : typeof! (@Imp_.SLoad p);
    SStore : typeof! (@Imp_.SStore p);
    SSet : typeof! (@Imp_.SSet p);
    SIf : typeof! (@Imp_.SIf p);
    SWhile : typeof! (@Imp_.SWhile p);
    SSeq : typeof! (@Imp_.SSeq p);
    SSkip : typeof! (@Imp_.SSkip p);
    SCall : typeof! (@Imp_.SCall p);
    SIO : typeof! (@Imp_.SIO p);
    stmt_rect : typeof! (@Imp_.stmt_rect p);

    cont : typeof! (@Imp_.cont p);
    CSuspended : typeof! (@Imp_.CSuspended p);
    CSeq : typeof! (@Imp_.CSeq p);
    CStack : typeof! (@Imp_.CStack p);
    cont_rect : typeof! (@Imp_.cont_rect p);

    ioact : typeof! (@Imp_.ioact p);
    ioret : typeof! (@Imp_.ioret p);

    interp_expr : typeof! (@Imp_.interp_expr p);
    interp_stmt : typeof! (@Imp_.interp_stmt p);
    interp_cont : typeof! (@Imp_.interp_cont p);
"""

for field in record.split(';'):
    field = field.strip()
    if not field:
        continue
    if ':' not in field:
        continue
    if ':=' in field:
        continue
    name = field.split(':')[0].strip()
    print ("Local Notation %s := RECORD.(%s)."
            %(name, name))
*)