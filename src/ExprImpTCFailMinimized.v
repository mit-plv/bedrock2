Require compiler.Common.
Require compiler.Memory.
Require riscv.util.BitWidths.
Require compiler.Op.
Require riscv.util.BitWidth32.

Require Import Coq.Init.Notations.
Module Export AdmitTactic.
Module Import LocalFalse.
Inductive False := .
End LocalFalse.
Axiom proof_admitted : False.
Tactic Notation "admit" := abstract case proof_admitted.
End AdmitTactic.
Require Coq.Init.Notations.

Set Printing Projections.

Ltac typeof x := match type of x with ?T => T end.
Notation "'typeof!' x" := (ltac:(let T := typeof x in exact T)) (at level 10).
Local Notation "'bind_Some' x <- a ; f" :=
  (match a with
   | Some x => f
   | None => None
   end)
    (right associativity, at level 60, x pattern).

Module Export Imp.

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

Module Export Imp_.
  Section Imp_.
    Context {p : ImpParameters}.

    Local Notation mword := p.(mword).
    Local Notation mword_nonzero := p.(mword_nonzero).
    Local Notation varname := p.(varname).
    Local Notation funname := p.(funname).
    Local Notation actname := p.(actname).
    Local Notation bopname := p.(bopname).
    Local Notation varmap := p.(varmap).
    Local Notation mem := p.(mem).
    Local Definition varmap_operations_ : Common.Map _ _ _ := p.(varmap_operations).
Global Existing Instance varmap_operations_.
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
    End cont.
Global Arguments cont : clear implicits.

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
        | 0 => None
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
        | 0 => None
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
  Global Arguments cont : clear implicits.
End Imp_.

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

End Imp.

Module Export RISCVImp.

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
End RISCVImp.

Import compiler.Common.
Import ListNotations.
Import riscv.util.BitWidths.
Import compiler.Op.
Import compiler.Memory.

Module TRC.
  Section TRC.
    Context {T : Type} {R : T -> T -> Type}.
    Inductive trc : T -> T -> Prop :=
    | nil x : trc x x
    | cons x y z (head:R x y) (tail:trc y z) : trc x z.
  End TRC.
  Arguments trc {T} R.
End TRC.
  Import Imp.

  Module Export ContStep.
    Section ContStep.
      Context {p : Imp.ImpParameters}.
      Let Imp : Imp.ImpInterface p := Imp.Imp p.

      Local Notation mword := p.(mword).
      Local Notation varname := p.(varname).
      Local Notation funname := p.(funname).
      Local Notation actname := p.(actname).
      Local Notation varmap := p.(varmap).
      Local Notation mem := p.(mem).
      Local Notation stmt := Imp.(stmt).
      Local Notation cont := Imp.(cont).
      Local Notation ioret := Imp.(ioret).
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

    End ContStep.
  End ContStep.

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

      Local Notation mword := p.(mword).
      Local Notation varname := p.(varname).
      Local Notation funname := p.(funname).
      Local Notation actname := p.(actname).
      Local Notation varmap := p.(varmap).
      Local Notation mem := p.(mem).
      Local Notation stmt := Imp.(stmt).
      Local Notation cont := Imp.(cont).
      Local Notation CSuspended := Imp.(CSuspended).
      Local Notation CSeq := Imp.(CSeq).
      Local Notation ioret := Imp.(ioret).
      Let ContStep := ContStep p.

      Definition cont_of_stmt (s : stmt) : cont ioret := CSeq (CSuspended (nil, nil)) s.

      Definition event : Type := actname * (mem * list mword) * (mem * list mword).
      Context (e : funname -> option (list varname * list varname * stmt)).
      Let state : Type := varmap * mem * option ((Imp.Imp p).(Imp.cont) (Imp.Imp p).(Imp.ioret)) * list event.
      Definition init (l : varmap) (m : mem) (s:stmt) : state := (l, m, Some (cont_of_stmt s), nil).
      Definition update_log : actname * list mword * mem * list event -> list mword * mem * list event -> Prop
        := fun '(action, argvs, m0, l0) '(retvs, m1, l1) => cons (action, (m0, argvs), (m1, retvs)) l0 = l1.
      Definition steps := ContStep.(steps) e (list event) update_log.
    End ContTrace.
  End ContTrace.

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

    Local Notation mword := p.(mword).

    Local Notation funname := p.(funname).
    Local Notation varmap := p.(varmap).
    Local Notation mem := p.(mem).
    Local Notation load := p.(load).
    Local Notation ELit := Imp.(ELit).
    Local Notation EVar := Imp.(EVar).
    Local Notation EOp := Imp.(EOp).
    Local Notation stmt := Imp.(stmt).
    Local Notation SLoad := Imp.(SLoad).
    Local Notation SStore := Imp.(SStore).
    Local Notation SIf := Imp.(SIf).
    Local Notation SWhile := Imp.(SWhile).
    Local Notation SSeq := Imp.(SSeq).
    Local Notation SSkip := Imp.(SSkip).
    Local Notation SIO := Imp.(SIO).

    Definition inbounds : mword -> mword -> mword -> Prop.
Admitted.

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
    Lemma prog_ok e l0 l m c t :
      List.Forall syscall_spec t ->
      ContTrace.steps (p:=p) e (ContTrace.init l0 (Memory.no_mem : mem) prog) (l, m, c, t) ->
      True.
    Lemma prog_ok e l0 l m c t :
      List.Forall syscall_spec t ->
      ContTrace.steps (p:=p) e (ContTrace.init l0 (Memory.no_mem : _) prog) (l, m, c, t) ->
      True.
