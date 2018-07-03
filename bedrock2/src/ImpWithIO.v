Require compiler.Common.

Local Notation "'bind_Some' x <- a ; f" :=
  (match a with
   | Some x => f
   | None => None
   end)
    (right associativity, at level 60, x pattern).

Class ImpParameters :=
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
Global Existing Instance varmap_operations.

Section Imp.
  Goal True. let cls := constr:(ImpParameters) in match constr:(Set) with _ => (let none := constr:(_:cls) in idtac); fail 99 "DUPLICATE INSTANCE" | _ => idtac end. Abort.
  Context {p : ImpParameters}.

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

  Definition cont : Type := list (varmap * list varname * list varname * stmt) * stmt.
  Definition CSkip : cont := (nil, SSkip).
  Definition CSeq (c1:cont) (c2: stmt) : cont := let (stack, c1) := c1 in (stack, SSeq c1 c2).
  Definition CStack (locals: varmap) (cf: cont) (binds rets: list varname) : cont :=
    let '(stack, c1) := cf in (cons (locals, binds, rets, c1) stack, SSkip).

  Definition blocked := list mword -> option (varmap * cont).
  Definition BWait (locals : varmap) (binders : list varname) : blocked :=
    fun values => bind_Some l' <- Common.putmany binders values locals; Some (l', CSkip).
  Definition BSeq (c1 : blocked) (c2 : stmt) :=
    fun values => bind_Some (l, c1) <- c1 values; Some (l, CSeq c1 c2).
  Definition BStack (caller_locals : varmap) (callee : blocked) (binds rets: list varname) : blocked :=
    fun values => bind_Some (callee_locals, c) <- callee values; Some (caller_locals, CStack callee_locals c binds rets).

  Fixpoint interp_expr (st:varmap) (e:expr) : option mword :=
    match e with
    | ELit v => Some v
    | EVar x => Common.get st x
    | EOp op e1 e2 =>
      bind_Some v1 <- interp_expr st e1;
        bind_Some v2 <- interp_expr st e2;
        Some (interp_binop op v1 v2)
    end.

  Definition computation_result : Type := mem * (actname * list mword * blocked + varmap).
  Section WithFunctions.
    Context (lookupFunction : funname -> option (list varname * list varname * stmt)).
    Fixpoint interp_stmt(f: nat)(st: varmap)(m: mem)(s: stmt): option computation_result :=
      match f with
      | 0 => None (* out of fuel *)
      | S f => match s with
        | SLoad x a =>
          bind_Some a <- interp_expr st a;
          bind_Some v <- load a m;
          Some (m, inr (Common.put st x v))
        | SStore a v =>
          bind_Some a <- interp_expr st a;
          bind_Some v <- interp_expr st v;
          bind_Some m <- store a v m;
          Some (m, inr st)
        | SSet x e =>
          bind_Some v <- interp_expr st e;
          Some (m, inr (Common.put st x v))
        | SIf cond bThen bElse =>
          bind_Some v <- interp_expr st cond;
          interp_stmt f st m (if mword_nonzero v then bThen else bElse)
        | SWhile cond body =>
          bind_Some v <- interp_expr st cond;
          if mword_nonzero v
          then
            bind_Some (m, ob) <- interp_stmt f st m body;
            match ob with
            | inl (action, args, b) => Some (m, inl (action, args, BSeq b (SWhile cond body)))
            | inr st => interp_stmt f st m (SWhile cond body)
            end
          else Some (m, inr st)
        | SSeq s1 s2 =>
          bind_Some (m, ob) <- interp_stmt f st m s1;
          match ob with
          | inl (action, args, b) => Some (m, inl (action, args, BSeq b s2))
          | inr st => interp_stmt f st m s2
          end
        | SSkip => Some (m, inr st)
        | SCall binds fname args =>
          bind_Some (params, rets, fbody) <- lookupFunction fname;
            bind_Some argvs <- Common.option_all (List.map (interp_expr st) args);
            bind_Some st0 <- Common.putmany params argvs Common.empty;
            bind_Some (m', ob) <- interp_stmt f st0 m fbody;
            match ob with
            | inl (action, args, b) => Some (m', inl (action, args, BStack st b binds rets))
            | inr st1 => 
              bind_Some retvs <- Common.option_all (List.map (Common.get st1) rets);
              bind_Some st' <- Common.putmany binds retvs st;
              Some (m', inr st')
            end
        | SIO binds ionum args =>
          bind_Some argvs <- Common.option_all (List.map (interp_expr st) args);
          Some (m, inl (ionum, argvs, BWait st binds))
        end
      end.
    Definition exec_stmt st m c r := exists f, interp_stmt f st m c = Some r.
    
    Fixpoint interp_cont(f: nat)(st: varmap)(m: mem)(c: cont): option computation_result :=
      match f with
      | 0 => None (* out of fuel *)
      | S f =>
        match c with
        | (nil, c) => interp_stmt f st m c
        | (cons (stf, binds, rets, cf) stack, c) =>
          bind_Some (m', ob) <- interp_cont f stf m (stack, cf);
          match ob with
          | inl (action, args, b) => Some (m', inl (action, args, BStack st b binds rets))
          | inr st1 => 
            bind_Some retvs <- Common.option_all (List.map (Common.get st1) rets);
            bind_Some st' <- Common.putmany binds retvs st;
            interp_stmt f st' m' c
          end
        end
      end.
    Definition exec_cont st m c r := exists f, interp_cont f st m c = Some r.

    (* If a predicate [P_x : forall b, Prop] identifies the return value of a partial function [f x],
       [arbitraryIfUndefined P_x] identifies the return value of [f x] when [f x] is defined and allows
       arbitrary return values otherwise. *)
    Definition arbitraryIfUndefined {T} (P : T -> Prop) (b:T) := (exists b', P b') -> P b.

    Section WithWorld.
      Context {world : Type} (external_step : world -> mem*actname*list mword -> mem*list mword -> world -> Prop).
      Definition interactive_step (s s' : world * computation_result) : Prop :=
        exists w m action argvs b, s = (w, (m, inl (action, argvs, b))) /\
        exists w' retvs m_, external_step w (m, action, argvs) (m_, retvs) w' /\
        exists st' c', b retvs = Some (st', c') /\
        exists m' R', exec_cont st' m_ c' (m', R') /\ s' = (w', (m', R')).
      Definition done (s : world * computation_result) : Prop :=
        exists w m l, s = (w, (m, inr l)).
      Definition step s s' : Prop := not (done s) /\ arbitraryIfUndefined (interactive_step s) s'.
    End WithWorld.

    Section LabeledTransitionSystem.
      Definition label : Type := (mem*actname*list mword) * (mem*list mword).
      Definition trace := list label.
      Definition lts_external_step w i o w' : Prop := w' = @cons label (i, o) w.
      Definition lts_step := @step trace lts_external_step.
    End LabeledTransitionSystem.
  End WithFunctions.
End Imp.