Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.
Require Import bedrock2.Notations bedrock2.Syntax coqutil.Map.Interface.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.LittleEndian.

Require Coq.Lists.List.

(* TODO: moveme *)
Module List.
  Section WithA.
    Context {A : Type}.
    Fixpoint option_all (xs : list (option A)) {struct xs} : option (list A) :=
      match xs with
      | nil => Some nil
      | cons ox xs =>
        match ox, option_all xs with
        | Some x, Some ys => Some (cons x ys)
        | _ , _ => None
        end
      end.

    Section WithStep.
      Context (step : A -> A).
      Fixpoint unfoldn (n : nat) (start : A) :=
        match n with
        | 0%nat => nil
        | S n => cons start (unfoldn n (step start))
        end.
    End WithStep.
  End WithA.
End List.

Class parameters := {
  syntax :> Syntax.parameters;

  width : Z;
  word :> Word.Interface.word width;
  byte :> Word.Interface.word 8%Z;

  mem :> map.map word byte;
  locals :> map.map varname word;
  env :> map.map funname (list varname * list varname * cmd);

  interp_binop : bopname -> word -> word -> word;
  funname_eqb : funname -> funname -> bool;

  trace := list ((mem * actname * list word) * (mem * list word));

  ExtSpec :=
    (* Given a trace of what happened so far,
       the current memory, an action label and a list of function call arguments, *)
    trace -> mem -> actname -> list word ->
    (* and a postcondition on the new memory and function call results, *)
    (mem -> list word -> Prop) ->
    (* tells if this postcondition will hold *)
    Prop;

  ext_spec: ExtSpec;
}.

Section semantics.
  Context {pp : unique! parameters}.
  Definition bytes_per sz :=
    match sz with
      | access_size.one => 1 | access_size.two => 2 | access_size.four => 4
      | access_size.word => Z.to_nat (Z.div (Z.add width 7) 8)
    end%nat.

  Definition footprint(a: word)(sz: access_size) :=
    List.unfoldn (word.add (word.of_Z 1)) (bytes_per sz) a.
  Definition load(sz: access_size)(m: mem)(a: word): option word :=
    'Some bs <- List.option_all (List.map (map.get m) (footprint a sz)) | None ;
    Some (word.of_Z (LittleEndian.combine _ (tuple.of_list bs))).
  Definition unchecked_store(sz: access_size)(m: mem)(a: word)(v: word) : option mem :=
    map.putmany_of_list
      (footprint a sz)
      (tuple.to_list (LittleEndian.split (bytes_per sz) (word.unsigned v)))
      m.
  Definition store(sz: access_size)(m: mem)(a: word)(v: word): option mem :=
    'Some _ <- load sz m a | None;
    unchecked_store sz m a v.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    Fixpoint eval_expr (e : expr) : option word :=
      match e with
      | expr.literal v => Some (word.of_Z v)
      | expr.var x => map.get l x
      | expr.load aSize a =>
          'Some a' <- eval_expr a | None;
          load aSize m a'
      | expr.op op e1 e2 =>
          'Some v1 <- eval_expr e1 | None;
          'Some v2 <- eval_expr e2 | None;
          Some (interp_binop op v1 v2)
      end.
  End WithMemAndLocals.
End semantics.

Module exec. Section WithEnv.
  Context {pp : unique! parameters} {e: env}.

  Implicit Types post : trace -> mem -> locals -> Prop. (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
  Inductive exec :
    cmd -> trace -> mem -> locals -> (trace -> mem -> locals -> Prop) -> Prop :=
  | skip
    t m l post
    (_ : post t m l)
    : exec cmd.skip t m l post
  | set x e
    t m l post
    v (_ : eval_expr m l e = Some v)
    (_ : post t m (map.put l x v))
    : exec (cmd.set x e) t m l post
  | store sz ea ev
    t m l post
    a (_ : eval_expr m l ea = Some a)
    v (_ : eval_expr m l ev = Some v)
    m' (_ : store sz m a v = Some m')
    (_ : post t m' l)
    : exec (cmd.store sz ea ev) t m l post
  | if_true t m l e c1 c2 post
    v (_ : eval_expr m l e = Some v)
    (_ : v <> word.of_Z 0)
    (_ : exec c1 t m l post)
    : exec (cmd.cond e c1 c2) t m l post
  | if_false e c1 c2
    t m l post
    (_ : eval_expr m l e = Some (word.of_Z 0))
    (_ : exec c2 t m l post)
    : exec (cmd.cond e c1 c2) t m l post
  | seq c1 c2
    t m l post
    mid (_ : exec c1 t m l mid)
    (_ : forall t' m' l', mid t' m' l' -> exec c2 t' m' l' post)
    : exec (cmd.seq c1 c2) t m l post
  | while_false e c
    t m l post
    (_ : eval_expr m l e = Some (word.of_Z 0))
    (_ : post t m l)
    : exec (cmd.while e c) t m l post
  | while_true e c 
      t m l post
      v (_ : eval_expr m l e  = Some v)
      (_ : v <> word.of_Z 0)
      mid (_ : exec c t m l mid)
      (_ : forall t' m' l', mid t' m' l' -> exec (cmd.while e c) t' m' l' post)
    : exec (cmd.while e c) t m l post
  | call binds fname arges
         t m l post
      params rets fbody (_ : map.get e fname = Some (params, rets, fbody))
      args (_ : List.option_all (List.map (eval_expr m l) arges) = Some args)
      lf (_ : map.putmany_of_list params args map.empty = Some lf)
      mid (_ : exec fbody t m lf mid)
      (_ : forall t' m' st1, mid t' m' st1 ->
          exists retvs l',
            List.option_all (List.map (map.get st1) rets) = Some retvs /\
            map.putmany_of_list binds retvs l = Some l' /\
            post t' m' l')
    : exec (cmd.call binds fname arges) t m l post
  | interact binds action arges 
             t m l post
      args (_ : List.option_all (List.map (eval_expr m l) arges) = Some args)
      mid (_ : ext_spec t m action args mid)
      (_ : forall new_m resvals, mid new_m resvals ->
          exists l', map.putmany_of_list binds resvals l = Some l' /\
                     post (cons ((m, action, args), (new_m, resvals)) t) new_m l')
    : exec (cmd.interact binds action arges) t m l post
  .
  End WithEnv.
  Arguments exec {_} _.
End exec. Notation exec := exec.exec.
