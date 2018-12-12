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

  Implicit Types post : trace -> mem -> locals -> Prop. (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)

  Fixpoint eval_expr(m: mem)(st: locals)(e: expr): option word :=
    match e with
    | expr.literal v => Some (word.of_Z v)
    | expr.var x => map.get st x
    | expr.load aSize a =>
        'Some a' <- eval_expr m st a | None;
        load aSize m a'
    | expr.op op e1 e2 =>
        'Some v1 <- eval_expr m st e1 | None;
        'Some v2 <- eval_expr m st e2 | None;
        Some (interp_binop op v1 v2)
    end.

  Section WithEnv.
    Context (e: env).

    Inductive exec_cmd:
      cmd ->
      trace -> mem -> locals ->
      (trace -> mem -> locals -> Prop) ->
      Prop :=
    | ExSkip: forall t m l post,
        post t m l ->
        exec_cmd cmd.skip t m l post
    | ExSet: forall t m l x y y' post,
        eval_expr m l y = Some y' ->
        post t m (map.put l x y') ->
        exec_cmd (cmd.set x y) t m l post
    | ExStore: forall t m m' l aSize a addr v val post,
        eval_expr m l a = Some addr ->
        eval_expr m l v = Some val ->
        store aSize m addr val = Some m' ->
        post t m' l ->
        exec_cmd (cmd.store aSize a v) t m l post
    | ExIfThen: forall t m l cond vcond bThen bElse post,
        eval_expr m l cond = Some vcond ->
        vcond <> word.of_Z 0 ->
        exec_cmd bThen t m l post ->
        exec_cmd (cmd.cond cond bThen bElse) t m l post
    | ExIfElse: forall t m l cond bThen bElse post,
        eval_expr m l cond = Some (word.of_Z 0) ->
        exec_cmd bElse t m l post ->
        exec_cmd (cmd.cond cond bThen bElse) t m l post
     | ExSeq: forall t m l s1 s2 mid post,
        exec_cmd s1 t m l mid ->
        (forall t' m' l', mid t' m' l' -> exec_cmd s2 t' m' l' post) ->
        exec_cmd (cmd.seq s1 s2) t m l post
     | ExWhileDone: forall t m l cond body post,
        eval_expr m l cond = Some (word.of_Z 0) ->
        post t m l ->
        exec_cmd (cmd.while cond body) t m l post
     | ExWhileStep : forall t m l cond body v mid post,
        eval_expr m l cond  = Some v ->
        v <> word.of_Z 0 ->
        exec_cmd body t m l mid ->
        (forall t' m' l',
            mid t' m' l' ->
            exec_cmd (cmd.while cond body) t' m' l' post) ->
        exec_cmd (cmd.while cond body) t m l post
     | ExCall: forall t m l binds fname args params rets fbody argvs st0 post outcome,
        map.get e fname = Some (params, rets, fbody) ->
        List.option_all (List.map (eval_expr m l) args) = Some argvs ->
        map.putmany_of_list params argvs map.empty = Some st0 ->
        exec_cmd fbody t m st0 outcome ->
        (forall t' m' st1,
            outcome t' m' st1 ->
            exists retvs l',
              List.option_all (List.map (map.get st1) rets) = Some retvs /\
              map.putmany_of_list binds retvs l = Some l' /\
              post t' m' l') ->
        exec_cmd (cmd.call binds fname args) t m l post
     | ExInteract: forall t m l action argexprs argvals resvars outcome post,
        List.option_all (List.map (eval_expr m l) argexprs) = Some argvals ->
        ext_spec t m action argvals outcome ->
        (forall new_m resvals,
            outcome new_m resvals ->
            exists l', map.putmany_of_list resvars resvals l = Some l' /\
                       post (cons ((m, action, argvals), (new_m, resvals)) t) new_m l') ->
        exec_cmd (cmd.interact resvars action argexprs) t m l post
    .
  End WithEnv.
End semantics.
