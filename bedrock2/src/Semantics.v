Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.
Require Import coqutil.Decidable.
Require Import bedrock2.Notations bedrock2.Syntax coqutil.Map.Interface.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.LittleEndian.
Require Export bedrock2.Memory.

Require Coq.Lists.List.

Class parameters := {
  syntax :> Syntax.parameters;

  width : Z;
  word :> Word.Interface.word width;
  byte :> Word.Interface.word 8%Z;

  mem :> map.map word byte;
  locals :> map.map varname word;
  funname_env : forall T: Type, map.map funname T; (* abstract T for better reusability *)

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

Module ext_spec.
  Class ok{p: parameters} := {
    (* The action name and arguments uniquely determine the footprint of the given-away memory. *)
    unique_mGive_footprint: forall t1 t2 mGive1 mGive2 a args
                                            (post1 post2: mem -> list word -> Prop),
        ext_spec t1 mGive1 a args post1 ->
        ext_spec t2 mGive2 a args post2 ->
        map.same_domain mGive1 mGive2;

    (* This one is less useful because it doesn't allow for "built-in weakining" in
       ext_specs: Each ext_spec has to require that its post is tight,
       i.e. it not only has to require
       "forall mReceive resvals, possible mReceive resvals -> post my_mReceive my_resvals"
       but also the opposite direction, which is cumbersome.

       The trace of events which happened so far & the given-away memory & the action name &
       the arguments uniquely determine the set of possible outcomes of the external call.
       That is, the external call CAN be non-deterministic, but ext_spec must return the
       tightest possible set of outcomes.
    unique_post: forall t mGive a args (post1 post2: mem -> list word -> Prop),
        ext_spec t mGive a args post1 ->
        ext_spec t mGive a args post2 ->
        forall mReceive resvals, post1 mReceive resvals <-> post2 mReceive resvals;
    *)

    (* Should hold, but not needed at the moment
    weaken: forall t mGive a args (post1 post2: mem -> list word -> Prop),
        ext_spec t mGive a args post1 ->
        (forall mReceive resvals, post1 mReceive resvals -> post2 mReceive resvals) ->
        ext_spec t mGive a args post2;
     *)

    intersect: forall t mGive a args
                      (post1 post2: mem -> list word -> Prop),
        ext_spec t mGive a args post1 ->
        ext_spec t mGive a args post2 ->
        ext_spec t mGive a args (fun mReceive resvals =>
                                   post1 mReceive resvals /\ post2 mReceive resvals);
  }.
End ext_spec.
Arguments ext_spec.ok: clear implicits.

Class parameters_ok{p: parameters} := {
  varname_eq_dec :> DecidableEq varname;
  funname_eq_dec :> DecidableEq funname;
  actname_eq_dec :> DecidableEq actname;
  width_cases : width = 32 \/ width = 64;
  word_ok :> word.ok word;
  byte_ok :> word.ok byte;
  mem_ok :> map.ok mem;
  locals_ok :> map.ok locals;
  funname_env_ok : forall T: Type, map.ok (funname_env T);
  ext_spec_ok :> ext_spec.ok p;
}.
Arguments parameters_ok: clear implicits.

Instance env{p: parameters}: map.map funname (list varname * list varname * cmd) :=
  funname_env _.

Section binops.
  Context {width : Z} {word : Word.Interface.word width}.
  Definition interp_binop (bop : bopname) : word -> word -> word :=
    match bop with
    | bopname.add => word.add
    | bopname.sub => word.sub
    | bopname.mul => word.mul
    | bopname.mulhuu => word.mulhuu
    | bopname.divu => word.divu
    | bopname.remu => word.modu
    | bopname.and => word.and
    | bopname.or => word.or
    | bopname.xor => word.xor
    | bopname.sru => word.sru
    | bopname.slu => word.slu
    | bopname.srs => word.srs
    | bopname.lts => fun a b =>
      if word.lts a b then word.of_Z 1 else word.of_Z 0
    | bopname.ltu => fun a b =>
      if word.ltu a b then word.of_Z 1 else word.of_Z 0
    | bopname.eq => fun a b =>
      if word.eqb a b then word.of_Z 1 else word.of_Z 0
    end.
End binops.

Section semantics.
  Context {pp : unique! parameters}.

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
  | unset x
    t m l post
    (_ : post t m (map.remove l x))
    : exec (cmd.unset x) t m l post
  | store sz ea ev
    t m l post
    a (_ : eval_expr m l ea = Some a)
    v (_ : eval_expr m l ev = Some v)
    m' (_ : store sz m a v = Some m')
    (_ : post t m' l)
    : exec (cmd.store sz ea ev) t m l post
  | if_true t m l e c1 c2 post
    v (_ : eval_expr m l e = Some v)
    (_ : word.unsigned v <> 0)
    (_ : exec c1 t m l post)
    : exec (cmd.cond e c1 c2) t m l post
  | if_false e c1 c2
    t m l post
    v (_ : eval_expr m l e = Some v)
    (_ : word.unsigned v = 0)
    (_ : exec c2 t m l post)
    : exec (cmd.cond e c1 c2) t m l post
  | seq c1 c2
    t m l post
    mid (_ : exec c1 t m l mid)
    (_ : forall t' m' l', mid t' m' l' -> exec c2 t' m' l' post)
    : exec (cmd.seq c1 c2) t m l post
  | while_false e c
    t m l post
    v (_ : eval_expr m l e  = Some v)
    (_ : word.unsigned v = 0)
    (_ : post t m l)
    : exec (cmd.while e c) t m l post
  | while_true e c
      t m l post
      v (_ : eval_expr m l e  = Some v)
      (_ : word.unsigned v <> 0)
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
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list binds retvs l = Some l' /\
          post t' m' l')
    : exec (cmd.call binds fname arges) t m l post
  | interact binds action arges
             t m l post
      mKeep mGive (_: map.split m mKeep mGive)
      args (_ : List.option_all (List.map (eval_expr m l) arges) = Some args)
      mid (_ : ext_spec t mGive action args mid)
      (_ : forall mReceive resvals, mid mReceive resvals ->
          exists l', map.putmany_of_list binds resvals l = Some l' /\
          exists m', map.split m' mKeep mReceive /\
          post (cons ((mGive, action, args), (mReceive, resvals)) t) m' l')
    : exec (cmd.interact binds action arges) t m l post
  .
  End WithEnv.
  Arguments exec {_} _.
End exec. Notation exec := exec.exec.
