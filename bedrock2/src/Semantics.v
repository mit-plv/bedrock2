Require Import coqutil.sanity coqutil.Macros.subst coqutil.Macros.unique.
Require Import coqutil.Datatypes.PrimitivePair coqutil.Datatypes.HList.
Require Import coqutil.Decidable.
Require Import bedrock2.Notations bedrock2.Syntax coqutil.Map.Interface.
Require Import BinIntDef coqutil.Word.Interface coqutil.Word.LittleEndian.
Require Import bedrock2.MetricLogging.
Require Export bedrock2.Memory.

Require Import Coq.Lists.List.

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
       the given-away memory, an action label and a list of function call arguments, *)
    trace -> mem -> actname -> list word ->
    (* and a postcondition on the received memory and function call results, *)
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

  Local Notation metrics := MetricLog.

  Section WithMemAndLocals.
    Context (m : mem) (l : locals).
    Fixpoint eval_expr (e : expr) (mc : metrics) : option (word * metrics) :=
      match e with
      | expr.literal v => Some (word.of_Z v, addMetricInstructions 8
                                             (addMetricLoads 8 mc))
      | expr.var x => match map.get l x with
                      | Some v => Some (v, addMetricInstructions 1
                                           (addMetricLoads 2 mc))
                      | None => None
                      end
      | expr.load aSize a =>
          'Some (a', mc') <- eval_expr a mc | None;
          'Some v <- load aSize m a' | None;
          Some (v, addMetricInstructions 1
                   (addMetricLoads 2 mc'))
      | expr.op op e1 e2 =>
          'Some (v1, mc') <- eval_expr e1 mc | None;
          'Some (v2, mc'') <- eval_expr e2 mc' | None;
          Some (interp_binop op v1 v2, addMetricInstructions 2
                                       (addMetricLoads 2 mc''))
      end.

    Fixpoint eval_expr_old (e : expr) : option word :=
      match e with
      | expr.literal v => Some (word.of_Z v)
      | expr.var x => map.get l x
      | expr.load aSize a =>
          'Some a' <- eval_expr_old a | None;
          load aSize m a'
      | expr.op op e1 e2 =>
          'Some v1 <- eval_expr_old e1 | None;
          'Some v2 <- eval_expr_old e2 | None;
          Some (interp_binop op v1 v2)
      end.

    Fixpoint evaluate_call_args_log (arges : list expr) (mc : metrics) :=
      match arges with
      | e :: tl =>
        'Some (v, mc') <- eval_expr e mc | None;
        'Some (args, mc'') <- evaluate_call_args_log tl mc' | None;
        Some (v :: args, mc'')
      | _ => Some (nil, mc)
      end.

  End WithMemAndLocals.
End semantics.

Module exec. Section WithEnv.
  Context {pp : unique! parameters} {e: env}.

  Local Notation metrics := MetricLog.

  Implicit Types post : trace -> mem -> locals -> metrics -> Prop. (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
  Inductive exec :
    cmd -> trace -> mem -> locals -> metrics ->
    (trace -> mem -> locals -> metrics -> Prop) -> Prop :=
  | skip
    t m l mc post
    (_ : post t m l mc)
    : exec cmd.skip t m l mc post
  | set x e
    t m l mc post
    v mc' (_ : eval_expr m l e mc = Some (v, mc'))
    (_ : post t m (map.put l x v) (addMetricInstructions 1
                                  (addMetricLoads 1 mc')))
    : exec (cmd.set x e) t m l mc post
  | unset x
    t m l mc post
    (_ : post t m (map.remove l x) mc)
    : exec (cmd.unset x) t m l mc post
  | store sz ea ev
    t m l mc post
    a mc' (_ : eval_expr m l ea mc = Some (a, mc'))
    v mc'' (_ : eval_expr m l ev mc' = Some (v, mc''))
    m' (_ : store sz m a v = Some m')
    (_ : post t m' l (addMetricInstructions 1
                     (addMetricLoads 1
                     (addMetricStores 1 mc''))))
    : exec (cmd.store sz ea ev) t m l mc post
  | if_true t m l mc e c1 c2 post
    v mc' (_ : eval_expr m l e mc = Some (v, mc'))
    (_ : word.unsigned v <> 0)
    (_ : exec c1 t m l (addMetricInstructions 2
                       (addMetricLoads 2
                       (addMetricJumps 1 mc'))) post)
    : exec (cmd.cond e c1 c2) t m l mc post
  | if_false e c1 c2
    t m l mc post
    v mc' (_ : eval_expr m l e mc = Some (v, mc'))
    (_ : word.unsigned v = 0)
    (_ : exec c2 t m l (addMetricInstructions 2
                       (addMetricLoads 2
                       (addMetricJumps 1 mc'))) post)
    : exec (cmd.cond e c1 c2) t m l mc post
  | seq c1 c2
    t m l mc post
    mid (_ : exec c1 t m l mc mid)
    (_ : forall t' m' l' mc', mid t' m' l' mc' -> exec c2 t' m' l' mc' post)
    : exec (cmd.seq c1 c2) t m l mc post
  | while_false e c
    t m l mc post
    v mc' (_ : eval_expr m l e mc = Some (v, mc'))
    (_ : word.unsigned v = 0)
    (_ : post t m l (addMetricInstructions 1
                    (addMetricLoads 1
                    (addMetricJumps 1 mc'))))
    : exec (cmd.while e c) t m l mc post
  | while_true e c
      t m l mc post
      v mc' (_ : eval_expr m l e mc = Some (v, mc'))
      (_ : word.unsigned v <> 0)
      mid (_ : exec c t m l mc' mid)
      (_ : forall t' m' l' mc'', mid t' m' l' mc'' ->
                                 exec (cmd.while e c) t' m' l' (addMetricInstructions 2
                                                               (addMetricLoads 2
                                                               (addMetricJumps 1 mc''))) post)
    : exec (cmd.while e c) t m l mc post
  | call binds fname arges
      t m l mc post
      params rets fbody (_ : map.get e fname = Some (params, rets, fbody))
      args mc' (_ : evaluate_call_args_log m l arges mc = Some (args, mc'))
      lf (_ : map.putmany_of_list params args map.empty = Some lf)
      mid (_ : exec fbody t m lf mc' mid)
      (_ : forall t' m' st1 mc'', mid t' m' st1 mc'' ->
          exists retvs, map.getmany_of_list st1 rets = Some retvs /\
          exists l', map.putmany_of_list binds retvs l = Some l' /\
          post t' m' l' mc'')
    : exec (cmd.call binds fname arges) t m l mc post
  | interact binds action arges
      t m l mc post
      mKeep mGive (_: map.split m mKeep mGive)
      args mc' (_ :  evaluate_call_args_log m l arges mc = Some (args, mc'))
      mid (_ : ext_spec t mGive action args mid)
      (_ : forall mReceive resvals, mid mReceive resvals ->
          exists l', map.putmany_of_list binds resvals l = Some l' /\
          exists m', map.split m' mKeep mReceive /\
                     post (cons ((mGive, action, args), (mReceive, resvals)) t) m' l'
                       (addMetricInstructions 1
                       (addMetricStores 1
                       (addMetricLoads 2 mc'))))
    : exec (cmd.interact binds action arges) t m l mc post
  .
  End WithEnv.
  Arguments exec {_} _.
End exec. Notation exec := exec.exec.