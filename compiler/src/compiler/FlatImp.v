Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.MetricLogging.
Require Import coqutil.Macros.unique.
Require Import bedrock2.Memory.
Require Import compiler.util.Common.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Byte.
Require Import bedrock2.Syntax.
Require Import coqutil.Z.Lia.
Require Import coqutil.Tactics.Simp.
Require Import bedrock2.Semantics.
Require Import coqutil.Datatypes.ListSet.
Require Import coqutil.Map.OfListWord.

Require Import coqutil.Word.Interface.
Local Hint Mode Word.Interface.word - : typeclass_instances.

Inductive bbinop: Type :=
| BEq
| BNe
| BLt
| BGe
| BLtu
| BGeu.

Section Syntax.
  Context {varname: Type}.

  Inductive bcond: Type :=
    | CondBinary (op: bbinop) (x y: varname)
    | CondNez (x: varname)
  .

  Inductive stmt: Type :=
    | SLoad(sz: Syntax.access_size)(x: varname)(a: varname)(offset: Z)
    | SStore(sz: Syntax.access_size)(a: varname)(v: varname)(offset: Z)
    | SInlinetable(sz: Syntax.access_size)(x: varname)(t: list Byte.byte)(i: varname)
    | SStackalloc(x : varname)(nbytes: Z)(body: stmt)
    | SLit(x: varname)(v: Z)
    | SOp(x: varname)(op: bopname)(y z: varname)
    | SSet(x y: varname)
    | SIf(cond: bcond)(bThen bElse: stmt)
    | SLoop(body1: stmt)(cond: bcond)(body2: stmt)
    | SSeq(s1 s2: stmt)
    | SSkip
    | SCall(binds: list varname)(f: String.string)(args: list varname)
    | SInteract(binds: list varname)(a: String.string)(args: list varname).

  Definition stmt_size_body(rec: stmt -> Z)(s: stmt): Z :=
    match s with
    | SLoad sz x a o => 1
    | SStore sz a v o => 1
    | SInlinetable sz x t i => 1 + (Z.of_nat (length t) + 3) / 4 + 2
    | SStackalloc x a body => 1 + rec body
    | SLit x v => 8
    | SOp x op y z => 2
    | SSet x y => 1
    | SIf cond bThen bElse => 1 + (rec bThen) + 1 + (rec bElse)
    | SLoop body1 cond body2 => (rec body1) + 1 + (rec body2) + 1
    | SSeq s1 s2 => (rec s1) + (rec s2)
    | SSkip => 0
    (* TODO only works because all registers are callee-saved.
       And we still need to account for the code emitted by compile_function somewhere. *)
    | SCall binds f args => Z.of_nat (List.length args) + 1 + Z.of_nat (List.length binds)
    | SInteract binds f args => 7 (* TODO don't hardcode a magic number *)
    end.

  Fixpoint stmt_size(s: stmt): Z := stmt_size_body stmt_size s.
  Lemma stmt_size_unfold : forall s, stmt_size s = stmt_size_body stmt_size s.
  Proof. destruct s; reflexivity. Qed.

  Arguments Z.add _ _ : simpl never.

  Lemma stmt_size_nonneg: forall s, 0 <= stmt_size s.
  Proof.
    induction s; simpl; try blia.
    assert (0 <= (Z.of_nat (Datatypes.length t) + 3) / 4). {
      apply Z.div_pos; blia.
    }
    blia.
  Qed.

  Fixpoint modVars_as_list(veq: varname -> varname -> bool)(s: stmt): list varname :=
    match s with
    | SSkip | SStore _ _ _ _ => []
    | SStackalloc x n body => list_union veq [x] (modVars_as_list veq body)
    | SLoad _ x _ _ | SLit x _ | SOp x _ _ _ | SSet x _ | SInlinetable _ x _ _ => [x]
    | SIf _ s1 s2 | SLoop s1 _ s2 | SSeq s1 s2 =>
        list_union veq (modVars_as_list veq s1) (modVars_as_list veq s2)
    | SCall binds _ _ | SInteract binds _ _ => list_union veq binds []
    end.

  Definition ForallVars_bcond(P: varname -> Prop)(cond: bcond) : Prop :=
    match cond with
    | CondBinary _ x y => P x /\ P y
    | CondNez x => P x
    end.

  Definition Forall_vars_stmt(P: varname -> Prop)(P_calls: varname -> Prop): stmt -> Prop :=
    fix rec s :=
      match s with
      | SLoad _ x a _ => P x /\ P a
      | SStore _ a x _ => P a /\ P x
      | SInlinetable _ x _ i => P x /\ P i
      | SStackalloc x n body => P x /\ rec body
      | SLit x _ => P x
      | SOp x _ y z => P x /\ P y /\ P z
      | SSet x y => P x /\ P y
      | SIf c s1 s2 => ForallVars_bcond P c /\ rec s1 /\ rec s2
      | SLoop s1 c s2 => ForallVars_bcond P c /\ rec s1 /\ rec s2
      | SSeq s1 s2 => rec s1 /\ rec s2
      | SSkip => True
      | SCall binds _ args => Forall P_calls binds /\ Forall P_calls args
      | SInteract binds _ args => Forall P_calls binds /\ Forall P_calls args
      end.

  Definition ForallVars_stmt P := Forall_vars_stmt P P.

  Lemma ForallVars_bcond_impl: forall (P Q: varname -> Prop),
      (forall x, P x -> Q x) ->
      forall s, ForallVars_bcond P s -> ForallVars_bcond Q s.
  Proof.
    intros. destruct s; simpl in *; intuition eauto.
  Qed.

  Lemma Forall_vars_stmt_impl: forall (P Q P_calls Q_calls: varname -> Prop),
      (forall x, P x -> Q x) ->
      (forall x, P_calls x -> Q_calls x) ->
      forall s, Forall_vars_stmt P P_calls s -> Forall_vars_stmt Q Q_calls s.
  Proof.
    induction s; intros; simpl in *; intuition eauto using ForallVars_bcond_impl, Forall_impl.
  Qed.

  Lemma ForallVars_stmt_impl: forall (P Q: varname -> Prop),
      (forall x, P x -> Q x) ->
      forall s, ForallVars_stmt P s -> ForallVars_stmt Q s.
  Proof. unfold ForallVars_stmt. eauto using Forall_vars_stmt_impl. Qed.

End Syntax.

Arguments bcond: clear implicits.
Arguments stmt: clear implicits.

Local Notation "' x <- a ; f" :=
  (match (a: option _) with
   | x => f
   | _ => None
   end)
  (right associativity, at level 70, x pattern).


Local Open Scope Z_scope.

Class parameters(varname: Type) := {
  varname_eqb: varname -> varname -> bool;
  width : Z;
  word :> Word.Interface.word width;
  mem :> map.map word byte;
  locals :> map.map varname word;
  env :> map.map String.string (list varname * list varname * stmt varname);

  trace := list ((mem * String.string * list word) * (mem * list word));

  ExtSpec :=
    (* Given a trace of what happened so far,
       the given-away memory, an action label and a list of function call arguments, *)
    trace -> mem -> String.string -> list word ->
    (* and a postcondition on the received memory and function call results, *)
    (mem -> list word -> Prop) ->
    (* tells if this postcondition will hold *)
    Prop;

  ext_spec: ExtSpec;
}.

Module ext_spec.
  Class ok(varname: Type){p: parameters varname}: Prop := {
    (* The action name and arguments uniquely determine the footprint of the given-away memory. *)
    unique_mGive_footprint: forall t1 t2 mGive1 mGive2 a args
                                            (post1 post2: mem -> list word -> Prop),
        ext_spec t1 mGive1 a args post1 ->
        ext_spec t2 mGive2 a args post2 ->
        map.same_domain mGive1 mGive2;

    weaken :> forall t mGive act args,
        Morphisms.Proper
          (Morphisms.respectful
             (Morphisms.pointwise_relation Interface.map.rep
               (Morphisms.pointwise_relation (list word) Basics.impl)) Basics.impl)
          (ext_spec t mGive act args);

    intersect: forall t mGive a args
                      (post1 post2: mem -> list word -> Prop),
        ext_spec t mGive a args post1 ->
        ext_spec t mGive a args post2 ->
        ext_spec t mGive a args (fun mReceive resvals =>
                                   post1 mReceive resvals /\ post2 mReceive resvals);
  }.
End ext_spec.
Arguments ext_spec.ok: clear implicits.

Class parameters_ok(varname: Type){p: parameters varname}: Prop := {
  varname_eq_spec :> EqDecider varname_eqb;
  width_cases : width = 32 \/ width = 64;
  word_ok :> word.ok word;
  mem_ok :> map.ok mem;
  locals_ok :> map.ok locals;
  env_ok :> map.ok env;
  ext_spec_ok :> ext_spec.ok _ _;
}.
Arguments parameters_ok: clear implicits.

Section FlatImp1.
  Context {varname: Type}.
  Context {pp : unique! (parameters varname)}.

  Section WithEnv.
    Variable (e: env).

    Definition eval_bbinop(op: bbinop)(x y: word): bool :=
      match op with
      | BEq  => word.eqb x y
      | BNe  => negb (word.eqb x y)
      | BLt  => word.lts x y
      | BGe  => negb (word.lts x y)
      | BLtu => word.ltu x y
      | BGeu => negb (word.ltu x y)
      end.

    Definition eval_bcond(st: locals)(cond: bcond varname): option bool :=
      match cond with
      | CondBinary op x y =>
          'Some mx <- map.get st x;
          'Some my <- map.get st y;
          Some (eval_bbinop op mx my)
      | CondNez x =>
          'Some mx <- map.get st x;
          Some (negb (word.eqb mx (word.of_Z 0)))
      end.

    (* Fixpoint semantics are not currently used *)
    (* If we want a bigstep evaluation relation, we either need to put
       fuel into the SLoop constructor, or give it as argument to eval *)
    Fixpoint eval_stmt(f: nat)(st: locals)(m: mem)(s: stmt varname):
      option (locals * mem) :=
      match f with
      | O => None (* out of fuel *)
      | S f => match s with
        | SLoad sz x a o =>
            'Some a <- map.get st a;
            'Some v <- load sz m (word.add a (word.of_Z o));
            Some (map.put st x v, m)
        | SStore sz a v o =>
            'Some a <- map.get st a;
            'Some v <- map.get st v;
            'Some m <- store sz m (word.add a (word.of_Z o)) v;
            Some (st, m)
        | SInlinetable sz x t i =>
            'Some index <- map.get st i;
            'Some v <- load sz (map.of_list_word t) index;
            Some (map.put st x v, m)
        | SStackalloc x n body =>
          (* the deterministic semantics do not support stack alloc, because at
             this level, we don't have a means of obtaining a stack address *)
           None
        | SLit x v =>
            Some (map.put st x (word.of_Z v), m)
        | SOp x op y z =>
            'Some y <- map.get st y;
            'Some z <- map.get st z;
            Some (map.put st x (interp_binop op y z), m)
        | SSet x y =>
            'Some v <- map.get st y;
            Some (map.put st x v, m)
        | SIf cond bThen bElse =>
            'Some vcond <- (eval_bcond st cond);
             eval_stmt f st m (if vcond then bThen else bElse)
        | SLoop body1 cond body2 =>
            'Some (st, m) <- eval_stmt f st m body1;
            'Some vcond <- eval_bcond st cond;
            if negb vcond then Some (st, m) else
              'Some (st, m) <- eval_stmt f st m body2;
              eval_stmt f st m (SLoop body1 cond body2)
        | SSeq s1 s2 =>
            'Some (st, m) <- eval_stmt f st m s1;
            eval_stmt f st m s2
        | SSkip => Some (st, m)
        | SCall binds fname args =>
          'Some (params, rets, fbody) <- map.get e fname;
          'Some argvs <- map.getmany_of_list st args;
          'Some st0 <- map.putmany_of_list_zip params argvs map.empty;
          'Some (st1, m') <- eval_stmt f st0 m fbody;
          'Some retvs <- map.getmany_of_list st1 rets;
          'Some st' <- map.putmany_of_list_zip binds retvs st;
          Some (st', m')
        | SInteract binds fname args =>
          None (* the deterministic semantics do not support external calls *)
        end
      end.

    Local Ltac inversion_lemma :=
      intros;
      simpl in *;
      repeat (destruct_one_match_hyp; try discriminate);
      repeat match goal with
             | E: negb _ = true       |- _ => apply negb_true_iff in E
             | E: negb _ = false      |- _ => apply negb_false_iff in E
             end;
      simp;
      subst;
      eauto 10.

    Lemma invert_eval_SLoad: forall fuel initialSt initialM sz x y o final,
      eval_stmt (S fuel) initialSt initialM (SLoad sz x y o) = Some final ->
      exists a v, map.get initialSt y = Some a /\
                  load sz initialM (word.add a (word.of_Z o)) = Some v /\
                  final = (map.put initialSt x v, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SStore: forall fuel initialSt initialM sz x y o final,
      eval_stmt (S fuel) initialSt initialM (SStore sz x y o) = Some final ->
      exists a v finalM, map.get initialSt x = Some a /\
                         map.get initialSt y = Some v /\
                         store sz initialM (word.add a (word.of_Z o)) v = Some finalM /\
                         final = (initialSt, finalM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SInlinetable: forall fuel initialSt m sz x i t final,
        eval_stmt (S fuel) initialSt m (SInlinetable sz x t i) = Some final ->
        exists index v, map.get initialSt i = Some index /\
                        load sz (map.of_list_word t) index = Some v /\
                        final = (map.put initialSt x v, m).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SStackalloc : forall st m1 p2 f x n body,
      eval_stmt (S f) st m1 (SStackalloc x n body) = Some p2 ->
      False.
    Proof. inversion_lemma. discriminate. Qed.

    Lemma invert_eval_SLit: forall fuel initialSt initialM x v final,
      eval_stmt (S fuel) initialSt initialM (SLit x v) = Some final ->
      final = (map.put initialSt x (word.of_Z v), initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SOp: forall fuel x y z op initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM (SOp x op y z) = Some final ->
      exists v1 v2,
        map.get initialSt y = Some v1 /\
        map.get initialSt z = Some v2 /\
        final = (map.put initialSt x (Semantics.interp_binop op v1 v2), initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SSet: forall fuel x y initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM (SSet x y) = Some final ->
      exists v,
        map.get initialSt y = Some v /\ final = (map.put initialSt x v, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SIf: forall fuel cond bThen bElse initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM (SIf cond bThen bElse) = Some final ->
      exists vcond,
        eval_bcond initialSt cond = Some vcond /\
        (vcond = true  /\ eval_stmt fuel initialSt initialM bThen = Some final \/
         vcond = false /\ eval_stmt fuel initialSt initialM bElse = Some final).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SLoop: forall fuel st1 m1 body1 cond body2 p4,
      eval_stmt (S fuel) st1 m1 (SLoop body1 cond body2) = Some p4 ->
      (eval_stmt fuel st1 m1 body1 = Some p4 /\ eval_bcond (fst p4) cond = Some false) \/
      exists st2 m2 st3 m3, eval_stmt fuel st1 m1 body1 = Some (st2, m2) /\
                            eval_bcond st2 cond = Some true /\
                            eval_stmt fuel st2 m2 body2 = Some (st3, m3) /\
                            eval_stmt fuel st3 m3 (SLoop body1 cond body2) = Some p4.
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SSeq: forall fuel initialSt initialM s1 s2 final,
      eval_stmt (S fuel) initialSt initialM (SSeq s1 s2) = Some final ->
      exists midSt midM, eval_stmt fuel initialSt initialM s1 = Some (midSt, midM) /\
                         eval_stmt fuel midSt midM s2 = Some final.
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SSkip: forall fuel initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM SSkip = Some final ->
      final = (initialSt, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SCall : forall st m1 p2 f binds fname args,
      eval_stmt (S f) st m1 (SCall binds fname args) = Some p2 ->
      exists params rets fbody argvs st0 st1 m' retvs st',
        map.get e fname = Some (params, rets, fbody) /\
        map.getmany_of_list st args = Some argvs /\
        map.putmany_of_list_zip params argvs map.empty = Some st0 /\
        eval_stmt f st0 m1 fbody = Some (st1, m') /\
        map.getmany_of_list st1 rets = Some retvs /\
        map.putmany_of_list_zip binds retvs st = Some st' /\
        p2 = (st', m').
    Proof. inversion_lemma. eauto 16. Qed.

    Lemma invert_eval_SInteract : forall st m1 p2 f binds fname args,
      eval_stmt (S f) st m1 (SInteract binds fname args) = Some p2 ->
      False.
    Proof. inversion_lemma. discriminate. Qed.

  End WithEnv.

  (* returns the set of modified vars *)
  Fixpoint modVars(s: stmt varname): set varname :=
    match s with
    | SLoad sz x y o => singleton_set x
    | SStore sz x y o => empty_set
    | SInlinetable sz x t i => singleton_set x
    | SStackalloc x n body => union (singleton_set x) (modVars body)
    | SLit x v => singleton_set x
    | SOp x op y z => singleton_set x
    | SSet x y => singleton_set x
    | SIf cond bThen bElse =>
        union (modVars bThen) (modVars bElse)
    | SLoop body1 cond body2 =>
        union (modVars body1) (modVars body2)
    | SSeq s1 s2 =>
        union (modVars s1) (modVars s2)
    | SSkip => empty_set
    | SCall binds funcname args => of_list binds
    | SInteract binds funcname args => of_list binds
    end.

  Definition accessedVarsBcond(cond: bcond varname): set varname :=
    match cond with
    | CondBinary _ x y =>
        union (singleton_set x) (singleton_set y)
    | CondNez x =>
        singleton_set x
    end.
End FlatImp1.


Module exec.
  Section FlatImpExec.
    Context {varname: Type}.
    Context {pp : unique! parameters varname}.
    Context {ok : parameters_ok varname pp}.
    Variable (e: env).

    Local Notation metrics := MetricLog.

    (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
    Implicit Types post : trace -> mem -> locals -> metrics -> Prop.

    (* alternative semantics which allow non-determinism *)
    Inductive exec:
      stmt varname ->
      trace -> mem -> locals -> metrics ->
      (trace -> mem -> locals -> metrics -> Prop)
    -> Prop :=
    | interact: forall t m mKeep mGive l mc action argvars argvals resvars outcome post,
        map.split m mKeep mGive ->
        map.getmany_of_list l argvars = Some argvals ->
        ext_spec t mGive action argvals outcome ->
        (forall mReceive resvals,
            outcome mReceive resvals ->
            exists l', map.putmany_of_list_zip resvars resvals l = Some l' /\
            forall m', map.split m' mKeep mReceive ->
            post (((mGive, action, argvals), (mReceive, resvals)) :: t) m' l'
                 (addMetricInstructions 1
                 (addMetricStores 1
                 (addMetricLoads 2 mc)))) ->
        exec (SInteract resvars action argvars) t m l mc post
    | call: forall t m l mc binds fname args params rets fbody argvs st0 post outcome,
        map.get e fname = Some (params, rets, fbody) ->
        map.getmany_of_list l args = Some argvs ->
        map.putmany_of_list_zip params argvs map.empty = Some st0 ->
        exec fbody t m st0 mc outcome ->
        (forall t' m' mc' st1,
            outcome t' m' st1 mc' ->
            exists retvs l',
              map.getmany_of_list st1 rets = Some retvs /\
              map.putmany_of_list_zip binds retvs l = Some l' /\
              post t' m' l' mc') ->
        exec (SCall binds fname args) t m l mc post
    | load: forall t m l mc sz x a o v addr post,
        map.get l a = Some addr ->
        load sz m (word.add addr (word.of_Z o)) = Some v ->
        post t m (map.put l x v)
             (addMetricLoads 2
             (addMetricInstructions 1 mc)) ->
        exec (SLoad sz x a o) t m l mc post
    | store: forall t m m' mc l sz a o addr v val post,
        map.get l a = Some addr ->
        map.get l v = Some val ->
        store sz m (word.add addr (word.of_Z o)) val = Some m' ->
        post t m' l
             (addMetricLoads 1
             (addMetricInstructions 1
             (addMetricStores 1 mc))) ->
        exec (SStore sz a v o) t m l mc post
    | inlinetable: forall sz x table i v index t m l mc post,
        (* compiled riscv code uses x as a tmp register and this shouldn't overwrite i *)
        x <> i ->
        map.get l i = Some index ->
        load sz (map.of_list_word table) index = Some v ->
        post t m (map.put l x v)
             (addMetricLoads 4
             (addMetricInstructions 3
             (addMetricJumps 1 mc))) ->
        exec (SInlinetable sz x table i) t m l mc post
    | stackalloc: forall t mSmall l mc x n body post,
        n mod (bytes_per_word width) = 0 ->
        (forall a mStack mCombined,
            anybytes a n mStack ->
            map.split mCombined mSmall mStack ->
            exec body t mCombined (map.put l x a) (addMetricLoads 1 (addMetricInstructions 1 mc))
             (fun t' mCombined' l' mc' =>
              exists mSmall' mStack',
                anybytes a n mStack' /\
                map.split mCombined' mSmall' mStack' /\
                post t' mSmall' l' mc')) ->
        exec (SStackalloc x n body) t mSmall l mc post
    | lit: forall t m l mc x v post,
        post t m (map.put l x (word.of_Z v))
             (addMetricLoads 8
             (addMetricInstructions 8 mc)) ->
        exec (SLit x v) t m l mc post
    | op: forall t m l mc x op y y' z z' post,
        map.get l y = Some y' ->
        map.get l z = Some z' ->
        post t m (map.put l x (interp_binop op y' z'))
             (addMetricLoads 2
             (addMetricInstructions 2 mc)) ->
        exec (SOp x op y z) t m l mc post
    | set: forall t m l mc x y y' post,
        map.get l y = Some y' ->
        post t m (map.put l x y')
             (addMetricLoads 1
             (addMetricInstructions 1 mc)) ->
        exec (SSet x y) t m l mc post
    | if_true: forall t m l mc cond  bThen bElse post,
        eval_bcond l cond = Some true ->
        exec bThen t m l
             (addMetricLoads 2
             (addMetricInstructions 2
             (addMetricJumps 1 mc))) post ->
        exec (SIf cond bThen bElse) t m l mc post
    | if_false: forall t m l mc cond bThen bElse post,
        eval_bcond l cond = Some false ->
        exec bElse t m l
             (addMetricLoads 2
             (addMetricInstructions 2
             (addMetricJumps 1 mc))) post ->
        exec (SIf cond bThen bElse) t m l mc post
    | loop: forall t m l mc cond body1 body2 mid1 mid2 post,
        (* This case is carefully crafted in such a way that recursive uses of exec
         only appear under forall and ->, but not under exists, /\, \/, to make sure the
         auto-generated induction principle contains an IH for all recursive uses. *)
        exec body1 t m l mc mid1 ->
        (forall t' m' l' mc',
            mid1 t' m' l' mc' ->
            eval_bcond l' cond <> None) ->
        (forall t' m' l' mc',
            mid1 t' m' l' mc' ->
            eval_bcond l' cond = Some false ->
            post t' m' l'
                 (addMetricLoads 1
                 (addMetricInstructions 1
                 (addMetricJumps 1 mc')))) ->
        (forall t' m' l' mc',
            mid1 t' m' l' mc' ->
            eval_bcond l' cond = Some true ->
            exec body2 t' m' l' mc' mid2) ->
        (forall t'' m'' l'' mc'',
            mid2 t'' m'' l'' mc'' ->
            exec (SLoop body1 cond body2) t'' m'' l''
                 (addMetricLoads 2
                 (addMetricInstructions 2
                 (addMetricJumps 1 mc''))) post) ->
        exec (SLoop body1 cond body2) t m l mc post
    | seq: forall t m l mc s1 s2 mid post,
        exec s1 t m l mc mid ->
        (forall t' m' l' mc', mid t' m' l' mc' -> exec s2 t' m' l' mc' post) ->
        exec (SSeq s1 s2) t m l mc post
    | skip: forall t m l mc post,
        post t m l mc ->
        exec SSkip t m l mc post.

    Lemma det_step: forall t0 m0 l0 mc0 s1 s2 t1 m1 l1 mc1 post,
        exec s1 t0 m0 l0 mc0 (fun t1' m1' l1' mc1' => t1' = t1 /\ m1' = m1 /\ l1' = l1 /\ mc1 = mc1') ->
        exec s2 t1 m1 l1 mc1 post ->
        exec (SSeq s1 s2) t0 m0 l0 mc0 post.
    Proof.
      intros.
      eapply seq; [eassumption|].
      intros. simpl in *. simp.
      assumption.
    Qed.

    Lemma weaken: forall t l m mc s post1,
        exec s t m l mc post1 ->
        forall post2,
          (forall t' m' l' mc', post1 t' m' l' mc' -> post2 t' m' l' mc') ->
          exec s t m l mc post2.
    Proof.
      induction 1; intros; try solve [econstructor; eauto].
      - eapply interact; try eassumption.
        intros; simp.
        edestruct H2; [eassumption|].
        simp. eauto 10.
      - eapply call.
        4: eapply IHexec.
        all: eauto.
        intros. simp.
        specialize H3 with (1 := H5).
        simp. eauto 10.
      - eapply stackalloc. 1: assumption.
        intros.
        eapply H1; eauto.
        intros. simp. eauto 10.
    Qed.

    Ltac equalities :=
      repeat match goal with
             | H1: ?e = ?e1, H2: ?e = ?e2 |- _ =>
               progress (let H := fresh in assert (e1 = e2) as H by congruence; ensure_new H; simp)
             | H1: ?P, H2: ?P |- _ => clear H2
             end;
      simp.

    Lemma intersect: forall t l m mc s post1,
        exec s t m l mc post1 ->
        forall post2,
          exec s t m l mc post2 ->
          exec s t m l mc (fun t' m' l' mc' => post1 t' m' l' mc' /\ post2 t' m' l' mc').
    Proof.
      induction 1; intros;
        match goal with
        | H: exec _ _ _ _ _ _ |- _ => inversion H; subst; clear H
        end;
        equalities;
        try solve [econstructor; eauto | exfalso; congruence].

      - (* SInteract *)
        pose proof ext_spec.unique_mGive_footprint as P.
        specialize P with (1 := H1) (2 := H14).
        destruct (map.split_diff P H H7). subst mKeep0 mGive0.
        eapply @interact.
        + eassumption.
        + eassumption.
        + eapply ext_spec.intersect; [exact H1|exact H14].
        + simpl. intros. simp.
          edestruct H2 as (? & ? & ?); [eassumption|].
          edestruct H15 as (? & ? & ?); [eassumption|].
          simp.
          equalities.
          eauto 10.

      - (* SCall *)
        rename IHexec into IH.
        specialize IH with (1 := H16).
        eapply @call; [..|exact IH|]; eauto.
        rename H3 into Ex1.
        rename H17 into Ex2.
        move Ex1 before Ex2.
        intros. simpl in *. simp.
        edestruct Ex1; [eassumption|].
        edestruct Ex2; [eassumption|].
        simp.
        equalities.
        eauto 10.

      - (* SStackalloc *)
        eapply @stackalloc. 1: eassumption.
        intros.
        rename H0 into Ex1, H12 into Ex2.
        eapply weaken. 1: eapply H1. 1,2: eassumption.
        1: eapply Ex2. 1,2: eassumption.
        cbv beta. clear -ok.
        intros. simp.
        lazymatch goal with
          | A: map.split _ _ _, B: map.split _ _ _ |- _ =>
            specialize @map.split_diff with (4 := A) (5 := B) as P
        end.
        edestruct P; try typeclasses eauto. 2: subst; eauto 10.
        eapply anybytes_unique_domain; eassumption.

      - (* SLoop *)
        eapply @loop.
        + eapply IHexec. exact H10.
        + simpl. intros. simp. eauto.
        + simpl. intros. simp. eauto.
        + simpl. intros. simp. eapply H3; [eassumption..|]. (* also an IH *)
          eapply H18; eassumption.
        + simpl. intros. simp. eapply H5; [eassumption..|]. (* also an IH *)
          eapply H19; eassumption.

      - (* SSeq *)
        pose proof IHexec as IH1.
        specialize IH1 with (1 := H5).
        eapply @seq; [exact IH1|].
        intros; simpl in *.
        destruct H2.
        eauto.
    Qed.

  End FlatImpExec.
End exec.
Notation exec := exec.exec.

Ltac invert_eval_stmt :=
  lazymatch goal with
  | E: eval_stmt _ (S ?fuel) _ _ ?s = Some _ |- _ =>
    destruct s;
    [ apply invert_eval_SLoad in E
    | apply invert_eval_SStore in E
    | apply invert_eval_SInlinetable in E
    | apply invert_eval_SStackalloc in E
    | apply invert_eval_SLit in E
    | apply invert_eval_SOp in E
    | apply invert_eval_SSet in E
    | apply invert_eval_SIf in E
    | apply invert_eval_SLoop in E
    | apply invert_eval_SSeq in E
    | apply invert_eval_SSkip in E
    | apply invert_eval_SCall in E
    | apply invert_eval_SInteract in E ];
    deep_destruct E;
    [ let x := fresh "Case_SLoad" in pose proof tt as x; move x at top
    | let x := fresh "Case_SStore" in pose proof tt as x; move x at top
    | let x := fresh "Case_SInlinetable" in pose proof tt as x; move x at top
    | let x := fresh "Case_SStackalloc" in pose proof tt as x; move x at top
    | let x := fresh "Case_SLit" in pose proof tt as x; move x at top
    | let x := fresh "Case_SOp" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSet" in pose proof tt as x; move x at top
    | let x := fresh "Case_SIf_Then" in pose proof tt as x; move x at top
    | let x := fresh "Case_SIf_Else" in pose proof tt as x; move x at top
    | let x := fresh "Case_SLoop_Done" in pose proof tt as x; move x at top
    | let x := fresh "Case_SLoop_NotDone" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSeq" in pose proof tt as x; move x at top
    | let x := fresh "Case_SSkip" in pose proof tt as x; move x at top
    | let x := fresh "Case_SCall" in pose proof tt as x; move x at top
    | let x := fresh "Case_SInteract" in pose proof tt as x; move x at top ]
  end.


Section FlatImp2.
  Context (varname: Type).
  Context {pp : unique! parameters varname}.
  Context {ok : parameters_ok varname pp}.

  Definition SimState: Type := trace * mem * locals * MetricLog.
  Definition SimExec(e: env)(c: stmt varname): SimState -> (SimState -> Prop) -> Prop :=
    fun '(t, m, l, mc) post =>
      exec e c t m l mc (fun t' m' l' mc' => post (t', m', l', mc')).

  Lemma increase_fuel_still_Success: forall fuel1 fuel2 e initialSt initialM s final,
    (fuel1 <= fuel2)%nat ->
    eval_stmt e fuel1 initialSt initialM s = Some final ->
    eval_stmt e fuel2 initialSt initialM s = Some final.
  Proof.
    induction fuel1; intros *; intros L Ev.
    - inversion Ev.
    - destruct fuel2; [blia|].
      assert (fuel1 <= fuel2)%nat as F by blia. specialize IHfuel1 with (1 := F).
      destruct final as [finalSt finalM].
      invert_eval_stmt; cbn in *;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          ensure_new IH'
      end;
      repeat match goal with
      | H: _ = Some _ |- _ => rewrite H
      end;
      try congruence;
      try simpl_if;
      rewrite? (proj2 (reg_eqb_true _ _) eq_refl);
      repeat match goal with
      | H : _ = true  |- _ => rewrite H
      | H : _ = false |- _ => rewrite H
      end;
      eauto.
      all: contradiction.
  Qed.

  Lemma modVarsSound_fixpoint: forall fuel e s initialSt initialM finalSt finalM,
    eval_stmt e fuel initialSt initialM s = Some (finalSt, finalM) ->
    map.only_differ initialSt (modVars s) finalSt.
  Proof.
    induction fuel; intros *; intro Ev.
    - discriminate.
    - invert_eval_stmt; simpl in *; simp; subst;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          simpl in IH';
          ensure_new IH'
      end;
      try solve [map_solver locals_ok |refine (map.only_differ_putmany _ _ _ _ _); eassumption].
  Qed.

  Lemma modVarsSound: forall e s initialT (initialSt: locals) initialM (initialMc: MetricLog) post,
      exec e s initialT initialM initialSt initialMc post ->
      exec e s initialT initialM initialSt initialMc
           (fun finalT finalM finalSt _ => map.only_differ initialSt (modVars s) finalSt).
  Proof.
    induction 1;
      try solve [ econstructor; [eassumption..|simpl; map_solver locals_ok] ].
    - eapply exec.interact; try eassumption.
      intros; simp.
      edestruct H2; try eassumption. simp.
      eexists; split; [eassumption|].
      simpl. try split; eauto.
      intros.
      eapply map.only_differ_putmany. eassumption.
    - eapply exec.call. 4: exact H2. (* don't pick IHexec! *) all: try eassumption.
      intros; simpl in *; simp.
      edestruct H3; try eassumption. simp.
      do 2 eexists; split; [|split]; try eassumption.
      eapply map.only_differ_putmany. eassumption.
    - eapply exec.stackalloc; try eassumption.
      intros.
      eapply exec.weaken.
      + eapply exec.intersect.
        * eapply H0; eassumption.
        * eapply H1; eassumption.
      + simpl. intros. simp.
        do 2 eexists. split; [eassumption|]. split; [eassumption|]. map_solver locals_ok.
    - eapply exec.if_true; try eassumption.
      eapply exec.weaken; [eassumption|].
      simpl; intros. map_solver locals_ok.
    - eapply exec.if_false; try eassumption.
      eapply exec.weaken; [eassumption|].
      simpl; intros. map_solver locals_ok.
    - eapply exec.loop with
          (mid3 := fun t' m' l' mc' => mid1 t' m' l' mc' /\
                                   map.only_differ l (modVars body1) l')
          (mid4 := fun t' m' l' mc' => mid2 t' m' l' mc' /\
                                   map.only_differ l (modVars (SLoop body1 cond body2)) l').
      + eapply exec.intersect; eassumption.
      + intros. simp. eauto.
      + intros. simp. simpl. map_solver locals_ok.
      + intros. simp. simpl in *.
        eapply exec.intersect; [eauto|].
        eapply exec.weaken.
        * eapply H3; eassumption.
        * simpl. intros. map_solver locals_ok.
      + intros. simp. simpl in *.
        eapply exec.weaken.
        * eapply H5; eassumption.
        * simpl. intros. map_solver locals_ok.
    - eapply exec.seq with
          (mid0 := fun t' m' l' mc' => mid t' m' l' mc' /\ map.only_differ l (modVars s1) l').
      + eapply exec.intersect; eassumption.
      + simpl; intros. simp.
        eapply exec.weaken; [eapply H1; eauto|].
        simpl; intros.
        map_solver locals_ok.
  Qed.

End FlatImp2.

(* used to work at adfc32e107439abcda2d99052f74e9ae891e95bf

Module Import FlatImpSemanticsEquiv.
  Class parameters := {
    noActionParams :> NoActionSyntaxParams.parameters;

    varname_eq_dec :> DecidableEq varname;
    funcname_eq_dec:> DecidableEq varname;
  }.

  Instance to_FlatImp_params(p: parameters): FlatImp.parameters := {|
    FlatImp.ext_spec _ _ _ _ _ := False;
  |}.

End FlatImpSemanticsEquiv.

Section FlatImp3.

  Context {pp : unique! FlatImpSemanticsEquiv.parameters}.

  Hint Constructors exec.

  Ltac prove_exec :=
    let useOnce := fresh "useOnce_name" in
    pose proof @ExLoop as useOnce;
    repeat match goal with
           | |- _ => progress destruct_pair_eqs
           | H: _ /\ _ |- _ => destruct H
           | |- _ => progress (simpl in *; subst)
           | |- _ => progress eauto 10
           | |- _ => congruence
           | |- _ => contradiction
           | |- _ => progress rewrite_match
           | |- _ => rewrite reg_eqb_ne by congruence
           | |- _ => rewrite reg_eqb_eq by congruence
           | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
             replace v2 with v1 in * by congruence;
             clear H2
           (* | |- _ => eapply @ExInteract  not possible because varname=Empty_set *)
           | |- _ => eapply @ExCall
           | |- _ => eapply @ExLoad
           | |- _ => eapply @ExStore
           | |- _ => eapply @ExLit
           | |- _ => eapply @ExOp
           | |- _ => eapply @ExSet
           | |- _ => solve [eapply @ExIfThen; eauto]
           | |- _ => solve [eapply @ExIfElse; eauto]
           (* | |- _ => eapply @ExLoop    could loop infinitely     *)
           | |- _ => eapply useOnce; clear useOnce
           | |- _ => eapply @ExSeq
           | |- _ => eapply @ExSkip
           | |- _ => progress intros
           end;
    try clear useOnce.

  Lemma fixpoint_to_inductive_semantics: forall env fuel l m s l' m',
      eval_stmt env fuel l m s = Some (l', m') ->
      exec env s nil m l (fun t'' m'' l'' => t'' = nil /\ m'' = m' /\ l'' = l').
  Proof.
    induction fuel; intros; [ simpl in *; discriminate | invert_eval_stmt ]; prove_exec.
  Qed.

  Lemma inductive_to_fixpoint_semantics_aux: forall env t l m s post,
      exec env s t m l post ->
      t = nil ->
      exec env s t m l (fun t' m' l' =>
        t' = nil /\
        post t' m' l' /\ (* <-- this one is just to get the induction work, maybe a
                            better induction principle could do that for us? *)
        exists fuel, eval_stmt env fuel l m s = Some (l', m')).
  Proof.
    induction 1; intros; subst;
      try destruct action;
      try specialize (IHexec eq_refl);
      try solve [prove_exec;
                 repeat split; eauto;
                 prove_exec;
                 exists 1%nat; simpl; rewrite_match; reflexivity].
    - eapply @ExCall.
      4: eapply IHexec.
      all: eauto.
      intros; simpl in *; destruct_products; subst.
      specialize H3 with (1 := H4rl).
      destruct_products.
      do 2 eexists; repeat split; eauto.
      exists (S fuel); simpl.
      rewrite_match.
      reflexivity.
    - eapply @ExIfThen; eauto. eapply weaken_exec; [exact IHexec|].
      intros; simpl in *; destruct_products; subst.
      repeat split; eauto.
      exists (S fuel). simpl. prove_exec.
    - eapply @ExIfElse; eauto. eapply weaken_exec; [exact IHexec|].
      intros; simpl in *; destruct_products; subst.
      repeat split; eauto.
      exists (S fuel). simpl. prove_exec.
    - eapply @ExLoop; eauto; intros; simpl in *; destruct_products; subst;
        repeat split; eauto.
      + intros. exists (S fuel); prove_exec.
      + eapply weaken_exec; [eapply H3|]; eauto.
        intros; simpl in *; destruct_products; subst;
          repeat split; eauto.
        destruct fuel0; simpl in *; [discriminate|].
        destruct_one_match_hyp; [|discriminate].
        exists (S (fuel + fuel0)). simpl.
        fuel_increasing_rewrite.
        rewrite_match.
        rewrite reg_eqb_ne by congruence.
        fuel_increasing_rewrite.
        destruct p.
        fuel_increasing_rewrite.
        reflexivity.
    - eapply @ExSeq; [exact IHexec | ].
      intros; simpl in *; destruct_products. subst.
      specialize H1 with (1 := H2rl) (2 := eq_refl).
      eapply weaken_exec; [exact H1|].
      intros; simpl in *; destruct_products. subst.
      repeat split; eauto.
      exists (S (fuel + fuel0)).
      simpl in *.
      do 2 fuel_increasing_rewrite. reflexivity.
  Qed.

  (* note: only holds if there are no external calls with an empty result set
     (not the same as "no result set"/failure),
     which we ensure here by banning external calls altogether *)
  Lemma exists_state_satisfying_post: forall env t l m s post,
      exec env s t m l post ->
      exists t' m' l', post t' m' l'.
  Proof.
    induction 1;
      try destruct action;
      destruct_products;
      eauto.
    - edestruct H3; eauto. destruct_products. eauto.
    - repeat match goal with
             | H: _ |- _ => specialize H with (1 := IHexec)
             end.
      destruct (get l' cond) as [vcond|] eqn: E; [|contradiction].
      simpl in *.
      destruct (reg_eqb vcond (ZToReg 0)) eqn: F;
        [ apply reg_eqb_true in F; subst | apply reg_eqb_false in F ];
        eauto.
  Qed.

  Lemma inductive_to_fixpoint_semantics: forall env t l m s post,
      exec env s t m l post ->
      t = nil ->
      exists fuel m' l', eval_stmt env fuel l m s = Some (l', m').
  Proof.
    intros.
    pose proof inductive_to_fixpoint_semantics_aux as P.
    specialize P with (1 := H) (2 := H0).
    subst.
    apply exists_state_satisfying_post in P.
    destruct_products.
    subst.
    eauto.
  Qed.

End FlatImp3.
*)

(*Goal True. idtac "End of FlatImp.v". Abort.*)
