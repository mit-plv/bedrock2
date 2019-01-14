Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import lib.LibTacticsMin.
Require Import riscv.util.BitWidths.
Require Import riscv.util.ListLib.
Require Import bedrock2.Semantics.
Require Import riscv.Utility.
Require Import riscv.MkMachineWidth.
Require Import coqutil.Macros.unique.
Require Import bedrock2.Memory.
Require compiler.NoActionSyntaxParams.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PropSet.
Require Import bedrock2.Syntax.
Require Import Coq.micromega.Lia.


Inductive bbinop: Type :=
| BEq
| BNe
| BLt
| BGe
| BLtu
| BGeu.

Section Syntax.
  Context {pp : unique! Syntax.parameters}.

  Inductive bcond: Type :=
    | CondBinary (op: bbinop) (x y: varname)
    | CondNez (x: varname)
  .

  Inductive stmt: Type :=
    | SLoad(sz: Syntax.access_size)(x: varname)(a: varname): stmt
    | SStore(sz: Syntax.access_size)(a: varname)(v: varname): stmt
    | SLit(x: varname)(v: Z): stmt
    | SOp(x: varname)(op: bopname)(y z: varname): stmt
    | SSet(x y: varname): stmt
    | SIf(cond: bcond)(bThen bElse: stmt): stmt
    | SLoop(body1: stmt)(cond: bcond)(body2: stmt): stmt
    | SSeq(s1 s2: stmt): stmt
    | SSkip: stmt
    | SCall(binds: list varname)(f: funname)(args: list varname)
    | SInteract(binds: list varname)(a: actname)(args: list varname).

End Syntax.

Module Import FlatImp.
  Class parameters := {
    syntax_params :> Syntax.parameters;

    W :> Words;

    varname_eq_dec  :> DecidableEq varname;
    funcname_eq_dec :> DecidableEq funname;
    actname_eq_dec  :> DecidableEq actname;

    locals :> map.map varname word;
    env :> map.map funname (list varname * list varname * stmt);
    mem :> map.map word byte;

    locals_ok :> map.ok locals;
    env_ok :> map.ok env;
    mem_ok :> map.ok mem;

    trace := list (mem * Syntax.actname * list word * (mem * list word));

    ext_spec: trace -> mem -> Syntax.actname -> list word -> (mem -> list word -> Prop) -> Prop;

    max_ext_call_code_size : actname -> Z;
    max_ext_call_code_size_nonneg: forall a, 0 <= max_ext_call_code_size a;
  }.
End FlatImp.

Local Notation "' x <- a ; f" :=
  (match (a: option _) with
   | x => f
   | _ => None
   end)
  (right associativity, at level 70, x pattern).


Local Open Scope Z_scope.

Section FlatImp1.
  Context {pp : unique! parameters}.

  Section WithEnv.
    Variable (e: env).

    Definition eval_bbinop(st: locals)(op: bbinop)(x y: word): bool :=
      match op with
      | BEq  => reg_eqb x y
      | BNe  => negb (reg_eqb x y)
      | BLt  => signed_less_than x y
      | BGe  => negb (signed_less_than x y)
      | BLtu => ltu x y
      | BGeu => negb (ltu x y)
      end.

    Definition eval_bcond(st: locals)(cond: bcond): option bool :=
      match cond with
      | CondBinary op x y =>
          'Some mx <- map.get st x;
          'Some my <- map.get st y;
          Some (eval_bbinop st op mx my)
      | CondNez x =>
          'Some mx <- map.get st x;
          Some (negb (reg_eqb mx (ZToReg 0)))
      end.

    (* If we want a bigstep evaluation relation, we either need to put
       fuel into the SLoop constructor, or give it as argument to eval *)
    Fixpoint eval_stmt(f: nat)(st: locals)(m: mem)(s: stmt):
      option (locals * mem) :=
      match f with
      | O => None (* out of fuel *)
      | S f => match s with
        | SLoad sz x a =>
            'Some a <- map.get st a;
            'Some v <- load sz m a;
            Some (map.put st x v, m)
        | SStore sz a v =>
            'Some a <- map.get st a;
            'Some v <- map.get st v;
            'Some m <- store sz m a v;
            Some (st, m)
        | SLit x v =>
            Some (map.put st x (ZToReg v), m)
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
          'Some argvs <- option_all (List.map (map.get st) args);
          'Some st0 <- map.putmany_of_list params argvs map.empty;
          'Some (st1, m') <- eval_stmt f st0 m fbody;
          'Some retvs <- option_all (List.map (map.get st1) rets);
          'Some st' <- map.putmany_of_list binds retvs st;
          Some (st', m')
        | SInteract binds fname args =>
          None (* the deterministic semantics do not support external calls *)
        end
      end.

    Definition stmt_size_body(rec: stmt -> Z)(s: stmt): Z :=
        match s with
        | SLoad sz x a => 1
        | SStore sz a v => 1
        | SLit x v => 8
        | SOp x op y z => 2
        | SSet x y => 1
        | SIf cond bThen bElse => 1 + (rec bThen) + (rec bElse)
        | SLoop body1 cond body2 => 1 + (rec body1) + (rec body2)
        | SSeq s1 s2 => 1 + (rec s1) + (rec s2)
        | SSkip => 1
        | SCall binds f args => 1 + (Zlength binds + Zlength args)
        | SInteract binds f args => 1 + (Zlength binds + Zlength args) + max_ext_call_code_size f
        end.

    Fixpoint stmt_size(s: stmt): Z := stmt_size_body stmt_size s.

    Arguments Z.add: simpl never.
    Arguments Z.mul: simpl never.

    Lemma stmt_size_pos: forall s, stmt_size s > 0.
    Proof.
      induction s; simpl; try omega;
        repeat match goal with
               | e: expr |- _ => unique pose proof (expr_size_pos e)
               | l: list _ |- _ => unique pose proof (Zlength_nonneg l)
               end;
        try omega.
      {
        pose proof (max_ext_call_code_size_nonneg a).
        lia.
      }
    Qed.

    Local Ltac inversion_lemma :=
      intros;
      simpl in *;
      repeat (destruct_one_match_hyp; try discriminate);
      repeat match goal with
             | E: negb _ = true       |- _ => apply negb_true_iff in E
             | E: negb _ = false      |- _ => apply negb_false_iff in E
             end;
      inversionss;
      eauto 16.

    Lemma invert_eval_SLoad: forall fuel initialSt initialM sz x y final,
      eval_stmt (S fuel) initialSt initialM (SLoad sz x y) = Some final ->
      exists a v, map.get initialSt y = Some a /\
                  load sz initialM a = Some v /\
                  final = (map.put initialSt x v, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SStore: forall fuel initialSt initialM sz x y final,
      eval_stmt (S fuel) initialSt initialM (SStore sz x y) = Some final ->
      exists a v finalM, map.get initialSt x = Some a /\
                         map.get initialSt y = Some v /\
                         store sz initialM a v = Some finalM /\
                         final = (initialSt, finalM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SLit: forall fuel initialSt initialM x v final,
      eval_stmt (S fuel) initialSt initialM (SLit x v) = Some final ->
      final = (map.put initialSt x (ZToReg v), initialM).
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
        option_all (List.map (map.get st) args) = Some argvs /\
        map.putmany_of_list params argvs map.empty = Some st0 /\
        eval_stmt f st0 m1 fbody = Some (st1, m') /\
        option_all (List.map (map.get st1) rets) = Some retvs /\
        map.putmany_of_list binds retvs st = Some st' /\
        p2 = (st', m').
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SInteract : forall st m1 p2 f binds fname args,
      eval_stmt (S f) st m1 (SInteract binds fname args) = Some p2 ->
      False.
    Proof. inversion_lemma. Qed.

    (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
    Implicit Types post : trace -> mem -> locals -> Prop.

    (* alternative semantics which allow non-determinism *)
    Inductive exec:
      stmt ->
      trace -> mem -> locals ->
      (trace -> mem -> locals -> Prop)
    -> Prop :=
    | ExInteract: forall t m l action argvars argvals resvars outcome post,
        option_all (List.map (map.get l) argvars) = Some argvals ->
        ext_spec t m action argvals outcome ->
        (forall m' resvals,
            outcome m' resvals ->
            exists l', map.putmany_of_list resvars resvals l = Some l' /\
                       post (((m, action, argvals), (m', resvals)) :: t) m' l') ->
        exec (SInteract resvars action argvars) t m l post
    | ExCall: forall t m l binds fname args params rets fbody argvs st0 post outcome,
        map.get e fname = Some (params, rets, fbody) ->
        option_all (List.map (map.get l) args) = Some argvs ->
        map.putmany_of_list params argvs map.empty = Some st0 ->
        exec fbody t m st0 outcome ->
        (forall t' m' st1,
            outcome t' m' st1 ->
            exists retvs l',
              option_all (List.map (map.get st1) rets) = Some retvs /\
              map.putmany_of_list binds retvs l = Some l' /\
              post t' m' l') ->
        exec (SCall binds fname args) t m l post
    | ExLoad: forall t m l sz x a v addr post,
        map.get l a = Some addr ->
        load sz m addr = Some v ->
        post t m (map.put l x v) ->
        exec (SLoad sz x a) t m l post
    | ExStore: forall t m m' l sz a addr v val post,
        map.get l a = Some addr ->
        map.get l v = Some val ->
        store sz m addr val = Some m' ->
        post t m' l ->
        exec (SStore sz a v) t m l post
    | ExLit: forall t m l x v post,
        post t m (map.put l x (ZToReg v)) ->
        exec (SLit x v) t m l post
    | ExOp: forall t m l x op y y' z z' post,
        map.get l y = Some y' ->
        map.get l z = Some z' ->
        post t m (map.put l x (interp_binop op y' z')) ->
        exec (SOp x op y z) t m l post
    | ExSet: forall t m l x y y' post,
        map.get l y = Some y' ->
        post t m (map.put l x y') ->
        exec (SSet x y) t m l post
    | ExIfThen: forall t m l cond  bThen bElse post,
        eval_bcond l cond = Some true ->
        exec bThen t m l post ->
        exec (SIf cond bThen bElse) t m l post
    | ExIfElse: forall t m l cond bThen bElse post,
        eval_bcond l cond = Some false ->
        exec bElse t m l post ->
        exec (SIf cond bThen bElse) t m l post
    | ExLoop: forall t m l cond body1 body2 mid post,
        (* this case is carefully crafted in such a way that recursive uses of exec
         only appear under forall and ->, but not under exists, /\, \/, to make sure the
         auto-generated induction principle contains an IH for both recursive uses *)
        exec body1 t m l mid ->
        (forall t' m' l', mid t' m' l' -> eval_bcond l' cond <> None) ->
        (forall t' m' l',
            mid t' m' l' ->
            eval_bcond l' cond = Some false -> post t' m' l') ->
        (forall t' m' l',
            mid t' m' l' ->
            eval_bcond l' cond = Some true ->
            exec (SSeq body2 (SLoop body1 cond body2)) t' m' l' post) ->
        exec (SLoop body1 cond body2) t m l post
    | ExSeq: forall t m l s1 s2 mid post,
        exec s1 t m l mid ->
        (forall t' m' l', mid t' m' l' -> exec s2 t' m' l' post) ->
        exec (SSeq s1 s2) t m l post
    | ExSkip: forall t m l post,
        post t m l ->
        exec SSkip t m l post.

  End WithEnv.

  (* returns the set of modified vars *)
  Fixpoint modVars(s: stmt): set varname :=
    match s with
    | SLoad sz x y => singleton_set x
    | SStore sz x y => empty_set
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

  Definition accessedVarsBcond(cond: bcond): set varname :=
    match cond with
    | CondBinary _ x y =>
        union (singleton_set x) (singleton_set y)
    | CondNez x =>
        singleton_set x
    end.

  Fixpoint accessedVars(s: stmt): set varname :=
    match s with
    | SLoad sz x y => union (singleton_set x) (singleton_set y)
    | SStore sz x y => union (singleton_set x) (singleton_set y)
    | SLit x v => singleton_set x
    | SOp x op y z => union (singleton_set x) (union (singleton_set y) (singleton_set z))
    | SSet x y => union (singleton_set x) (singleton_set y)
    | SIf cond bThen bElse =>
        union (accessedVarsBcond cond) (union (accessedVars bThen) (accessedVars bElse))
    | SLoop body1 cond body2 =>
        union (accessedVarsBcond cond) (union (accessedVars body1) (accessedVars body2))
    | SSeq s1 s2 =>
        union (accessedVars s1) (accessedVars s2)
    | SSkip => empty_set
    | SCall binds funcname args => union (of_list binds) (of_list args)
    | SInteract binds funcname args => union (of_list binds) (of_list args)
    end.

  Lemma modVars_subset_accessedVars: forall s,
    subset (modVars s) (accessedVars s).
  Proof.
    intro s. induction s; simpl; map_solver locals_ok.
  Qed.
End FlatImp1.


Ltac invert_eval_stmt :=
  lazymatch goal with
  | E: eval_stmt _ (S ?fuel) _ _ ?s = Some _ |- _ =>
    destruct s;
    [ apply invert_eval_SLoad in E
    | apply invert_eval_SStore in E
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
  Context {pp : unique! parameters}.

  Lemma increase_fuel_still_Success: forall fuel1 fuel2 e initialSt initialM s final,
    (fuel1 <= fuel2)%nat ->
    eval_stmt e fuel1 initialSt initialM s = Some final ->
    eval_stmt e fuel2 initialSt initialM s = Some final.
  Proof.
    induction fuel1; introv L Ev.
    - inversions Ev.
    - destruct fuel2; [omega|].
      assert (fuel1 <= fuel2)%nat as F by omega. specialize IHfuel1 with (1 := F).
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
      contradiction.
  Qed.

  Lemma modVarsSound: forall fuel e s initialSt initialM finalSt finalM,
    eval_stmt e fuel initialSt initialM s = Some (finalSt, finalM) ->
    map.only_differ initialSt (modVars s) finalSt.
  Proof.
    induction fuel; introv Ev.
    - discriminate.
    - invert_eval_stmt; simpl in *; inversionss;
      repeat match goal with
      | IH: _, H: _ |- _ =>
          let IH' := fresh IH in pose proof IH as IH';
          specialize IH' with (1 := H);
          simpl in IH';
          ensure_new IH'
      end;
      map_solver locals_ok;
      refine (only_differ_putmany _ _ _ _ _ _); eassumption.
  Qed.

End FlatImp2.
