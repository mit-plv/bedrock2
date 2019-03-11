Require Import Coq.Bool.Bool.
Require Import Coq.ZArith.ZArith.
Require Import lib.LibTacticsMin.
Require Import riscv.Utility.ListLib.
Require Import coqutil.Macros.unique.
Require Import bedrock2.Memory.
Require compiler.NoActionSyntaxParams.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import coqutil.Decidable.
Require Import coqutil.Datatypes.PropSet.
Require Import bedrock2.Syntax.
Require Import Coq.micromega.Lia.
Require Import compiler.Simp.
Require Import bedrock2.Semantics.

Local Set Ltac Profiling.

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


Module Import FlatImpSize.
  Class parameters := {
    bopname_params :> Syntax.parameters;
    max_ext_call_code_size: actname -> Z;
    max_ext_call_code_size_nonneg: forall a, 0 <= max_ext_call_code_size a;
  }.
End FlatImpSize.

Section FlatImpSize1.

  Context {p: unique! FlatImpSize.parameters}.

  Definition stmt_size_body(rec: stmt -> Z)(s: stmt): Z :=
    match s with
    | SLoad sz x a => 1
    | SStore sz a v => 1
    | SLit x v => 15
    | SOp x op y z => 2
    | SSet x y => 1
    | SIf cond bThen bElse => 1 + (rec bThen) + 1 + (rec bElse)
    | SLoop body1 cond body2 => (rec body1) + 1 + (rec body2) + 1
    | SSeq s1 s2 => (rec s1) + (rec s2)
    | SSkip => 0
    | SCall binds f args => 1000 (* TODO not sure how much register saving will cost etc *)
    | SInteract binds f args => max_ext_call_code_size f
    end.

  Fixpoint stmt_size(s: stmt): Z := stmt_size_body stmt_size s.
  Lemma stmt_size_unfold : forall s, stmt_size s = stmt_size_body stmt_size s.
  Proof. destruct s; reflexivity. Qed.

  Arguments Z.add _ _ : simpl never.

  Lemma stmt_size_nonneg: forall s, 0 <= stmt_size s.
  Proof.
    induction s; simpl; try omega.
    apply max_ext_call_code_size_nonneg.
  Qed.

End FlatImpSize1.

Local Notation "' x <- a ; f" :=
  (match (a: option _) with
   | x => f
   | _ => None
   end)
  (right associativity, at level 70, x pattern).


Local Open Scope Z_scope.

(* shadows Semantics.env, which maps funnames to cmd (non-flattened) with a new instance
   which maps funnames to stmt (flattened) *)
Instance env{p: Semantics.parameters}: map.map funname (list varname * list varname * stmt) :=
  funname_env _.

Section FlatImp1.
  Context {pp : unique! Semantics.parameters}.

  Section WithEnv.
    Variable (e: env).

    Definition eval_bbinop(st: locals)(op: bbinop)(x y: word): bool :=
      match op with
      | BEq  => word.eqb x y
      | BNe  => negb (word.eqb x y)
      | BLt  => word.lts x y
      | BGe  => negb (word.lts x y)
      | BLtu => word.ltu x y
      | BGeu => negb (word.ltu x y)
      end.

    Definition eval_bcond(st: locals)(cond: bcond): option bool :=
      match cond with
      | CondBinary op x y =>
          'Some mx <- map.get st x;
          'Some my <- map.get st y;
          Some (eval_bbinop st op mx my)
      | CondNez x =>
          'Some mx <- map.get st x;
          Some (negb (word.eqb mx (word.of_Z 0)))
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
          'Some argvs <- List.option_all (List.map (map.get st) args);
          'Some st0 <- map.putmany_of_list params argvs map.empty;
          'Some (st1, m') <- eval_stmt f st0 m fbody;
          'Some retvs <- List.option_all (List.map (map.get st1) rets);
          'Some st' <- map.putmany_of_list binds retvs st;
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
        List.option_all (List.map (map.get st) args) = Some argvs /\
        map.putmany_of_list params argvs map.empty = Some st0 /\
        eval_stmt f st0 m1 fbody = Some (st1, m') /\
        List.option_all (List.map (map.get st1) rets) = Some retvs /\
        map.putmany_of_list binds retvs st = Some st' /\
        p2 = (st', m').
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SInteract : forall st m1 p2 f binds fname args,
      eval_stmt (S f) st m1 (SInteract binds fname args) = Some p2 ->
      False.
    Proof. inversion_lemma. Qed.

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
End FlatImp1.


Module exec.
  Section FlatImpExec.
    Context {pp : unique! Semantics.parameters}.
    Variable (e: env).

    (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
    Implicit Types post : trace -> mem -> locals -> Prop.

    (* alternative semantics which allow non-determinism *)
    Inductive exec:
      stmt ->
      trace -> mem -> locals ->
      (trace -> mem -> locals -> Prop)
    -> Prop :=
    | interact: forall t m l action argvars argvals resvars outcome post,
        List.option_all (List.map (map.get l) argvars) = Some argvals ->
        ext_spec t m action argvals outcome ->
        (forall m' resvals,
            outcome m' resvals ->
            exists l', map.putmany_of_list resvars resvals l = Some l' /\
                       post (((m, action, argvals), (m', resvals)) :: t) m' l') ->
        exec (SInteract resvars action argvars) t m l post
    | call: forall t m l binds fname args params rets fbody argvs st0 post outcome,
        map.get e fname = Some (params, rets, fbody) ->
        List.option_all (List.map (map.get l) args) = Some argvs ->
        map.putmany_of_list params argvs map.empty = Some st0 ->
        exec fbody t m st0 outcome ->
        (forall t' m' st1,
            outcome t' m' st1 ->
            exists retvs l',
              List.option_all (List.map (map.get st1) rets) = Some retvs /\
              map.putmany_of_list binds retvs l = Some l' /\
              post t' m' l') ->
        exec (SCall binds fname args) t m l post
    | load: forall t m l sz x a v addr post,
        map.get l a = Some addr ->
        load sz m addr = Some v ->
        post t m (map.put l x v) ->
        exec (SLoad sz x a) t m l post
    | store: forall t m m' l sz a addr v val post,
        map.get l a = Some addr ->
        map.get l v = Some val ->
        store sz m addr val = Some m' ->
        post t m' l ->
        exec (SStore sz a v) t m l post
    | lit: forall t m l x v post,
        post t m (map.put l x (word.of_Z v)) ->
        exec (SLit x v) t m l post
    | op: forall t m l x op y y' z z' post,
        map.get l y = Some y' ->
        map.get l z = Some z' ->
        post t m (map.put l x (interp_binop op y' z')) ->
        exec (SOp x op y z) t m l post
    | set: forall t m l x y y' post,
        map.get l y = Some y' ->
        post t m (map.put l x y') ->
        exec (SSet x y) t m l post
    | if_true: forall t m l cond  bThen bElse post,
        eval_bcond l cond = Some true ->
        exec bThen t m l post ->
        exec (SIf cond bThen bElse) t m l post
    | if_false: forall t m l cond bThen bElse post,
        eval_bcond l cond = Some false ->
        exec bElse t m l post ->
        exec (SIf cond bThen bElse) t m l post
    | loop: forall t m l cond body1 body2 mid1 mid2 post,
        (* This case is carefully crafted in such a way that recursive uses of exec
         only appear under forall and ->, but not under exists, /\, \/, to make sure the
         auto-generated induction principle contains an IH for all recursive uses. *)
        exec body1 t m l mid1 ->
        (forall t' m' l',
            mid1 t' m' l' ->
            eval_bcond l' cond <> None) ->
        (forall t' m' l',
            mid1 t' m' l' ->
            eval_bcond l' cond = Some false ->
            post t' m' l') ->
        (forall t' m' l',
            mid1 t' m' l' ->
            eval_bcond l' cond = Some true ->
            exec body2 t' m' l' mid2) ->
        (forall t'' m'' l'',
            mid2 t'' m'' l'' ->
            exec (SLoop body1 cond body2) t'' m'' l'' post) ->
        exec (SLoop body1 cond body2) t m l post
    | seq: forall t m l s1 s2 mid post,
        exec s1 t m l mid ->
        (forall t' m' l', mid t' m' l' -> exec s2 t' m' l' post) ->
        exec (SSeq s1 s2) t m l post
    | skip: forall t m l post,
        post t m l ->
        exec SSkip t m l post.

    Lemma det_step: forall t0 m0 l0 s1 s2 t1 m1 l1 post,
        exec s1 t0 m0 l0 (fun t1' m1' l1' => t1' = t1 /\ m1' = m1 /\ l1' = l1) ->
        exec s2 t1 m1 l1 post ->
        exec (SSeq s1 s2) t0 m0 l0 post.
    Proof.
      intros.
      eapply seq; [eassumption|].
      intros. simpl in *. simp.
      assumption.
    Qed.

    Lemma weaken: forall t l m s post1,
        exec s t m l post1 ->
        forall post2,
          (forall t' m' l', post1 t' m' l' -> post2 t' m' l') ->
          exec s t m l post2.
    Proof.
      induction 1; intros; try solve [econstructor; eauto].
      - eapply interact; try eassumption.
        intros; simp.
        match goal with
        | H: _ |- _ => solve [edestruct H; simp; eauto]
        end.
      - eapply call.
        4: eapply IHexec.
        all: eauto.
        intros. simp.
        specialize H3 with (1 := H5).
        simp. eauto 10.
    Qed.

    Ltac equalities :=
      repeat match goal with
             | H1: ?e = ?e1, H2: ?e = ?e2 |- _ =>
               progress (let H := fresh in assert (e1 = e2) as H by congruence; ensure_new H; simp)
             | H1: ?P, H2: ?P |- _ => clear H2
             end;
      simp.

    (* TODO is this the canconical form to impose as a requirement?
     Or should we impose post1 <-> post2, or something else? *)
    Axiom ext_spec_intersect: forall t m a args (post1 post2: mem -> list word -> Prop),
        ext_spec t m a args post1 ->
        ext_spec t m a args post2 ->
        ext_spec t m a args (fun m' resvals => post1 m' resvals /\ post2 m' resvals).

    Lemma intersect: forall t l m s post1,
        exec s t m l post1 ->
        forall post2,
          exec s t m l post2 ->
          exec s t m l (fun t' m' l' => post1 t' m' l' /\ post2 t' m' l').
    Proof.
      induction 1; intros;
        match goal with
        | H: exec _ _ _ _ _ |- _ => inversion H; subst; clear H
        end;
        equalities;
        try solve [econstructor; eauto | exfalso; congruence].

      - (* SInteract *)
        eapply @interact.
        + eassumption.
        + eapply ext_spec_intersect; [ exact H0 | exact H11 ].
        + simpl. intros. simp.
        edestruct H1 as (? & ? & ?); [eassumption|].
        edestruct H12 as (? & ? & ?); [eassumption|].
        equalities.
        eauto 10.

      - (* SCall *)
        rename IHexec into IH.
        specialize IH with (1 := H15).
        eapply @call; [..|exact IH|]; eauto.
        rename H3 into Ex1.
        rename H16 into Ex2.
        move Ex1 before Ex2.
        intros. simpl in *. destruct_conjs.
        specialize Ex1 with (1 := H3).
        specialize Ex2 with (1 := H4).
        destruct_conjs.
        equalities.
        eauto 10.

      - (* SLoop *)
        eapply @loop.
        + eapply IHexec. exact H10.
        + simpl. intros. simp. eauto.
        + simpl. intros. simp. eauto.
        + simpl. intros. simp. eapply H3; [eassumption..|]. (* also an IH *)
          eapply H17; eassumption.
        + simpl. intros. simp. eapply H5; [eassumption..|]. (* also an IH *)
          eapply H18; eassumption.

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
  Context {pp : unique! Semantics.parameters}.
  Context {locals_ok: map.ok locals}.
  Context {varname_eq_dec: DecidableEq varname}.

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

  Lemma modVarsSound_fixpoint: forall fuel e s initialSt initialM finalSt finalM,
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
      try solve [map_solver locals_ok|refine (map.only_differ_putmany _ _ _ _ _); eassumption].
  Qed.

  Lemma modVarsSound: forall e s initialT (initialSt: locals) initialM post,
      exec e s initialT initialM initialSt post ->
      exec e s initialT initialM initialSt
           (fun finalT finalM finalSt => map.only_differ initialSt (modVars s) finalSt).
  Proof.
    induction 1;
      try solve [ econstructor; [eassumption..|simpl; map_solver locals_ok] ].
    - eapply exec.interact; try eassumption.
      intros; simp.
      edestruct H1; try eassumption. simp.
      eexists; split; [eassumption|].
      simpl. try split; eauto.
      eapply map.only_differ_putmany. eassumption.
    - eapply exec.call. 4: exact H2. (* don't pick IHexec! *) all: try eassumption.
      intros; simpl in *; simp.
      edestruct H3; try eassumption. simp.
      do 2 eexists; split; [|split]; try eassumption.
      eapply map.only_differ_putmany. eassumption.
    - eapply exec.if_true; try eassumption.
      eapply exec.weaken; [eassumption|].
      simpl; intros. map_solver locals_ok.
    - eapply exec.if_false; try eassumption.
      eapply exec.weaken; [eassumption|].
      simpl; intros. map_solver locals_ok.
    - eapply exec.loop with
          (mid3 := fun t' m' l' => mid1 t' m' l' /\ map.only_differ l (modVars body1) l')
          (mid4 := fun t' m' l' => mid2 t' m' l' /\
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
          (mid0 := fun t' m' l' => mid t' m' l' /\ map.only_differ l (modVars s1) l').
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
    funcname_eq_dec:> DecidableEq funname;
  }.

  Instance to_FlatImp_params(p: parameters): FlatImp.parameters := {|
    FlatImp.max_ext_call_code_size _ := 0;
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
           (* | |- _ => eapply @ExInteract  not possible because actname=Empty_set *)
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

Goal True. idtac "End of FlatImp.v". Abort.