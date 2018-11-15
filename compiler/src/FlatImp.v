Require Import Coq.ZArith.ZArith.
Require Import lib.LibTacticsMin.
Require Import riscv.util.BitWidths.
Require Import riscv.Utility.
Require Import bedrock2.Macros.
Require Import bedrock2.Syntax.
Require compiler.NoActionSyntaxParams.
Require Import compiler.util.Common.
Require Import compiler.util.Tactics.
Require Import compiler.Op.
Require Import compiler.Memory.
Require Import compiler.Decidable.


Section Syntax.
  Context {pp : unique! Basic_bopnames.parameters}.

  Inductive stmt: Set :=
    | SLoad(x: varname)(a: varname): stmt
    | SStore(a: varname)(v: varname): stmt
    | SLit(x: varname)(v: Z): stmt
    | SOp(x: varname)(op: bopname)(y z: varname): stmt
    | SSet(x y: varname): stmt
    | SIf(cond: varname)(bThen bElse: stmt): stmt
    | SLoop(body1: stmt)(cond: varname)(body2: stmt): stmt
    | SSeq(s1 s2: stmt): stmt
    | SSkip: stmt
    | SCall(binds: list varname)(f: funcname)(args: list varname)
    | SInteract(binds: list varname)(a: actname)(args: list varname).
End Syntax.


Module Import FlatImp.
  Class parameters := {
    bopname_params :> Basic_bopnames.parameters;

    mword : Set;
    MachineWidth_Inst: MachineWidth mword;

    varname_eq_dec : DecidableEq varname;
    funcname_eq_dec: DecidableEq funcname;
    actname_eq_dec : DecidableEq actname;

    varSet_Inst: SetFunctions varname;
    varMap_Inst: MapFunctions varname mword;
    funcMap_Inst: MapFunctions funcname (list varname * list varname * stmt);

    max_ext_call_code_size: Z;
    Event: Type;

    ext_spec:
      (* given an action label, a trace of what happened so fat,
         and a list of function call arguments, *)
      actname -> list Event -> list mword ->
      (* returns a set of (extended trace, function call results) *)
      (list Event -> list mword -> Prop) ->
      Prop; (* or returns no set if the call fails.
      Will give it access to the memory (and possibly the full registers)
      once we have adequate separation logic reasoning in the compiler correctness proof.
      Passing in the trace of what happened so far allows ext_spec to impose restrictions
      such as "you can only call foo after calling init". *)
  }.
End FlatImp.

Existing Instance varname_eq_dec.
Existing Instance funcname_eq_dec.
Existing Instance actname_eq_dec.
Existing Instance varSet_Inst.
Existing Instance MachineWidth_Inst.
Existing Instance varMap_Inst.
Existing Instance funcMap_Inst.


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
    Variable (e: map funcname (list varname * list varname * stmt)).

    (* If we want a bigstep evaluation relation, we either need to put
       fuel into the SLoop constructor, or give it as argument to eval *)
    Fixpoint eval_stmt(f: nat)(st: map varname mword)(m: mem)(s: stmt):
      option (map varname mword * mem) :=
      match f with
      | O => None (* out of fuel *)
      | S f => match s with
        | SLoad x a =>
            'Some a <- get st a;
            'Some v <- read_mem a m;
            Some (put st x v, m)
        | SStore a v =>
            'Some a <- get st a;
            'Some v <- get st v;
            'Some m <- write_mem a v m;
            Some (st, m)
        | SLit x v =>
            Some (put st x (ZToReg v), m)
        | SOp x op y z =>
            'Some y <- get st y;
            'Some z <- get st z;
            Some (put st x (eval_binop op y z), m)
        | SSet x y =>
            'Some v <- get st y;
            Some (put st x v, m)
        | SIf cond bThen bElse =>
            'Some vcond <- get st cond;
            eval_stmt f st m (if reg_eqb vcond (ZToReg 0) then bElse else bThen)
        | SLoop body1 cond body2 =>
            'Some (st, m) <- eval_stmt f st m body1;
            'Some vcond <- get st cond;
            if reg_eqb vcond (ZToReg 0) then Some (st, m) else
              'Some (st, m) <- eval_stmt f st m body2;
              eval_stmt f st m (SLoop body1 cond body2)
        | SSeq s1 s2 =>
            'Some (st, m) <- eval_stmt f st m s1;
            eval_stmt f st m s2
        | SSkip => Some (st, m)
        | SCall binds fname args =>
          'Some (params, rets, fbody) <- get e fname;
          'Some argvs <- option_all (List.map (get st) args);
          'Some st0 <- putmany params argvs empty_map;
          'Some (st1, m') <- eval_stmt f st0 m fbody;
          'Some retvs <- option_all (List.map (get st1) rets);
          'Some st' <- putmany binds retvs st;
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
             | E: reg_eqb _ _ = true  |- _ => apply reg_eqb_true  in E
             | E: reg_eqb _ _ = false |- _ => apply reg_eqb_false in E
             end;
      inversionss;
      eauto 16.

    Lemma invert_eval_SLoad: forall fuel initialSt initialM x y final,
      eval_stmt (S fuel) initialSt initialM (SLoad x y) = Some final ->
      exists a v, get initialSt y = Some a /\
                  read_mem a initialM = Some v /\
                  final = (put initialSt x v, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SStore: forall fuel initialSt initialM x y final,
      eval_stmt (S fuel) initialSt initialM (SStore x y) = Some final ->
      exists a v finalM, get initialSt x = Some a /\
                         get initialSt y = Some v /\
                         write_mem a v initialM = Some finalM /\
                         final = (initialSt, finalM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SLit: forall fuel initialSt initialM x v final,
      eval_stmt (S fuel) initialSt initialM (SLit x v) = Some final ->
      final = (put initialSt x (ZToReg v), initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SOp: forall fuel x y z op initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM (SOp x op y z) = Some final ->
      exists v1 v2,
        get initialSt y = Some v1 /\
        get initialSt z = Some v2 /\
        final = (put initialSt x (eval_binop op v1 v2), initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SSet: forall fuel x y initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM (SSet x y) = Some final ->
      exists v,
        get initialSt y = Some v /\ final = (put initialSt x v, initialM).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SIf: forall fuel cond bThen bElse initialSt initialM final,
      eval_stmt (S fuel) initialSt initialM (SIf cond bThen bElse) = Some final ->
      exists vcond,
        get initialSt cond = Some vcond /\
        (vcond <> ZToReg 0 /\ eval_stmt fuel initialSt initialM bThen = Some final \/
         vcond =  ZToReg 0 /\ eval_stmt fuel initialSt initialM bElse = Some final).
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SLoop: forall fuel st1 m1 body1 cond body2 p4,
      eval_stmt (S fuel) st1 m1 (SLoop body1 cond body2) = Some p4 ->
      eval_stmt fuel st1 m1 body1 = Some p4 /\ get (fst p4) cond = Some (ZToReg 0) \/
      exists st2 m2 st3 m3 cv, eval_stmt fuel st1 m1 body1 = Some (st2, m2) /\
                               get st2 cond = Some cv /\ cv <> ZToReg 0 /\
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
        get e fname = Some (params, rets, fbody) /\
        option_all (List.map (get st) args) = Some argvs /\
        putmany params argvs empty_map = Some st0 /\
        eval_stmt f st0 m1 fbody = Some (st1, m') /\
        option_all (List.map (get st1) rets) = Some retvs /\
        putmany binds retvs st = Some st' /\
        p2 = (st', m').
    Proof. inversion_lemma. Qed.

    Lemma invert_eval_SInteract : forall st m1 p2 f binds fname args,
      eval_stmt (S f) st m1 (SInteract binds fname args) = Some p2 ->
      False.
    Proof. inversion_lemma. Qed.

    Local Notation locals := (map varname mword).
    Local Notation trace := (list Event).

    (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
    Implicit Types post : trace -> @Memory.mem mword -> locals -> Prop.

    (* alternative semantics which allow non-determinism *)
    Inductive exec:
      stmt ->
      trace -> @Memory.mem mword -> locals ->
      (trace -> @Memory.mem mword -> locals -> Prop)
    -> Prop :=
    | ExInteract: forall t m l action argvars argvals resvars outcome post,
        option_all (List.map (get l) argvars) = Some argvals ->
        ext_spec action t argvals outcome ->
        (forall new_t resvals,
            outcome new_t resvals ->
            exists l', putmany resvars resvals l = Some l' /\ post (new_t) m l') ->
        exec (SInteract resvars action argvars) t m l post
    | ExCall: forall t m l binds fname args params rets fbody argvs st0 post outcome,
        get e fname = Some (params, rets, fbody) ->
        option_all (List.map (get l) args) = Some argvs ->
        putmany params argvs empty_map = Some st0 ->
        exec fbody t m st0 outcome ->
        (forall t' m' st1,
            outcome t' m' st1 ->
            exists retvs l',
              option_all (List.map (get st1) rets) = Some retvs /\
              putmany binds retvs l = Some l' /\
              post t' m' l') ->
        exec (SCall binds fname args) t m l post
    | ExLoad: forall t m l x a v addr post,
        get l a = Some addr ->
        Memory.read_mem addr m = Some v ->
        post t m (put l x v) ->
        exec (SLoad x a) t m l post
    | ExStore: forall t m m' l a addr v val post,
        get l a = Some addr ->
        get l v = Some val ->
        Memory.write_mem addr val m = Some m' ->
        post t m' l ->
        exec (SStore a v) t m l post
    | ExLit: forall t m l x v post,
        post t m (put l x (ZToReg v)) ->
        exec (SLit x v) t m l post
    | ExOp: forall t m l x op y y' z z' post,
        get l y = Some y' ->
        get l z = Some z' ->
        post t m (put l x (eval_binop op y' z')) ->
        exec (SOp x op y z) t m l post
    | ExSet: forall t m l x y y' post,
        get l y = Some y' ->
        post t m (put l x y') ->
        exec (SSet x y) t m l post
    | ExIfThen: forall t m l cond vcond bThen bElse post,
        get l cond = Some vcond ->
        vcond <> ZToReg 0 ->
        exec bThen t m l post ->
        exec (SIf cond bThen bElse) t m l post
    | ExIfElse: forall t m l cond bThen bElse post,
        get l cond = Some (ZToReg 0) ->
        exec bElse t m l post ->
        exec (SIf cond bThen bElse) t m l post
    | ExLoop: forall t m l cond body1 body2 mid post,
        (* this case is carefully crafted in such a way that recursive uses of exec
         only appear under forall and ->, but not under exists, /\, \/, to make sure the
         auto-generated induction principle contains an IH for both recursive uses *)
        exec body1 t m l mid ->
        (forall t' m' l', mid t' m' l' -> get l' cond <> None) ->
        (forall t' m' l',
            mid t' m' l' ->
            get l' cond = Some (ZToReg 0) -> post t' m' l') ->
        (forall t' m' l',
            mid t' m' l' ->
            forall v,
              get l' cond = Some v ->
              v <> ZToReg 0 ->
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

  Definition stmt_size_body(rec: stmt -> Z)(s: stmt): Z :=
    match s with
    | SLoad x a => 1
    | SStore a v => 1
    | SLit x v => 8
    | SOp x op y z => 2
    | SSet x y => 1
    | SIf cond bThen bElse => 1 + (rec bThen) + (rec bElse)
    | SLoop body1 cond body2 => 1 + (rec body1) + (rec body2)
    | SSeq s1 s2 => 1 + (rec s1) + (rec s2)
    | SSkip => 1
    | SCall binds f args => 1 + (Zlength binds + Zlength args)
    | SInteract binds f args => 1 + (Zlength binds + Zlength args) + max_ext_call_code_size
    end.

  Fixpoint stmt_size(s: stmt): Z := stmt_size_body stmt_size s.
  (* TODO: in coq 8.9 it will be possible to state this lemma automatically: https://github.com/coq/coq/blob/91e8dfcd7192065f21273d02374dce299241616f/CHANGES#L16 *)
  Lemma stmt_size_unfold : forall s, stmt_size s = stmt_size_body stmt_size s. destruct s; reflexivity. Qed.

  (* returns the set of modified vars *)
  Fixpoint modVars(s: stmt): set varname :=
    match s with
    | SLoad x y => singleton_set x
    | SStore x y => empty_set
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

  Fixpoint accessedVars(s: stmt): set varname :=
    match s with
    | SLoad x y => union (singleton_set x) (singleton_set y)
    | SStore x y => union (singleton_set x) (singleton_set y)
    | SLit x v => singleton_set x
    | SOp x op y z => union (singleton_set x) (union (singleton_set y) (singleton_set z))
    | SSet x y => union (singleton_set x) (singleton_set y)
    | SIf cond bThen bElse =>
        union (singleton_set cond) (union (accessedVars bThen) (accessedVars bElse))
    | SLoop body1 cond body2 =>
        union (singleton_set cond) (union (accessedVars body1) (accessedVars body2))
    | SSeq s1 s2 =>
        union (accessedVars s1) (accessedVars s2)
    | SSkip => empty_set
    | SCall binds funcname args => union (of_list binds) (of_list args)
    | SInteract binds funcname args => union (of_list binds) (of_list args)
    end.

  Lemma modVars_subset_accessedVars: forall s,
    subset (modVars s) (accessedVars s).
  Proof.
    intro s. induction s; simpl; map_solver varname mword.
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
             | H:     (@eq mword _ _)  |- _ => apply reg_eqb_eq in H; rewrite H
             | H: not (@eq mword _ _)  |- _ => apply reg_eqb_ne in H; rewrite H
             end;
      rewrite? reg_eqb_eq by reflexivity;
      eauto.
      contradiction.
  Qed.

  Lemma modVarsSound: forall fuel e s initialSt initialM finalSt finalM,
    eval_stmt e fuel initialSt initialM s = Some (finalSt, finalM) ->
    only_differ initialSt (modVars s) finalSt.
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
      map_solver varname mword;
      refine (only_differ_putmany _ _ _ _ _ _); eassumption.
  Qed.
End FlatImp2.

Ltac fuel_increasing_rewrite :=
  match goal with
  | Ev: eval_stmt ?env ?Fuel1 ?l ?m ?s = ?final
    |- context [eval_stmt ?env ?Fuel2 ?l ?m ?s]
    => let IE := fresh in assert (Fuel1 <= Fuel2)%nat as IE by omega;
       let P := fresh in pose proof increase_fuel_still_Success;
       specialize P with (1 := IE) (2 := Ev);
       rewrite P;
       clear P IE
  end.


Module Import FlatImpSemanticsEquiv.
  Class parameters := {
    noActionParams :> NoActionSyntaxParams.parameters;

    mword : Set;
    MachineWidth_Inst: MachineWidth mword;

    varname_eq_dec : DecidableEq varname;
    funcname_eq_dec: DecidableEq funcname;

    varSet_Inst: SetFunctions varname;
    varMap_Inst: MapFunctions varname mword;
    funcMap_Inst: MapFunctions funcname (list varname * list varname * stmt);
  }.

  Existing Instance noActionParams.
  Existing Instance MachineWidth_Inst.
  Existing Instance varname_eq_dec.
  Existing Instance funcname_eq_dec.
  Existing Instance varSet_Inst.
  Existing Instance varMap_Inst.
  Existing Instance funcMap_Inst.

  Instance to_FlatImp_params(p: parameters): FlatImp.parameters := {|
    FlatImp.max_ext_call_code_size := 0;
    FlatImp.Event := Empty_set;
    FlatImp.ext_spec action oldTrace newTrace outcome := False;
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

  Lemma intersect_exec: forall env t l m s post1,
      exec env s t m l post1 ->
      forall post2,
      exec env s t m l post2 ->
      exec env s t m l (fun t' m' l' => post1 t' m' l' /\ post2 t' m' l').
  Proof.
    induction 1; intros;
      match goal with
      | H: exec _ _ _ _ _ _ |- _ => inversion H; subst; clear H
      end;
      try solve [prove_exec].
    - (* SCall *)
      match goal with
      | H1: ?e = Some (?x1, ?y1, ?z1), H2: ?e = Some (?x2, ?y2, ?z2) |- _ =>
        replace x2 with x1 in * by congruence;
        replace y2 with y1 in * by congruence;
        replace z2 with z1 in * by congruence;
        clear x2 y2 z2 H2
      end.
      repeat match goal with
             | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
               replace v2 with v1 in * by congruence;
               clear v2 H2
             end.
      rename IHexec into IH.
      specialize IH with (1 := H15).
      eapply @ExCall; [..|exact IH|]; eauto.
      rename H3 into Ex1.
      rename H16 into Ex2.
      move Ex1 before Ex2.
      intros. simpl in *. destruct_conjs.
      specialize Ex1 with (1 := H3).
      specialize Ex2 with (1 := H4).
      destruct_conjs.
      repeat match goal with
             | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
               replace v2 with v1 in * by congruence;
               clear v2 H2
             end.
      eauto 10.
    - (* SLoop *)
      pose proof IHexec as IH1.
      specialize IH1 with (1 := H8).
      eapply @ExLoop; [exact IH1 | intros; simpl in *; destruct_conjs; eauto ..].
    - (* SSeq *)
      pose proof IHexec as IH1.
      specialize IH1 with (1 := H5).
      eapply @ExSeq; [exact IH1|].
      intros; simpl in *.
      destruct H2.
      eauto.
  Qed.

  Lemma weaken_exec: forall env t l m s post1,
      exec env s t m l post1 ->
      forall post2 : list Event -> mem -> map varname FlatImp.mword -> Prop,
      (forall t' m' l', post1 t' m' l' -> post2 t' m' l') ->
      exec env s t m l post2.
  Proof.
    induction 1; intros; try solve [prove_exec].
    eapply @ExCall.
    4: eapply IHexec.
    all: eauto.
    intros.
    specialize H3 with (1 := H5).
    destruct_conjs. eauto 10.
  Qed.

  Lemma inductive_to_fixpoint_semantics_aux: forall env t l m s post,
      exec env s t m l post ->
      t = nil ->
      exists fuel, exec env s t m l (fun t' m' l' => eval_stmt env fuel l m s = Some (l', m')).
  Proof.
    induction 1; intros; subst;
      try destruct action;
      try (specialize (IHexec eq_refl); destruct IHexec as [fuel IHexec]);
      try solve [exists 1%nat; prove_exec];
      try solve [exists (S fuel); prove_exec].

    admit. admit.
    {
      exists (S fuel).
      pose proof intersect_exec as P.
      specialize P with (1 := H) (2 := IHexec).
      eapply @ExSeq; [exact P|].
      intros.
      destruct H2 as [? ?].
      simpl.
      rewrite_match.
(*
      edestruct H1 as [fuel' Q]; eauto.
      eauto.

      clear H IHexec.
      prove_exec.
      eapply @ExIfThen; eauto.
      simpl in *.
      rewrite_match.
      rewrite reg_eqb_ne by congruence.
      exact IH.
    }
*)
  Abort.

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
      try solve [prove_exec; exists 1%nat; simpl; rewrite_match; reflexivity].

    Focus 10.
    eapply @ExSeq; [exact IHexec | ].
    intros; simpl in *; destruct_products. subst.
    specialize H1 with (1 := H2rl) (2 := eq_refl).
    eapply weaken_exec; [exact H1|].
    intros; simpl in *; destruct_products. subst.
    repeat split; eauto.
    exists (S (fuel + fuel0)).
    simpl in *.
    do 2 fuel_increasing_rewrite. reflexivity.

  Admitted.



(*
  Lemma inductive_to_fixpoint_semantics_aux: forall env t l m s post,
      exec env s t m l post ->
      t = nil ->
      exec env s t m l (fun t' m' l' => exists fuel, eval_stmt env fuel l m s = Some (l', m')).
  Proof.
    induction 1; intros; subst;
      try destruct action;
      try specialize (IHexec eq_refl);
      try solve [prove_exec; exists 1%nat; simpl; rewrite_match; reflexivity].

    - admit.
    - eapply @ExIfThen; eauto.
      eapply weaken_exec; [exact IHexec|].
      intros. simpl in *.
      destruct H2 as [fuel ?].
      exists (S fuel).
      prove_exec.
    - eapply @ExIfElse; eauto.
      eapply weaken_exec; [exact IHexec|].
      intros. simpl in *.
      destruct H1 as [fuel ?].
      exists (S fuel).
      prove_exec.
    - eapply @ExLoop; [exact IHexec | intros; simpl in *..].
      + admit.
      + admit.
      + admit.
    - eapply @ExSeq; [exact IHexec | ].
      intros; simpl in *.



  Qed.
 *)

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
