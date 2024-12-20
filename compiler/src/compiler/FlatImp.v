Require Import Coq.Bool.Bool.
Require Import Coq.Relations.Relation_Operators.
Require Import Coq.Wellfounded.Transitive_Closure.
Require Import Coq.ZArith.ZArith.
Require Import Coq.Lists.List. Import ListNotations.
Require Import bedrock2.MetricLogging.
Require Import bedrock2.MetricCosts.
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
Require Import bedrock2.LeakageSemantics.
Require Import bedrock2.MetricLeakageSemantics.
Require Import coqutil.Datatypes.ListSet.
Require Import coqutil.Map.OfListWord.
Require Import coqutil.Word.Bitwidth.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.fwd.
Local Hint Mode Word.Interface.word - : typeclass_instances.

Inductive bbinop: Set :=
| BEq
| BNe
| BLt
| BGe
| BLtu
| BGeu.

Section Syntax.
  Context {varname: Type}.

  Inductive operand: Type :=
  | Var (v: varname)
  | Const (c: Z)
  .

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
    | SOp(x: varname)(op: bopname)(y: varname)(z: operand)
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

  Local Arguments Z.add _ _ : simpl never.

  Lemma stmt_size_nonneg: forall s, 0 <= stmt_size s.
  Proof.
    induction s; simpl; try blia;
    assert (0 <= (Z.of_nat (Datatypes.length t) + 3) / 4);
      try apply Z.div_pos; blia.
  Qed.

  Inductive subexpression : stmt -> stmt -> Prop :=
  | SStackalloc_subexp : forall x1 x2 s, subexpression s (SStackalloc x1 x2 s)
  | SIf_then_subexp : forall x1 x2 s, subexpression s (SIf x1 s x2)
  | SIf_else_subexp : forall x1 x2 s, subexpression s (SIf x1 x2 s)
  | SLoop_body1_subexp : forall x1 x2 s, subexpression s (SLoop s x1 x2)
  | SLoop_body2_subexp : forall x1 x2 s, subexpression s (SLoop x1 x2 s)
  | SSeq_body1_subexp : forall x1 s, subexpression s (SSeq s x1)
  | SSeq_body2_subexp : forall x1 s, subexpression s (SSeq x1 s).

  Lemma wf_subexpression : well_founded subexpression.
  Proof.
    cbv [well_founded]. intros a. induction a.
    all: constructor; intros ? H; inversion H; subst; assumption.
  Defined.

  Definition stmt_lt :=
    clos_trans _ subexpression.

  Lemma wf_stmt_lt : well_founded stmt_lt.
  Proof.
    cbv [stmt_lt]. apply Transitive_Closure.wf_clos_trans.
    apply wf_subexpression.
  Defined.

  Fixpoint modVars_as_list(veq: varname -> varname -> bool)(s: stmt): list varname :=
    match s with
    | SSkip | SStore _ _ _ _ => []
    | SStackalloc x n body => list_union veq [x] (modVars_as_list veq body)
    | SLoad _ x _ _ | SLit x _ | SOp x _ _ _ | SSet x _ | SInlinetable _ x _ _ => [x]
    | SIf _ s1 s2 | SLoop s1 _ s2 | SSeq s1 s2 =>
        list_union veq (modVars_as_list veq s1) (modVars_as_list veq s2)
    | SCall binds _ _ | SInteract binds _ _ => list_union veq binds []
    end.

  Definition ForallVars_bcond_gen{R: Type}(and: R -> R -> R)(P: varname -> R)(cond: bcond): R :=
    match cond with
    | CondBinary _ x y => and (P x) (P y)
    | CondNez x => P x
    end.

  Definition Forall_vars_stmt_gen{R: Type}(T: R)(and: R -> R -> R)
             (P_bcond: bcond -> R)
             (P_vars: varname -> R)
             (P_calls: list varname -> list varname -> R): stmt -> R :=
    fix rec s :=
      match s with
      | SLoad _ x a _ => and (P_vars x) (P_vars a)
      | SStore _ a x _ => and (P_vars a) (P_vars x)
      | SInlinetable _ x _ i => and (P_vars x) (P_vars i)
      | SStackalloc x n body => and (P_vars x) (rec body)
      | SLit x _ => P_vars x
      | SOp x _ y z => let op_z := match z with
                                   | Var v => P_vars v
                                   | Const _ => T
                                   end in
                       and (P_vars x) (and (P_vars y) (op_z))
      | SSet x y => and (P_vars x) (P_vars y)
      | SIf c s1 s2 => and (P_bcond c) (and (rec s1) (rec s2))
      | SLoop s1 c s2 => and (P_bcond c) (and (rec s1) (rec s2))
      | SSeq s1 s2 => and (rec s1) (rec s2)
      | SSkip => T
      | SCall binds _ args => P_calls binds args
      | SInteract binds _ args => P_calls binds args
      end.

  Definition ForallVars_bcond(P_vars: varname -> Prop)(cond: bcond): Prop :=
    Eval unfold ForallVars_bcond_gen in ForallVars_bcond_gen and P_vars cond.

  Definition Forall_vars_stmt(P_vars: varname -> Prop): stmt -> Prop :=
    Eval unfold Forall_vars_stmt_gen in
      Forall_vars_stmt_gen True and (ForallVars_bcond P_vars) P_vars
                           (fun binds args => (List.length binds <= 8)%nat /\
                                              (List.length args <= 8)%nat /\
                                              Forall P_vars binds /\
                                              Forall P_vars args).

  Definition forallbVars_bcond(P_vars: varname -> bool)(cond: bcond): bool :=
    Eval unfold ForallVars_bcond_gen in ForallVars_bcond_gen andb P_vars cond.

  Definition forallb_vars_stmt(P_vars: varname -> bool): stmt -> bool :=
    Eval unfold Forall_vars_stmt_gen in
      Forall_vars_stmt_gen true andb (forallbVars_bcond P_vars) P_vars
                           (fun binds args => (List.length binds <=? 8)%nat &&
                                              (List.length args <=? 8)%nat &&
                                              forallb P_vars binds &&
                                              forallb P_vars args).

  Lemma forallb_vars_stmt_correct
        (P: varname -> Prop)(p: varname -> bool)
        (p_correct: forall x, p x = true <-> P x):
    forall s, forallb_vars_stmt p s = true <-> Forall_vars_stmt P s.
  Proof.
    assert (p_correct_fw: forall x, p x = true -> P x). {
      intros. eapply p_correct. assumption.
    }
    assert (p_correct_bw: forall x, P x -> p x = true). {
      intros. eapply p_correct. assumption.
    }
    clear p_correct.
    induction s; split; simpl; intros; unfold ForallVars_bcond, forallbVars_bcond in *;
      repeat match goal with
             | c: bcond |- _ => destruct c
             | H: andb _ _ = true |- _ => eapply Bool.andb_true_iff in H
             | H: (_ <=? _)%nat = true |- _ => eapply Nat.leb_le in H
             | H: _ /\ _ |- _ => destruct H
             | H: _ <-> _ |- _ => destruct H
             | |- andb _ _ = true => apply Bool.andb_true_iff
             | |- _ /\ _ => split
             | |- (_ <=? _)%nat = true => eapply Nat.leb_le
             | y: operand |- _ => destruct y
             end;
      eauto using List.Forall_to_forallb, List.forallb_to_Forall.
  Qed.

  Lemma ForallVars_bcond_impl: forall (P Q: varname -> Prop),
      (forall x, P x -> Q x) ->
      forall s, ForallVars_bcond P s -> ForallVars_bcond Q s.
  Proof.
    intros. destruct s; simpl in *; intuition eauto.
  Qed.

  Lemma Forall_vars_stmt_impl: forall (P Q: varname -> Prop),
      (forall x, P x -> Q x) ->
      forall s, Forall_vars_stmt P s -> Forall_vars_stmt Q s.
  Proof.
    induction s; intros; simpl in *;
      repeat match goal with
          | y : operand |- _ => destruct y
          | _ => intuition eauto using ForallVars_bcond_impl, Forall_impl
          end.
  Qed.
End Syntax.

Arguments bcond: clear implicits.
Arguments stmt: clear implicits.

Local Open Scope Z_scope.

Section FlatImp1.
  Context {varname: Type} {varname_eqb: varname -> varname -> bool}.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {mem: map.map word byte} {locals: map.map varname word}
          {env: map.map String.string (list varname * list varname * stmt varname)}.

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
        match map.get st x, map.get st y with
        | Some mx, Some my => Some (eval_bbinop op mx my)
        | _, _ => None
        end
      | CondNez x =>
        match  map.get st x  with
        | Some mx => Some (negb (word.eqb mx (word.of_Z 0)))
        | None => None
        end
      end.
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
    Context {varname: Type} {varname_eqb: varname -> varname -> bool}.
    Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
    Context {mem: map.map word byte} {locals: map.map varname word}
            {env: map.map String.string (list varname * list varname * stmt varname)}.
    Context {ext_spec: ExtSpec} .
    Context {varname_eq_spec: EqDecider varname_eqb}
            {word_ok: word.ok word}
            {mem_ok: map.ok mem}
            {locals_ok: map.ok locals}
            {env_ok: map.ok env}
            {ext_spec_ok: ext_spec.ok ext_spec}.

    Variable (phase: compphase).
    Variable (isReg: varname -> bool).

    Variable (e: env).

    Local Notation metrics := MetricLog.

    (* COQBUG(unification finds Type instead of Prop and fails to downgrade *)
    Implicit Types post : leakage -> trace -> mem -> locals -> metrics -> Prop.

    Definition lookup_op_locals (l: locals) (o: operand) :=
      match o with
      | Var vo => map.get l vo
      | Const co => Some (word.of_Z co)
      end.

    (* Helper functions for computing costs of instructions *)

    Definition cost_SOp x y z mc :=
      cost_op (fun v => match v with | Var vo => isReg vo | Const _ => true end)
      (Var x) (Var y) z mc.

    Definition cost_SIf bcond mc :=
      match bcond with
      | CondBinary _ x y => cost_if isReg x (Some y)
      | CondNez x => cost_if isReg x None
      end mc.

    Definition cost_SLoop_true bcond mc :=
      match bcond with
      | CondBinary _ x y => cost_loop_true isReg x (Some y)
      | CondNez x => cost_loop_true isReg x None
      end mc.

    Definition cost_SLoop_false bcond mc :=
      match bcond with
      | CondBinary _ x y => cost_loop_false isReg x (Some y)
      | CondNez x => cost_loop_false isReg x None
      end mc.

    (* alternative semantics which allow non-determinism *)
    Inductive exec {pick_sp: PickSp} :
      stmt varname ->
      leakage -> trace -> mem -> locals -> metrics ->
      (leakage -> trace -> mem -> locals -> metrics -> Prop)
    -> Prop :=
    | interact: forall k t m mKeep mGive l mc action argvars argvals resvars outcome post,
        map.split m mKeep mGive ->
        map.getmany_of_list l argvars = Some argvals ->
        ext_spec t mGive action argvals outcome ->
        (forall mReceive resvals klist,
            outcome mReceive resvals klist ->
            exists l', map.putmany_of_list_zip resvars resvals l = Some l' /\
            forall m', map.split m' mKeep mReceive ->
            post (leak_list klist :: k) (((mGive, action, argvals), (mReceive, resvals)) :: t) m' l'
                 (cost_interact phase mc)) ->
        exec (SInteract resvars action argvars) k t m l mc post
    | call: forall k t m l mc binds fname args params rets fbody argvs st0 post outcome,
        map.get e fname = Some (params, rets, fbody) ->
        map.getmany_of_list l args = Some argvs ->
        map.putmany_of_list_zip params argvs map.empty = Some st0 ->
        exec fbody (leak_unit :: k) t m st0 mc outcome ->
        (forall k' t' m' mc' st1,
            outcome k' t' m' st1 mc' ->
            exists retvs l',
              map.getmany_of_list st1 rets = Some retvs /\
              map.putmany_of_list_zip binds retvs l = Some l' /\
              post k' t' m' l' (cost_call phase mc')) ->
        exec (SCall binds fname args) k t m l mc post
    | load: forall k t m l mc sz x a o v addr post,
        map.get l a = Some addr ->
        load sz m (word.add addr (word.of_Z o)) = Some v ->
        post (leak_word (word.add addr (word.of_Z o)) :: k) t m (map.put l x v) (cost_load isReg x a mc)->
        exec (SLoad sz x a o) k t m l mc post
    | store: forall k t m m' mc l sz a o addr v val post,
        map.get l a = Some addr ->
        map.get l v = Some val ->
        store sz m (word.add addr (word.of_Z o)) val = Some m' ->
        post (leak_word (word.add addr (word.of_Z o)) :: k) t m' l (cost_store isReg a v mc) ->
        exec (SStore sz a v o) k t m l mc post
    | inlinetable: forall sz x table i v index k t m l mc post,
        (* compiled riscv code uses x as a tmp register and this shouldn't overwrite i *)
        x <> i ->
        map.get l i = Some index ->
        load sz (map.of_list_word table) index = Some v ->
        post (leak_word index :: k) t m (map.put l x v) (cost_inlinetable isReg x i mc) ->
        exec (SInlinetable sz x table i) k t m l mc post
    | stackalloc: forall k t mSmall l mc x n body post,
        n mod (bytes_per_word width) = 0 ->
        (forall mStack mCombined,
            let a := pick_sp k in
            anybytes a n mStack ->
            map.split mCombined mSmall mStack ->
            exec body (leak_unit :: k) t mCombined (map.put l x a) mc
             (fun k' t' mCombined' l' mc' =>
              exists mSmall' mStack',
                anybytes a n mStack' /\
                map.split mCombined' mSmall' mStack' /\
                post k' t' mSmall' l' (cost_stackalloc isReg x mc'))) ->
        exec (SStackalloc x n body) k t mSmall l mc post
    | lit: forall k t m l mc x v post,
        post k t m (map.put l x (word.of_Z v)) (cost_lit isReg x mc) ->
        exec (SLit x v) k t m l mc post
    | op: forall k t m l mc x op y y' z z' post,
        map.get l y = Some y' ->
        lookup_op_locals l z = Some z' ->
        post (leak_binop op y' z' ++ k) t m (map.put l x (interp_binop op y' z')) (cost_SOp x y z mc) ->
        exec (SOp x op y z) k t m l mc post
    | set: forall k t m l mc x y y' post,
        map.get l y = Some y' ->
        post k t m (map.put l x y') (cost_set isReg x y mc) ->
        exec (SSet x y) k t m l mc post
    | if_true: forall k t m l mc cond  bThen bElse post,
        eval_bcond l cond = Some true ->
        exec bThen (leak_bool true :: k) t m l (cost_SIf cond mc) post ->
        exec (SIf cond bThen bElse) k t m l mc post
    | if_false: forall k t m l mc cond bThen bElse post,
        eval_bcond l cond = Some false ->
        exec bElse (leak_bool false :: k) t m l (cost_SIf cond mc) post ->
        exec (SIf cond bThen bElse) k t m l mc post
    | loop: forall k t m l mc cond body1 body2 mid1 mid2 post,
        (* This case is carefully crafted in such a way that recursive uses of exec
         only appear under forall and ->, but not under exists, /\, \/, to make sure the
         auto-generated induction principle contains an IH for all recursive uses. *)
        exec body1 k t m l mc mid1 ->
        (forall k' t' m' l' mc',
            mid1 k' t' m' l' mc' ->
            eval_bcond l' cond <> None) ->
        (forall k' t' m' l' mc',
            mid1 k' t' m' l' mc' ->
            eval_bcond l' cond = Some false ->
            post (leak_bool false :: k') t' m' l' (cost_SLoop_false cond mc')) ->
        (forall k' t' m' l' mc',
            mid1 k' t' m' l' mc' ->
            eval_bcond l' cond = Some true ->
            exec body2 (leak_bool true :: k') t' m' l' mc' mid2) ->
        (forall k'' t'' m'' l'' mc'',
            mid2 k'' t'' m'' l'' mc'' ->
            exec (SLoop body1 cond body2) k'' t'' m'' l''
                 (cost_SLoop_true cond mc'') post) ->
        exec (SLoop body1 cond body2) k t m l mc post
    | seq: forall k t m l mc s1 s2 mid post,
        exec s1 k t m l mc mid ->
        (forall k' t' m' l' mc', mid k' t' m' l' mc' -> exec s2 k' t' m' l' mc' post) ->
        exec (SSeq s1 s2) k t m l mc post
    | skip: forall k t m l mc post,
        post k t m l mc ->
        exec SSkip k t m l mc post.

    Lemma det_step {pick_sp: PickSp} : forall k0 t0 m0 l0 mc0 s1 s2 k1 t1 m1 l1 mc1 post,
        exec s1 k0 t0 m0 l0 mc0 (fun k1' t1' m1' l1' mc1' => k1' = k1 /\ t1' = t1 /\ m1' = m1 /\ l1' = l1 /\ mc1 = mc1') ->
        exec s2 k1 t1 m1 l1 mc1 post ->
        exec (SSeq s1 s2) k0 t0 m0 l0 mc0 post.
    Proof.
      intros.
      eapply seq; [eassumption|].
      intros. simpl in *. simp.
      assumption.
    Qed.

    Lemma seq_cps {pick_sp: PickSp} : forall s1 s2 k t m (l: locals) mc post,
        exec s1 k t m l mc (fun k' t' m' l' mc' => exec s2 k' t' m' l' mc' post) ->
        exec (SSeq s1 s2) k t m l mc post.
    Proof.
      intros. eapply seq. 1: eassumption. simpl. clear. auto.
    Qed.

    Lemma call_cps {pick_sp: PickSp} : forall fname params rets binds args fbody argvs k t (l: locals) m mc st post,
        map.get e fname = Some (params, rets, fbody) ->
        map.getmany_of_list l args = Some argvs ->
        map.putmany_of_list_zip params argvs map.empty = Some st ->
        exec fbody (leak_unit :: k) t m st mc
             (fun k' t' m' st' mc' =>
                exists retvs l',
                  map.getmany_of_list st' rets = Some retvs /\
                    map.putmany_of_list_zip binds retvs l = Some l' /\
                    post k' t' m' l' (cost_call phase mc')) ->
      exec (SCall binds fname args) k t m l mc post.
    Proof.
      intros. eapply call; try eassumption.
      cbv beta. intros *. exact id.
    Qed.

    Lemma loop_cps {pick_sp: PickSp} : forall body1 cond body2 k t m l mc post,
      exec body1 k t m l mc (fun k t m l mc => exists b,
        eval_bcond l cond = Some b /\
        (b = false -> post (leak_bool false :: k) t m l (cost_SLoop_false cond mc)) /\
        (b = true -> exec body2 (leak_bool true :: k) t m l mc (fun k t m l mc =>
           exec (SLoop body1 cond body2) k t m l
                (cost_SLoop_true cond mc) post))) ->
      exec (SLoop body1 cond body2) k t m l mc post.
    Proof.
      intros. eapply loop. 1: eapply H. all: cbv beta; intros; simp.
      - congruence.
      - replace b with false in * by congruence. clear b. eauto. 
      - replace b with true in * by congruence. clear b. eauto.
      - assumption.
    Qed.

    Lemma weaken {pick_sp: PickSp} : forall s k t m l mc post1,
        exec s k t m l mc post1 ->
        forall post2,
          (forall k' t' m' l' mc', post1 k' t' m' l' mc' -> post2 k' t' m' l' mc') ->
          exec s k t m l mc post2.
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

    Lemma seq_assoc {pick_sp: PickSp} : forall s1 s2 s3 k t m l mc post,
        exec (SSeq s1 (SSeq s2 s3)) k t m l mc post ->
        exec (SSeq (SSeq s1 s2) s3) k t m l mc post.
    Proof.
      intros. simp.
      eapply seq_cps.
      eapply seq_cps.
      eapply weaken. 1: eassumption. intros.
      specialize H9 with (1 := H). simp.
      eapply weaken. 1: eassumption. intros.
      eauto.
    Qed.

    Lemma seq_assoc_bw {pick_sp: PickSp} : forall s1 s2 s3 k t m l mc post,
        exec (SSeq (SSeq s1 s2) s3) k t m l mc post ->
        exec (SSeq s1 (SSeq s2 s3)) k t m l mc post.
    Proof. intros. simp. eauto 10 using seq. Qed.

    Ltac equalities :=
      repeat match goal with
             | H1: ?e = ?e1, H2: ?e = ?e2 |- _ =>
               progress (let H := fresh in assert (e1 = e2) as H by congruence; ensure_new H; simp)
             | H1: ?P, H2: ?P |- _ => clear H2
             end;
      simp.

    Lemma intersect {pick_sp: PickSp} : forall k t m l mc s post1,
        exec s k t m l mc post1 ->
        forall post2,
          exec s k t m l mc post2 ->
          exec s k t m l mc (fun k' t' m' l' mc' => post1 k' t' m' l' mc' /\ post2 k' t' m' l' mc').
    Proof.
      induction 1; intros;
        match goal with
        | H: exec _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H
        end;
        equalities;
        try solve [econstructor; eauto | exfalso; congruence].

      - (* SInteract *)
        pose proof ext_spec.mGive_unique as P.
        specialize P with (1 := H) (2 := H7) (3 := H1) (4 := H15).
        subst mGive0.
        destruct (map.split_diff (map.same_domain_refl mGive) H H7) as (? & _).
        subst mKeep0.
        eapply @interact.
        + eassumption.
        + eassumption.
        + eapply ext_spec.intersect; [exact H1|exact H15].
        + simpl. intros. simp.
          edestruct H2 as (? & ? & ?); [eassumption|].
          edestruct H16 as (? & ? & ?); [eassumption|].
          simp.
          equalities.
          eauto 10.

      - (* SCall *)
        rename IHexec into IH.
        specialize IH with (1 := H17).
        eapply @call; [..|exact IH|]; eauto.
        rename H3 into Ex1.
        rename H18 into Ex2.
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
        rename H0 into Ex1, H13 into Ex2.
        eapply weaken. 1: eapply H1. 1,2: eassumption.
        1: eapply Ex2. 1,2: eassumption.
        cbv beta.
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
          eapply H19; eassumption.
        + simpl. intros. simp. eapply H5; [eassumption..|]. (* also an IH *)
          eapply H20; eassumption.

      - (* SSeq *)
        pose proof IHexec as IH1.
        specialize IH1 with (1 := H5).
        eapply @seq; [exact IH1|].
        intros; simpl in *.
        destruct H2.
        eauto.
    Qed.

    Lemma exec_extends_trace {pick_sp: PickSp} s k t m l mc post :
      exec s k t m l mc post ->
      exec s k t m l mc (fun k' t' m' l' mc' => post k' t' m' l' mc' /\ exists k'', k' = k'' ++ k).
    Proof.
      intros H. induction H; try (econstructor; intuition eauto; eexists; align_trace; fail).
      - econstructor; intuition eauto. specialize H2 with (1 := H3). fwd.
        eexists. intuition eauto. eexists. align_trace.
      - econstructor; intuition eauto. fwd. specialize H3 with (1 := H4p0). fwd.
        eexists. intuition eauto. eexists. intuition eauto.
        eexists. align_trace.
      - econstructor; intuition eauto. intros. eapply weaken. 1: eapply H1; eauto.
        simpl. intros. fwd. eexists. eexists. intuition eauto. eexists. align_trace.
      - eapply if_true; intuition eauto. eapply weaken. 1: eapply IHexec.
        simpl. intros. fwd. intuition eauto. eexists. align_trace.
      - eapply if_false; intuition eauto. eapply weaken. 1: eapply IHexec.
        simpl. intros. fwd. intuition eauto. eexists. align_trace.
      - clear H2 H4. econstructor; intuition eauto; fwd; eauto.
        { eexists. align_trace. }
        { eapply weaken. 1: eapply H3; eauto. simpl. intros. fwd.
          instantiate (1 := fun k'0 t'0 m'0 l'0 mc'0 =>
                              mid2 k'0 t'0 m'0 l'0 mc'0 /\ exists k'', k'0 = k'' ++ k).
          simpl. intuition. eexists. align_trace. }
        simpl in *. fwd. eapply weaken. 1: eapply H5; eauto.
        simpl. intros. fwd. intuition. eexists. align_trace.
      - econstructor; intuition eauto. fwd. eapply weaken. 1: eapply H1; eauto.
        simpl. intros. fwd. intuition eauto. eexists. align_trace.
    Qed.

    Lemma exec_ext (pick_sp1: PickSp) s k t m l mc post :
      exec (pick_sp := pick_sp1) s k t m l mc post ->
      forall pick_sp2,
        (forall k', pick_sp1 (k' ++ k) = pick_sp2 (k' ++ k)) ->
        exec (pick_sp := pick_sp2) s k t m l mc post.
    Proof.
      Set Printing Implicit.
      intros H1 pick_sp2. induction H1; intros; try solve [econstructor; eauto].
      - econstructor. 4: eapply exec_extends_trace. all: intuition eauto.
        { eapply IHexec. intros. rewrite associate_one_left.
          repeat rewrite app_assoc. auto. }
        fwd. specialize H3 with (1 := H5p0). fwd. intuition eauto.
      - econstructor; eauto. intros. replace (pick_sp1 k) with (pick_sp2 k) in *.
        { subst a. eapply weaken.
        { eapply H1; eauto.
          intros. eassert (H2' := H2 (_ ++ _ :: nil)). rewrite <- app_assoc in H2'. eapply H2'. }
        eauto. }
        symmetry. apply H2 with (k' := nil).
      - eapply if_true; eauto. eapply IHexec.
        intros. rewrite associate_one_left. repeat rewrite app_assoc. auto.
      - eapply if_false; intuition eauto. eapply IHexec.
        intros. rewrite associate_one_left. repeat rewrite app_assoc. auto.
      - clear H2 H4. eapply loop. 1: eapply exec_extends_trace. all: intuition eauto; fwd; eauto.
        { eapply weaken. 1: eapply exec_extends_trace.
          { eapply H3; eauto.
            intros. rewrite associate_one_left. repeat rewrite app_assoc. auto. }
          simpl. intros. fwd.
          instantiate (1 := fun k'0 t'0 m'0 l'0 mc'0 =>
                              mid2 k'0 t'0 m'0 l'0 mc'0 /\ exists k'', k'0 = k'' ++ k).
          simpl. intuition eauto. eexists. align_trace. }
        simpl in *. fwd. eapply H5; eauto. intros.
        repeat (rewrite app_assoc || rewrite (app_one_l _ (_ ++ k))). auto.
      - econstructor. 1: eapply exec_extends_trace; eauto. simpl. intros. fwd.
        eapply H0; eauto. intros. repeat rewrite app_assoc. apply H2.      
    Qed.

    Local Ltac solve_picksps_equal :=
      intros; cbv beta; f_equal;
      repeat (rewrite rev_app_distr || cbn [rev app]); rewrite List.skipn_app_r;
      [|repeat (rewrite app_length || rewrite rev_length || simpl); blia];
      repeat rewrite <- app_assoc; rewrite List.skipn_app_r;
      [|rewrite rev_length; reflexivity];
      repeat (rewrite rev_app_distr || cbn [rev app] || rewrite rev_involutive);
      repeat rewrite <- app_assoc; reflexivity.

    Lemma exec_to_other_trace (pick_sp: PickSp) s k1 k2 t m l mc post :
      exec s k1 t m l mc post ->
      exec (pick_sp := fun k => pick_sp (rev (skipn (length k2) (rev k)) ++ k1))
        s k2 t m l mc (fun k2' t' m' l' mc' =>
                         exists k'',
                           k2' = k'' ++ k2 /\
                             post (k'' ++ k1) t' m' l' mc').
    Proof.
      intros H. generalize dependent k2. induction H; intros.
      - econstructor; intuition eauto. apply H2 in H3. fwd.
        eexists. intuition eauto. eexists. intuition eauto. 1: align_trace.
        auto.
      - econstructor; intuition eauto.
        { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec; eauto. solve_picksps_equal. }
        cbv beta in *. fwd. apply H3 in H4p1.
        fwd. eexists. intuition eauto. eexists. intuition eauto. eexists.
        split; [align_trace|]. repeat rewrite <- app_assoc. auto.
      - econstructor; intuition eauto. eexists. split; [align_trace|]. auto.
      - econstructor; intuition eauto. eexists. split; [align_trace|]. auto.
      - econstructor; intuition eauto. eexists. split; [align_trace|]. auto.
      - econstructor; intuition eauto. intros.
        replace (rev k2) with (rev k2 ++ nil) in * by apply app_nil_r.
        rewrite List.skipn_app_r in * by (rewrite rev_length; reflexivity).
        simpl in *. eapply weaken.
        { eapply exec_ext with (pick_sp1 := _). 1: eapply H1; eauto. solve_picksps_equal. }
      simpl. intros. fwd. eexists _, _. intuition eauto. eexists (_ ++ _ :: nil).
      rewrite <- app_assoc. simpl. rewrite <- (app_assoc _ _ k). simpl. eauto.
      - econstructor; intuition eauto. eexists. split; [align_trace|]. auto.
      - econstructor; intuition eauto.
      - econstructor; intuition eauto. eexists. split; [align_trace|]. auto.
      - eapply if_true; intuition eauto. eapply weaken.
        { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec. solve_picksps_equal. }
        simpl. intros. fwd. eexists. split; [align_trace|].
        repeat rewrite <- app_assoc. auto.
      - eapply if_false; intuition eauto. eapply weaken.
        { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec. solve_picksps_equal. }
        simpl. intros. fwd. eexists. split; [align_trace|].
        repeat rewrite <- app_assoc. auto.
      - eapply loop. 1: eapply IHexec. all: intuition eauto; fwd; eauto.
        { eexists. split; [align_trace|]. simpl. auto. }
        { eapply exec_ext with (pick_sp1 := _).
          { eapply weaken. 1: eapply H3; eauto. simpl. intros.
            instantiate (1 := fun k'0 t'0 m'0 l'0 mc'0 =>
                                exists k''0,
                                  k'0 = k''0 ++ k2 /\
                                    mid2 (k''0 ++ k) t'0 m'0 l'0 mc'0).
            fwd. eexists. split; [align_trace|].
            repeat rewrite <- app_assoc. simpl. auto. }
          solve_picksps_equal. }
        simpl in *. fwd. eapply exec_ext with (pick_sp1 := _).
        { eapply weaken. 1: eapply H5; eauto. simpl. intros. fwd.
          eexists. split; [align_trace|].
          repeat rewrite <- app_assoc. auto. }
        solve_picksps_equal.
      - econstructor; intuition. fwd. eapply weaken.
        { eapply exec_ext with (pick_sp1 := _). 1: eapply H1; eauto. solve_picksps_equal. }
        simpl. intros. fwd. eexists. split; [align_trace|].
        repeat rewrite <- app_assoc. auto.
      - econstructor. eexists. split; [align_trace|]. assumption.
    Qed.

  End FlatImpExec.
End exec.
Notation exec := exec.exec.

Section FlatImp2.
  Context (varname: Type).
  Context {varname_eqb: varname -> varname -> bool}.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width}.
  Context {mem: map.map word byte} {locals: map.map varname word}
          {env: map.map String.string (list varname * list varname * stmt varname)}.
  Context {ext_spec: ExtSpec} {pick_sp: PickSp}.
  Context {varname_eq_spec: EqDecider varname_eqb}
          {word_ok: word.ok word}
          {mem_ok: map.ok mem}
          {locals_ok: map.ok locals}
          {env_ok: map.ok env}
          {ext_spec_ok: ext_spec.ok ext_spec}.

  Variable (phase: compphase).
  Variable (isReg: varname -> bool).
  
  Definition SimState: Type := leakage * trace * mem * locals * MetricLog.
  Definition SimExec(e: env)(c: stmt varname): SimState -> (SimState -> Prop) -> Prop :=
    fun '(k, t, m, l, mc) post =>
      exec phase isReg e c k t m l mc (fun k' t' m' l' mc' => post (k', t', m', l', mc')).

  Lemma modVarsSound: forall e s initialK initialT (initialSt: locals) initialM (initialMc: MetricLog) post,
      exec phase isReg e s initialK initialT initialM initialSt initialMc post ->
      exec phase isReg e s initialK initialT initialM initialSt initialMc
           (fun initialK finalT finalM finalSt _ => map.only_differ initialSt (modVars s) finalSt).
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
      + eapply exec.intersect; try eassumption.
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
    - eapply @exec.loop with
          (mid1 := fun k' t' m' l' mc' => mid1 k' t' m' l' mc' /\
                                   map.only_differ l (modVars body1) l')
          (mid2 := fun k' t' m' l' mc' => mid2 k' t' m' l' mc' /\
                                   map.only_differ l (modVars (SLoop body1 cond body2)) l').
      + eapply exec.intersect; eassumption.
      + intros. simp. eauto.
      + intros. simp. simpl. map_solver locals_ok.
      + intros. simp. simpl in *.
        eapply exec.intersect; try eassumption; [eauto|].
        eapply exec.weaken.
        * eapply H3; eassumption.
        * simpl. intros. map_solver locals_ok.
      + intros. simp. simpl in *.
        eapply exec.weaken.
        * eapply H5; eassumption.
        * simpl. intros. map_solver locals_ok.
    - eapply @exec.seq with
          (mid := fun k' t' m' l' mc' => mid k' t' m' l' mc' /\ map.only_differ l (modVars s1) l').
      + eapply exec.intersect; eassumption.
      + simpl; intros. simp.
        eapply exec.weaken; [eapply H1; eauto|].
        simpl; intros.
        map_solver locals_ok.
  Qed.

End FlatImp2.

(* various helper tactics extending the ones from MetricCosts *)

Ltac scost_unfold :=
  unfold exec.cost_SOp, exec.cost_SIf, exec.cost_SLoop_true, exec.cost_SLoop_false in *; cost_unfold.

Ltac scost_destr :=
  repeat match goal with
         | x : operand |- _ => destr x
         | x : bbinop _ |- _ => destr x
         | x : bcond _ |- _ => destr x
         | _ => cost_destr
         end.

Ltac scost_solve := scost_unfold; scost_destr; try solve_MetricLog.
Ltac scost_solve_piecewise := scost_unfold; scost_destr; try solve_MetricLog_piecewise.
Ltac scost_hammer := try solve [eauto 3 with metric_arith | scost_solve].
