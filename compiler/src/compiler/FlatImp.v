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
    Context {ext_spec: ExtSpec}.
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
    Implicit Types post : bool -> AEP -> leakage -> trace -> mem -> locals -> metrics -> Prop.

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
      bool -> AEP -> leakage -> trace -> mem -> locals -> metrics ->
      (bool -> AEP -> leakage -> trace -> mem -> locals -> metrics -> Prop)
    -> Prop :=
    | interact: forall aep k t m mKeep mGive l mc action argvars argvals resvars outcome post,
        map.split m mKeep mGive ->
        map.getmany_of_list l argvars = Some argvals ->
        ext_spec t mGive action argvals outcome ->
        (forall mReceive resvals klist,
            outcome mReceive resvals klist ->
            exists l', map.putmany_of_list_zip resvars resvals l = Some l' /\
            forall m', map.split m' mKeep mReceive ->
            post true aep (leak_list klist :: k) (((mGive, action, argvals), (mReceive, resvals)) :: t) m' l'
                 (cost_interact phase mc)) ->
        exec (SInteract resvars action argvars) true aep k t m l mc post
    | call: forall aep k t m l mc binds fname args params rets fbody argvs st0 post outcome,
        map.get e fname = Some (params, rets, fbody) ->
        map.getmany_of_list l args = Some argvs ->
        map.putmany_of_list_zip params argvs map.empty = Some st0 ->
        exec fbody true aep (leak_unit :: k) t m st0 mc outcome ->
        (forall q' aep' k' t' m' st1 mc',
            outcome q' aep' k' t' m' st1 mc' ->
            if q' then
              exists retvs l',
                map.getmany_of_list st1 rets = Some retvs /\
                  map.putmany_of_list_zip binds retvs l = Some l' /\
                  post q' aep' k' t' m' l' (cost_call phase mc')
            else post q' aep' k' t' m' st1 (cost_call phase mc')) ->
        exec (SCall binds fname args) true aep k t m l mc post
    | load: forall aep k t m l mc sz x a o v addr post,
        map.get l a = Some addr ->
        load sz m (word.add addr (word.of_Z o)) = Some v ->
        post true aep (leak_word (word.add addr (word.of_Z o)) :: k) t m (map.put l x v) (cost_load isReg x a mc)->
        exec (SLoad sz x a o) true aep k t m l mc post
    | store: forall aep k t m m' mc l sz a o addr v val post,
        map.get l a = Some addr ->
        map.get l v = Some val ->
        store sz m (word.add addr (word.of_Z o)) val = Some m' ->
        post true aep (leak_word (word.add addr (word.of_Z o)) :: k) t m' l (cost_store isReg a v mc) ->
        exec (SStore sz a v o) true aep k t m l mc post
    | inlinetable: forall sz x table i v index aep k t m l mc post,
        (* compiled riscv code uses x as a tmp register and this shouldn't overwrite i *)
        x <> i ->
        map.get l i = Some index ->
        load sz (map.of_list_word table) index = Some v ->
        post true aep (leak_word index :: k) t m (map.put l x v) (cost_inlinetable isReg x i mc) ->
        exec (SInlinetable sz x table i) true aep k t m l mc post
    | stackalloc: forall aep k t mSmall l mc x n body post,
        n mod (bytes_per_word width) = 0 ->
        (forall mStack mCombined,
            let a := pick_sp k in
            anybytes a n mStack ->
            map.split mCombined mSmall mStack ->
            exec body true aep (leak_unit :: k) t mCombined (map.put l x a) mc
             (fun q' aep' k' t' mCombined' l' mc' =>
              if q' then exists mSmall' mStack',
                anybytes a n mStack' /\
                map.split mCombined' mSmall' mStack' /\
                  post q' aep' k' t' mSmall' l' (cost_stackalloc isReg x mc')
              else post q' aep' k' t' mCombined' l' (cost_stackalloc isReg x mc'))) ->
        exec (SStackalloc x n body) true aep k t mSmall l mc post
    | lit: forall aep k t m l mc x v post,
        post true aep k t m (map.put l x (word.of_Z v)) (cost_lit isReg x mc) ->
        exec (SLit x v) true aep k t m l mc post
    | op: forall aep k t m l mc x op y y' z z' post,
        map.get l y = Some y' ->
        lookup_op_locals l z = Some z' ->
        post true aep (leak_binop op y' z' ++ k) t m (map.put l x (interp_binop op y' z')) (cost_SOp x y z mc) ->
        exec (SOp x op y z) true aep k t m l mc post
    | set: forall aep k t m l mc x y y' post,
        map.get l y = Some y' ->
        post true aep k t m (map.put l x y') (cost_set isReg x y mc) ->
        exec (SSet x y) true aep k t m l mc post
    | if_true: forall aep k t m l mc cond  bThen bElse post,
        eval_bcond l cond = Some true ->
        exec bThen true aep (leak_bool true :: k) t m l (cost_SIf cond mc) post ->
        exec (SIf cond bThen bElse) true aep k t m l mc post
    | if_false: forall aep k t m l mc cond bThen bElse post,
        eval_bcond l cond = Some false ->
        exec bElse true aep (leak_bool false :: k) t m l (cost_SIf cond mc) post ->
        exec (SIf cond bThen bElse) true aep k t m l mc post
    | loop: forall aep k t m l mc cond body1 body2 mid1 mid2 post,
        (* This case is carefully crafted in such a way that recursive uses of exec
         only appear under forall and ->, but not under exists, /\, \/, to make sure the
         auto-generated induction principle contains an IH for all recursive uses. *)
        exec body1 true aep k t m l mc mid1 ->
        (forall aep' k' t' m' l' mc',
            mid1 true aep' k' t' m' l' mc' ->
            eval_bcond l' cond <> None) ->
        (forall aep' k' t' m' l' mc',
            mid1 true aep' k' t' m' l' mc' ->
            eval_bcond l' cond = Some false ->
            post true aep' (leak_bool false :: k') t' m' l' (cost_SLoop_false cond mc')) ->
        (forall aep' k' t' m' l' mc',
            mid1 true aep' k' t' m' l' mc' ->
            eval_bcond l' cond = Some true ->
            exec body2 true aep' (leak_bool true :: k') t' m' l' mc' mid2) ->
        (forall aep' k' t' m' l' mc',
            mid1 false aep' k' t' m' l' mc' ->
            post false aep' k' t' m' l' mc') ->
        (forall q'' aep'' k'' t'' m'' l'' mc'',
            mid2 q'' aep'' k'' t'' m'' l'' mc'' ->
            exec (SLoop body1 cond body2) q'' aep'' k'' t'' m'' l''
              (cost_SLoop_true cond mc'') post) ->
        exec (SLoop body1 cond body2) true aep k t m l mc post
    | seq: forall aep k t m l mc s1 s2 mid post,
        exec s1 true aep k t m l mc mid ->
        (forall q' aep' k' t' m' l' mc', mid q' aep' k' t' m' l' mc' -> exec s2 q' aep' k' t' m' l' mc' post) ->
        exec (SSeq s1 s2) true aep k t m l mc post
    | skip: forall aep k t m l mc post,
        post true aep k t m l mc ->
        exec SSkip true aep k t m l mc post
    | quit s q aep k t m l mc post
        (_ : post false aep k t m l mc)
      : exec s q aep k t m l mc post
    | exec_A s aep k t m l mc post
        (_ : forall x, exec s true (aep x) k t m l mc post)
      : exec s true (AEP_A aep) k t m l mc post
    | exec_E s aep k t m l mc post x
        (_ : exec s true (aep x) k t m l mc post)
      : exec s true (AEP_E aep) k t m l mc post.

    Lemma weaken {pick_sp: PickSp} : forall s q aep k t m l mc post1,
        exec s q aep k t m l mc post1 ->
        forall post2,
          (forall q' aep' k' t' m' l' mc', post1 q' aep' k' t' m' l' mc' -> post2 q' aep' k' t' m' l' mc') ->
          exec s q aep k t m l mc post2.
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
        destruct q'; [|solve[auto]].
        simp. eauto 10.
      - eapply stackalloc. 1: assumption.
        intros.
        eapply H1; eauto.
        intros. simp. destruct q'; fwd; eauto 10.
    Qed.
    
    Lemma det_step {pick_sp: PickSp} : forall aep0 k0 t0 m0 l0 mc0 s1 s2 q1 aep1 k1 t1 m1 l1 mc1 post,
        exec s1 true aep0 k0 t0 m0 l0 mc0 (fun q1' aep1' k1' t1' m1' l1' mc1' => q1' = q1 /\ aep1' = aep1 /\ k1' = k1 /\ t1' = t1 /\ m1' = m1 /\ l1' = l1 /\ mc1 = mc1') ->
        exec s2 q1 aep1 k1 t1 m1 l1 mc1 post ->
        exec (SSeq s1 s2) true aep0 k0 t0 m0 l0 mc0 post.
    Proof.
      intros.
      eapply seq; [eassumption|].
      intros. simpl in *. simp.
      assumption.
    Qed.

    Lemma loop_cps {pick_sp: PickSp} : forall body1 cond body2 aep k t m l mc post,
        exec body1 true aep k t m l mc
          (fun q aep k t m l mc =>
             if q then
               exists b,
               eval_bcond l cond = Some b /\
                 (b = false -> post q aep (leak_bool false :: k) t m l (cost_SLoop_false cond mc)) /\
                   (b = true -> 
                    exec body2 q aep (leak_bool true :: k) t m l mc
                      (fun q aep k t m l mc =>
                         exec (SLoop body1 cond body2) q aep k t m l
                                     (cost_SLoop_true cond mc) post))
               else post q aep k t m l mc) ->
      exec (SLoop body1 cond body2) true aep k t m l mc post.
    Proof.
      intros. eapply loop. 1: eapply H. all: cbv beta; intros; simp.
      - congruence.
      - replace b with false in * by congruence. clear b. eauto. 
      - replace b with true in * by congruence. clear b. eauto.
      - assumption.
      - simpl in *. destruct q''; [assumption|]. apply quit. inversion H0. subst.
        assumption.
    Qed.

    Fixpoint is_det (s : stmt varname) : Prop :=
      match s with
      | SLoad _ _ _ _ => True
      | SStore _ _ _ _ => True
      | SInlinetable _ _ _ _ => True
      | SStackalloc _ _ _ => False
      | SLit _ _ => True
      | SOp _ _ _ _ => True
      | SSet _ _ => True
      | SIf _ s1 s2 => (*is_det s1 /\ is_det s2*)False
      | SLoop s1 _ s2 => (*is_det s1 /\ is_det s2*)False
      | SSeq s1 s2 => (*is_det s1 /\ is_det s2*)False
      | SSkip => True
      | SCall _ _ _ => False
      | SInteract _ _ _ => False
      end.

    Require Import Coq.Logic.ChoiceFacts.

    Ltac stuff :=
      repeat match goal with
        | H1: ?e = Some (?x1, ?y1, ?z1), H2: ?e = Some (?x2, ?y2, ?z2) |- _ =>
            replace x2 with x1 in * by congruence;
            replace y2 with y1 in * by congruence;
            replace z2 with z1 in * by congruence;
            clear x2 y2 z2 H2
        end;
      repeat match goal with
        | H1: ?e = Some ?v1, H2: ?e = Some ?v2 |- _ =>
            replace v2 with v1 in * by congruence; clear H2
        end.

    Lemma call_cps {pick_sp: PickSp} : forall fname params rets binds args fbody argvs aep k t (l: locals) m mc st post,
        map.get e fname = Some (params, rets, fbody) ->
        map.getmany_of_list l args = Some argvs ->
        map.putmany_of_list_zip params argvs map.empty = Some st ->
        exec fbody true aep (leak_unit :: k) t m st mc
             (fun q' aep' k' t' m' st' mc' =>
                if q' then
                  exists retvs l',
                  map.getmany_of_list st' rets = Some retvs /\
                    map.putmany_of_list_zip binds retvs l = Some l' /\
                    post q' aep' k' t' m' l' (cost_call phase mc')
             else post q' aep' k' t' m' st' (cost_call phase mc')) ->
      exec (SCall binds fname args) true aep k t m l mc post.
    Proof.
      intros. eapply call; try eassumption.
      cbv beta. intros * ?. destruct q'; [|solve[auto]]. fwd. eauto.
    Qed.
    
    Lemma seq_cps {pick_sp: PickSp} : forall s1 s2 aep k t m (l: locals) mc post,
        exec s1 true aep k t m l mc (fun q' aep' k' t' m' l' mc' => exec s2 q' aep' k' t' m' l' mc' post) ->
        exec (SSeq s1 s2) true aep k t m l mc post.
    Proof.
      intros. eapply seq. 1: eassumption. simpl. clear. auto.
    Qed.

    Lemma aep_same {pick_sp: PickSp} : forall q blah k t m l mc s post,
        exec s q (AEP_P blah) k t m l mc post ->
        exec s q (AEP_P blah) k t m l mc (fun q' aep' k' t' m' l' mc' =>
                                            aep' = AEP_P blah /\ post q' aep' k' t' m' l' mc').
    Proof.
      intros. remember (AEP_P _) as blagh. revert Heqblagh.
      induction H; intros; subst; try solve [econstructor; eauto; simpl; intros; fwd; eauto].
      - econstructor; eauto. intros * H'. specialize H2 with (1 := H'). fwd. eauto.
      - eapply call_cps; eauto. eapply weaken. 1: clear H2; eauto. simpl. intros. fwd.
        apply H3 in H4p1. destruct q'; fwd; intuition eauto 20.
      - econstructor; eauto. intros. eapply weaken. 1: eapply H1; eauto. simpl.
        intros. fwd. destruct q'; fwd; eauto 20.
      - apply loop_cps. eapply weaken. 1: apply IHexec; auto. simpl. intros. fwd.
        destruct q'; [|solve[auto]]. Search mid1. specialize H0 with (1 := H7p1).
        destruct (eval_bcond _ _) eqn:E; [|congruence]. eexists.
        split; [reflexivity|split; intros; subst].
        + auto.
        + Search body2. Search body2. clear H2. eapply weaken. 1: eauto. simpl. intros.
          fwd. eauto.
      - apply seq_cps. clear H H0. eapply weaken; eauto. simpl. intros. fwd. eauto.
      - congruence.
      - congruence.
    Qed.
        
    Axiom choice : forall x y, FunctionalChoice_on x y.
   Lemma intersect {pick_sp: PickSp} : forall q blah0 k t m l mc s (postx : _ -> _ -> _ -> _ -> _ -> _ -> Prop),
        (forall (x : nat), exec s q (AEP_P blah0) k t m l mc (fun q' aep' k' t' m' l' mc' => q' = true /\ postx x k' t' m' l' mc')) ->
        forall blah, exec s q (AEP_P blah) k t m l mc (fun q' aep' k' t' m' l' mc' =>
                                            q' = true /\ forall x, postx x k' t' m' l' mc').
    Proof.
      intros. pose proof (H O) as H0. remember (fun q' aep' k' t' m' l' mc' => _) as post.
      assert (Hpost: forall q' aep' k' t' m' l' mc', post q' aep' k' t' m' l' mc' -> q' = true) by (subst; intros; fwd; auto).
      clear Heqpost. remember (AEP_P blah0) as aep. revert Hpost postx Heqaep H.
      induction H0; intros Hpost postx Haep Hx; subst.
      - eassert (exists f, _) as Hf.
        { apply choice. intros x. specialize (Hx x). inversion Hx; subst.
          2: { fwd. congruence. }
          rewrite H0 in H7. inversion H7. subst.
          pose proof ext_spec.mGive_unique as P.
          specialize P with (1 := H) (2 := H6) (3 := H1) (4 := H8). subst mGive0.
          destruct (map.split_diff (map.same_domain_refl mGive) H H6) as (? & _).
          subst mKeep0.
          exists outcome0. exact (conj H8 H16). }
        destruct Hf as [f Hf].
        econstructor. 1: eassumption. 1: eassumption.
        { eapply ext_spec.intersect with (post := f). intros x. specialize (Hf x).
          fwd. assumption. }
        simpl. intros. pose proof (H3 O) as H3'. pose proof (Hf O) as [Hf'1 Hf'2].
        specialize Hf'2 with (1 := H3'). fwd. eexists. split; [eassumption|]. intros.
        intuition. specialize (Hf x). specialize (H3 x).
        fwd. specialize Hfp1 with (1 := H3). fwd. rewrite Hfp1p0 in Hf'2p0.
        inversion Hf'2p0; subst; clear Hf'2p0. edestruct Hfp1p1; fwd; eassumption.
      - specialize IHexec with (2 := eq_refl). pose proof (Hx O) as HxO.
        inversion HxO; subst; [|fwd; congruence]. stuff.
        econstructor; eauto.
        { eapply IHexec.
          { intros * Hout. apply H3 in Hout. destruct q'; fwd; eauto. }
          intros. move Hx at bottom. specialize (Hx x).
          inversion Hx; subst; [|fwd; congruence].
          stuff.
          eapply weaken. 1: exact H11. intros * H4. specialize H20 with (1 := H4).
          destruct q'; [|fwd; congruence].
          split; [reflexivity|]. fwd. intuition.
          instantiate (1 := fun _ _ _ _ _ _ => exists retvs l'0, _ /\ _ /\ _). simpl.
          exists retvs, l'0. ssplit; [exact H20p0|exact H20p1|exact H20p3]. }
        simpl. intros. fwd. pose proof (H4p1 O) as HO. fwd. eexists. eexists.
        intuition eauto. specialize (H4p1 x). fwd. stuff. assumption.
      - econstructor; eauto. intuition. specialize (Hx x0).
        inversion Hx; subst; [|fwd; congruence]. fwd. stuff. assumption.
      - econstructor; eauto. intuition. specialize (Hx x).
        inversion Hx; subst; [|fwd; congruence]. fwd. stuff. assumption.
      - econstructor; eauto. intuition. specialize (Hx x0).
        inversion Hx; subst; [|fwd; congruence]. fwd. stuff. assumption.
      - econstructor; eauto. intros. eapply weaken.
        { eapply H1; eauto.
          { intros * Hmid. destruct q'; fwd; eauto. }
          intros x0. specialize (Hx x0).
          inversion Hx; subst; [|fwd; congruence].
          specialize (H15 _ _ ltac:(eassumption) ltac:(eassumption)). eapply weaken.
          1: eapply H15. simpl. intros. destruct q'; [|fwd; congruence]. fwd.
          intuition. instantiate (1 := fun _ _ _ _ _ _ => exists _ _, _ /\ _ /\ _).
          exists mSmall', mStack'. ssplit; [exact H4p0|exact H4p1|exact H4p3]. }
        simpl. intros. fwd. pose proof (H4p1 O) as HO. fwd. eexists. eexists.
        intuition eauto. specialize (H4p1 x0). fwd.
        lazymatch goal with
        | A: map.split _ _ _, B: map.split _ _ _ |- _ =>
            specialize @map.split_diff with (4 := A) (5 := B) as P
        end.
        edestruct P; try typeclasses eauto. 2: subst; eauto 10.
        eapply anybytes_unique_domain; eassumption.
      - econstructor; eauto. intuition. specialize (Hx x0).
        inversion Hx; subst; [|fwd; congruence]. fwd. stuff. assumption.
      - econstructor; eauto. intuition. specialize (Hx x0).
        inversion Hx; subst; [|fwd; congruence]. fwd. stuff. assumption.
      - econstructor; eauto. intuition. specialize (Hx x0).
        inversion Hx; subst; [|fwd; congruence]. fwd. stuff. assumption.
      - econstructor; eauto. apply IHexec; auto. intros x. specialize (Hx x).
        inversion Hx; subst; [|congruence|fwd; congruence]. assumption.
      - eapply if_false; eauto. apply IHexec; auto. intros x. specialize (Hx x).
        inversion Hx; subst; [congruence| |fwd; congruence]. assumption.
      - apply loop_cps. eapply weaken.
        { apply aep_same. eapply IHexec; eauto.
          { intros. destruct q' eqn:E; [reflexivity|]. eauto. }
          intros x. 
          instantiate (1 := fun x _ _ _ _ _ => match x with | O => _ | _ => _ end).
          destruct x.
          - eapply weaken.
            { apply aep_same. exact H0. }
            simpl. intros. fwd. destruct q'.
            + split; [reflexivity|]. exact H7p1.
            + Search mid1. apply H4 in H7p1. apply Hpost in H7p1. congruence.
          - specialize (Hx x).
            inversion Hx; subst; [|fwd; congruence]. eapply weaken.
            { apply aep_same. Check IHexec. exact H10. }
            simpl. intros. fwd. destruct q'.
            + split; [reflexivity|]. Search (mid0 true). specialize H11 with (1 := H7p1).
              Search (mid0 true). specialize H13 with (1 := H7p1). Search (mid0 true).
              specialize H12 with (1 := H7p1).
              simpl. instantiate (1 := exists mid3, _). exists mid3.
              exact (conj H11 (conj H13 (conj H12 H22))).
            + Search mid0. apply H14 in H7p1. fwd. congruence. }
        simpl. intros. fwd. pose proof (H7p2 O) as Hmid1. pose proof (H7p2 (S O)) as HO.
        simpl in *. fwd.
        destruct (eval_bcond _ _) eqn:E; [|congruence]. eexists. split; [reflexivity|].
        split; intros; subst.
        + clear HOp1 HOp0 HOp2 HOp3 mid3. intuition. specialize (H7p2 (S x)).
          simpl in H7p2. fwd. specialize (H7p2p2 eq_refl). fwd. assumption.
        + clear HOp1 HOp0 HOp2 HOp3 mid3. eapply weaken.
          { apply aep_same. eapply H3; eauto.
            - intros. destruct q'; [reflexivity|]. Search mid2. apply H5 in H7.
              inversion H7. subst. Search post. apply Hpost in H8. congruence.
            - instantiate (1 := fun x _ _ _ _ _ => match x with | O => _ | _ => _ end).
              intros x. destruct x.
              + eapply weaken.
                { apply aep_same. eauto. }
                simpl. intros. fwd. destruct q'.
                -- split; [reflexivity|]. exact H7p1.
                -- Search mid2. apply H5 in H7p1. inversion H7p1. subst.
                   apply Hpost in H7. congruence.
              + specialize (H7p2 (S x)). simpl in H7p2. fwd. Search mid3.
                eapply weaken.
                { apply aep_same. apply H7p2p1. reflexivity. }
                simpl. intros. fwd. apply H7p2p3 in H7p1. destruct q'.
                2: { inversion H7p1. subst. fwd. congruence. }
                split; [reflexivity|]. exact H7p1. }
          simpl. intros. fwd. eapply H6; eauto.
          -- apply (H7p3 O).
          -- exact (fun x => H7p3 (S x)).
      - 
        

    Lemma det_invert {pick_sp: PickSp} : forall q aep k t m l mc s post,
        is_det s ->
        exec s q aep k t m l mc post ->
        (forall q' aep' k' t' m' l' mc', post q' aep' k' t' m' l' mc' -> q' = true) ->
        exists inp, forall blah,
          exec s q (AEP_P blah) k t m l mc
            (fun q' _ k' t' m' l' mc' =>
               forall aep',
                 goes_to aep inp aep' ->
                 post q' aep' k' t' m' l' mc').
    Proof.
      intros * Hdet Hexec. revert Hdet.
      induction Hexec; try solve [intros []]; simpl; intros Hdet.
      all: try (exists inp_nil; intros; econstructor; eauto; intros aep' gt; inversion gt; subst; assumption).
      - specialize H0 with (1 := Hdet). Print FunctionalChoice_on. eassert (exists f, _).
        { apply choice. intros x. specialize (H0 x). destruct H0 as [inp H0].
          exists inp. exact H0. }
        clear H0. simpl in H1. destruct H1 as [f H1]. exists (inp_A f). intros.
        { destruct H1 as [f H1]. exists (inp_A f). apply H1. }
        apply choice.

    Lemma seq_assoc {pick_sp: PickSp} : forall s1 s2 s3 aep k t m l mc post,
        exec (SSeq s1 (SSeq s2 s3)) true aep k t m l mc post ->
        exec (SSeq (SSeq s1 s2) s3) true aep k t m l mc post.
    Proof.
      intros. remember (SSeq s1 _) as s. revert s1 s2 s3 Heqs.
      induction H; intros ? ? ? Hs; inversion Hs; subst.
      - eapply seq_cps.
        eapply seq_cps.
        eapply weaken. 1: eassumption. intros. apply H0 in H2. clear H1 IHexec H0 Hs.
        remember (SSeq s3 s4) as s. revert s3 s4 Heqs.
        induction H2; intros ? ? Hs; inversion Hs; subst.
        + eapply weaken. 1: eassumption. auto.
        + apply quit. apply quit. assumption.
        + apply exec_A. intros. apply H1. reflexivity.
        + eapply exec_E. eapply IHexec. reflexivity.
      - apply quit. assumption.
      - apply exec_A. intros. apply H0. reflexivity.
      - eapply exec_E. eapply IHexec. reflexivity.
    Qed.

    (*i don't want to*)
    (* Lemma seq_assoc_bw {pick_sp: PickSp} : forall s1 s2 s3 k t m l mc post, *)
    (*     exec (SSeq (SSeq s1 s2) s3) k t m l mc post -> *)
    (*     exec (SSeq s1 (SSeq s2 s3)) k t m l mc post. *)
    (* Proof. intros. simp. eauto 10 using seq. Qed. *)

    Ltac equalities :=
      repeat match goal with
             | H1: ?e = ?e1, H2: ?e = ?e2 |- _ =>
               progress (let H := fresh in assert (e1 = e2) as H by congruence; ensure_new H; simp)
             | H1: ?P, H2: ?P |- _ => clear H2
             end;
      simp.
    
    (* (*not true*) *)
    (* Lemma intersect {pick_sp: PickSp} : forall k t m l mc s post1, *)
    (*     exec s k t m l mc post1 -> *)
    (*     forall post2, *)
    (*       exec s k t m l mc post2 -> *)
    (*       exec s k t m l mc (fun k' t' m' l' mc' => post1 k' t' m' l' mc' /\ post2 k' t' m' l' mc'). *)
    (* Proof. *)
    (*   induction 1; intros; *)
    (*     match goal with *)
    (*     | H: exec _ _ _ _ _ _ _ |- _ => inversion H; subst; clear H *)
    (*     end; *)
    (*     equalities; *)
    (*     try solve [econstructor; eauto | exfalso; congruence]. *)

    (*   - (* SInteract *) *)
    (*     pose proof ext_spec.mGive_unique as P. *)
    (*     specialize P with (1 := H) (2 := H7) (3 := H1) (4 := H15). *)
    (*     subst mGive0. *)
    (*     destruct (map.split_diff (map.same_domain_refl mGive) H H7) as (? & _). *)
    (*     subst mKeep0. *)
    (*     eapply @interact. *)
    (*     + eassumption. *)
    (*     + eassumption. *)
    (*     + eapply ext_spec.intersect; [exact H1|exact H15]. *)
    (*     + simpl. intros. simp. *)
    (*       edestruct H2 as (? & ? & ?); [eassumption|]. *)
    (*       edestruct H16 as (? & ? & ?); [eassumption|]. *)
    (*       simp. *)
    (*       equalities. *)
    (*       eauto 10. *)

    (*   - (* SCall *) *)
    (*     rename IHexec into IH. *)
    (*     specialize IH with (1 := H17). *)
    (*     eapply @call; [..|exact IH|]; eauto. *)
    (*     rename H3 into Ex1. *)
    (*     rename H18 into Ex2. *)
    (*     move Ex1 before Ex2. *)
    (*     intros. simpl in *. simp. *)
    (*     edestruct Ex1; [eassumption|]. *)
    (*     edestruct Ex2; [eassumption|]. *)
    (*     simp. *)
    (*     equalities. *)
    (*     eauto 10. *)

    (*   - (* SStackalloc *) *)
    (*     eapply @stackalloc. 1: eassumption. *)
    (*     intros. *)
    (*     rename H0 into Ex1, H13 into Ex2. *)
    (*     eapply weaken. 1: eapply H1. 1,2: eassumption. *)
    (*     1: eapply Ex2. 1,2: eassumption. *)
    (*     cbv beta. *)
    (*     intros. simp. *)
    (*     lazymatch goal with *)
    (*       | A: map.split _ _ _, B: map.split _ _ _ |- _ => *)
    (*         specialize @map.split_diff with (4 := A) (5 := B) as P *)
    (*     end. *)
    (*     edestruct P; try typeclasses eauto. 2: subst; eauto 10. *)
    (*     eapply anybytes_unique_domain; eassumption. *)

    (*   - (* SLoop *) *)
    (*     eapply @loop. *)
    (*     + eapply IHexec. exact H10. *)
    (*     + simpl. intros. simp. eauto. *)
    (*     + simpl. intros. simp. eauto. *)
    (*     + simpl. intros. simp. eapply H3; [eassumption..|]. (* also an IH *) *)
    (*       eapply H19; eassumption. *)
    (*     + simpl. intros. simp. eapply H5; [eassumption..|]. (* also an IH *) *)
    (*       eapply H20; eassumption. *)

    (*   - (* SSeq *) *)
    (*     pose proof IHexec as IH1. *)
    (*     specialize IH1 with (1 := H5). *)
    (*     eapply @seq; [exact IH1|]. *)
    (*     intros; simpl in *. *)
    (*     destruct H2. *)
    (*     eauto. *)
    (* Qed. *)

    Lemma exec_extends_trace {pick_sp: PickSp} s q aep k t m l mc post :
      exec s q aep k t m l mc post ->
      exec s q aep k t m l mc (fun q' aep' k' t' m' l' mc' => post q' aep' k' t' m' l' mc' /\ exists k'', k' = k'' ++ k).
    Proof.
      intros H. induction H; try (econstructor; intuition eauto; eexists; align_trace; fail).
      - econstructor; intuition eauto. specialize H2 with (1 := H3). fwd.
        eexists. intuition eauto. eexists. align_trace.
      - econstructor; intuition eauto. fwd. specialize H3 with (1 := H4p0). fwd.
        destruct q'.
        + fwd. eexists. eexists. intuition eauto. eexists. align_trace.
        + intuition. eexists. align_trace.
      - econstructor; intuition eauto. intros. eapply weaken. 1: eapply H1; eauto.
        simpl. intros. fwd. destruct q'.
        + fwd. eexists. eexists. intuition eauto. eexists. align_trace.
        + intuition. eexists. align_trace.
      - eapply if_true; intuition eauto. eapply weaken. 1: eapply IHexec.
        simpl. intros. fwd. intuition eauto. eexists. align_trace.
      - eapply if_false; intuition eauto. eapply weaken. 1: eapply IHexec.
        simpl. intros. fwd. intuition eauto. eexists. align_trace.
      - clear H2 H5. eapply loop_cps. eapply weaken. 1: exact IHexec. simpl. intros. fwd.
        destruct q'.
        + specialize H0 with (1 := H2p0). specialize H1 with (1 := H2p0).
          specialize H3 with (1 := H2p0). destruct (eval_bcond l' cond); [|congruence].
          exists b. intuition; subst; auto.
          -- eexists. align_trace.
          -- eapply weaken. 1: eapply H3; auto. simpl. intros. fwd.
             eapply weaken. 1: eapply H6; eauto. simpl. intros. fwd. intuition.
             eexists. align_trace.
        + intuition. eexists. align_trace.
      - econstructor; intuition eauto. fwd. eapply weaken. 1: eapply H1; eauto.
        simpl. intros. fwd. intuition eauto. eexists. align_trace.
    Qed.

    Lemma exec_ext (pick_sp1: PickSp) s q aep k t m l mc post :
      exec (pick_sp := pick_sp1) s q aep k t m l mc post ->
      forall pick_sp2,
        (forall k', pick_sp1 (k' ++ k) = pick_sp2 (k' ++ k)) ->
        exec (pick_sp := pick_sp2) s q aep k t m l mc post.
    Proof.
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
      - clear H2 H5. eapply loop. 1: eapply exec_extends_trace. all: intuition eauto; fwd; eauto.
        { eapply weaken. 1: eapply exec_extends_trace.
          { eapply H3; eauto.
            intros. rewrite associate_one_left. repeat rewrite app_assoc. auto. }
          simpl. intros. fwd.
          instantiate (1 := fun q'0 aep'0 k'0 t'0 m'0 l'0 mc'0 =>
                              mid2 q'0 aep'0 k'0 t'0 m'0 l'0 mc'0 /\ exists k'', k'0 = k'' ++ k).
          simpl. intuition eauto. eexists. align_trace. }
        simpl in *. fwd. eapply H6; eauto. intros.
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

    Lemma exec_to_other_trace (pick_sp: PickSp) s q aep k1 k2 t m l mc post :
      exec s q aep k1 t m l mc post ->
      exec (pick_sp := fun k => pick_sp (rev (skipn (length k2) (rev k)) ++ k1))
        s q aep k2 t m l mc (fun q' aep' k2' t' m' l' mc' =>
                         exists k'',
                           k2' = k'' ++ k2 /\
                             post q' aep' (k'' ++ k1) t' m' l' mc').
    Proof.
      intros H. generalize dependent k2. induction H; intros.
      - econstructor; intuition eauto. apply H2 in H3. fwd.
        eexists. intuition eauto. eexists. intuition eauto. 1: align_trace.
        auto.
      - econstructor; intuition eauto.
        { eapply exec_ext with (pick_sp1 := _). 1: eapply IHexec; eauto. solve_picksps_equal. }
        cbv beta in *. fwd. apply H3 in H4p1. destruct q'.
        + fwd. eexists. intuition eauto. eexists. intuition eauto. eexists.
          split; [align_trace|]. repeat rewrite <- app_assoc. auto.
        + eexists. split; [align_trace|]. rewrite <- app_assoc. assumption.
      - econstructor; intuition eauto. eexists. split; [align_trace|]. auto.
      - econstructor; intuition eauto. eexists. split; [align_trace|]. auto.
      - econstructor; intuition eauto. eexists. split; [align_trace|]. auto.
      - econstructor; intuition eauto. intros.
        replace (rev k2) with (rev k2 ++ nil) in * by apply app_nil_r.
        rewrite List.skipn_app_r in * by (rewrite rev_length; reflexivity).
        simpl in *. eapply weaken.
        { eapply exec_ext with (pick_sp1 := _). 1: eapply H1; eauto. solve_picksps_equal. }
        simpl. intros. fwd. destruct q'.
        + fwd. eexists _, _. intuition eauto. eexists (_ ++ _ :: nil).
          rewrite <- app_assoc. simpl. rewrite <- (app_assoc _ _ k). simpl. eauto.
        + eexists. split; [align_trace|]. rewrite <- app_assoc. assumption.
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
            instantiate (1 := fun q'0 aep'0 k'0 t'0 m'0 l'0 mc'0 =>
                                exists k''0,
                                  k'0 = k''0 ++ k2 /\
                                    mid2 q'0 aep'0 (k''0 ++ k) t'0 m'0 l'0 mc'0).
            fwd. eexists. split; [align_trace|].
            repeat rewrite <- app_assoc. simpl. auto. }
          solve_picksps_equal. }
        simpl in *. fwd. eapply exec_ext with (pick_sp1 := _).
        { eapply weaken. 1: eapply H6; eauto. simpl. intros. fwd.
          eexists. split; [align_trace|].
          repeat rewrite <- app_assoc. auto. }
        solve_picksps_equal.
      - econstructor; intuition. fwd. eapply weaken.
        { eapply exec_ext with (pick_sp1 := _). 1: eapply H1; eauto. solve_picksps_equal. }
        simpl. intros. fwd. eexists. split; [align_trace|].
        repeat rewrite <- app_assoc. auto.
      - econstructor. eexists. split; [align_trace|]. assumption.
      - econstructor. exists nil. split; [align_trace|]. auto.
      - apply exec_A. auto.
      - eapply exec_E. eauto.
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
  
  Definition SimState: Type := bool * AEP * leakage * trace * mem * locals * MetricLog.
  Definition SimExec(e: env)(c: stmt varname): SimState -> (SimState -> Prop) -> Prop :=
    fun '(q, aep, k, t, m, l, mc) post =>
      exec phase isReg e c q aep k t m l mc (fun q' aep' k' t' m' l' mc' => post (q', aep', k', t', m', l', mc')).

  Lemma modVarsSound: forall e s initialQ initialAEP initialK initialT initialSt initialM initialMc post,
      exec phase isReg e s initialQ initialAEP initialK initialT initialM initialSt initialMc post ->
      exec phase isReg e s initialQ initialAEP initialK initialT initialM initialSt initialMc
        (fun finalQ finalAEP finalK finalT finalM finalSt finalMc => post finalQ finalAEP finalK finalT finalM finalSt finalMc /\ (finalQ = true -> initialQ = true /\ map.only_differ initialSt (modVars s) finalSt)).
  Proof.
    induction 1;
      try solve [ econstructor; [eassumption..|intuition auto; simpl; map_solver locals_ok] ].
    - eapply exec.interact; try eassumption.
      intros; simp.
      edestruct H2; try eassumption. simp.
      eexists; split; [eassumption|].
      simpl. try split; eauto.
      intros. intuition.
      eapply map.only_differ_putmany. eassumption.
    - eapply exec.call. 4: exact H2. (* don't pick IHexec! *) all: try eassumption.
      intros; simpl in *; simp. apply H3 in H4. destruct q'.
      + fwd. do 2 eexists; intuition eauto. eapply map.only_differ_putmany. eassumption.
      + intuition congruence.
    - eapply exec.stackalloc; try eassumption.
      intros.
      eapply exec.weaken.
      + eapply H1; eassumption.
      + simpl. intros. simp.
        destruct q'.
        -- specialize (H4p1 eq_refl). fwd. do 2 eexists. split; [eassumption|].
           split; [eassumption|]. intuition auto. map_solver locals_ok.
        -- intuition congruence.
    - eapply exec.if_true; try eassumption.
      eapply exec.weaken; [eassumption|].
      simpl; intros. intuition auto. map_solver locals_ok.
    - eapply exec.if_false; try eassumption.
      eapply exec.weaken; [eassumption|].
      simpl; intros. intuition auto. map_solver locals_ok.
    - clear H. apply exec.loop_cps. eapply exec.weaken. 1: eassumption.
      simpl. intros. fwd. destruct q'. 
      + repeat match goal with | H : _ |- _ => specialize H with (1 := Hp0); move H at bottom end.
        destruct (eval_bcond l' cond); try congruence. exists b. split; [reflexivity|]. split.
        -- intros. subst. intuition auto. map_solver locals_ok.
        -- intros. subst. eapply exec.weaken. 1: eapply H3; auto. simpl. intros.
           fwd. apply H6 in Hp2. eapply exec.weaken. 1: eapply Hp2.
           simpl. intros. fwd. intuition auto. map_solver locals_ok.
      + intuition. congruence.
    - eapply exec.seq.
      + eassumption.
      + simpl; intros. simp.
        eapply exec.weaken; [eapply H1; eauto|].
        simpl; intros. intuition auto.
        map_solver locals_ok.
    - apply exec.quit. intuition congruence.
    - eapply exec.exec_E. eauto.
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

