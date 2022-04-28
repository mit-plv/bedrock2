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
Require Import coqutil.Word.Bitwidth.
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

  Local Arguments Z.add _ _ : simpl never.

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
      | SOp x _ y z => and (P_vars x) (and (P_vars y) (P_vars z))
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
    induction s; intros; simpl in *; intuition eauto using ForallVars_bcond_impl, Forall_impl.
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
  Context {ext_spec: ExtSpec}.

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
        match map.get st x with
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
        exec fbody t m st0 (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc)))) outcome ->
        (forall t' m' mc' st1,
            outcome t' m' st1 mc' ->
            exists retvs l',
              map.getmany_of_list st1 rets = Some retvs /\
              map.putmany_of_list_zip binds retvs l = Some l' /\
              post t' m' l' (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc'))))) ->
        exec (SCall binds fname args) t m l mc post
        (* TODO think about a non-fixed bound on the cost of function preamble and postamble *)
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

    Lemma seq_cps: forall s1 s2 t m (l: locals) mc post,
        exec s1 t m l mc (fun t' m' l' mc' => exec s2 t' m' l' mc' post) ->
        exec (SSeq s1 s2) t m l mc post.
    Proof.
      intros. eapply seq. 1: eassumption. simpl. clear. auto.
    Qed.

    Lemma call_cps: forall fname params rets binds args fbody argvs t (l: locals) m mc st post,
        map.get e fname = Some (params, rets, fbody) ->
        map.getmany_of_list l args = Some argvs ->
        map.putmany_of_list_zip params argvs map.empty = Some st ->
        exec fbody t m st (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc))))
             (fun t' m' st' mc' =>
                exists retvs l',
                  map.getmany_of_list st' rets = Some retvs /\
                    map.putmany_of_list_zip binds retvs l = Some l' /\
                    post t' m' l' (addMetricInstructions 100 (addMetricJumps 100 (addMetricLoads 100 (addMetricStores 100 mc'))))) ->
      exec (SCall binds fname args) t m l mc post.
    Proof.
      intros. eapply call; try eassumption.
      cbv beta. intros *. exact id.
    Qed.

    Lemma loop_cps: forall body1 cond body2 t m l mc post,
      exec body1 t m l mc (fun t m l mc => exists b,
        eval_bcond l cond = Some b /\
        (b = false -> post t m l (addMetricLoads 1 (addMetricInstructions 1 (addMetricJumps 1 mc)))) /\
        (b = true -> exec body2 t m l mc (fun t m l mc =>
           exec (SLoop body1 cond body2) t m l
                (addMetricLoads 2 (addMetricInstructions 2 (addMetricJumps 1 mc))) post))) ->
      exec (SLoop body1 cond body2) t m l mc post.
    Proof.
      intros. eapply loop. 1: eapply H. all: cbv beta; intros; simp.
      - congruence.
      - replace b with false in * by congruence. clear b. eauto.
      - replace b with true in * by congruence. clear b. eauto.
      - assumption.
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

    Lemma seq_assoc: forall s1 s2 s3 t m l mc post,
        exec (SSeq s1 (SSeq s2 s3)) t m l mc post ->
        exec (SSeq (SSeq s1 s2) s3) t m l mc post.
    Proof.
      intros. simp.
      eapply seq_cps.
      eapply seq_cps.
      eapply weaken. 1: eassumption. intros.
      specialize H8 with (1 := H). simp.
      eapply weaken. 1: eassumption. intros.
      eauto.
    Qed.

    Lemma seq_assoc_bw: forall s1 s2 s3 t m l mc post,
        exec (SSeq (SSeq s1 s2) s3) t m l mc post ->
        exec (SSeq s1 (SSeq s2 s3)) t m l mc post.
    Proof. intros. simp. eauto 10 using seq. Qed.

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

Section FlatImp2.
  Context (varname: Type).
  Context {varname_eqb: varname -> varname -> bool}.
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

  Definition SimState: Type := trace * mem * locals * MetricLog.
  Definition SimExec(e: env)(c: stmt varname): SimState -> (SimState -> Prop) -> Prop :=
    fun '(t, m, l, mc) post =>
      exec e c t m l mc (fun t' m' l' mc' => post (t', m', l', mc')).

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
    - eapply @exec.loop with
          (mid1 := fun t' m' l' mc' => mid1 t' m' l' mc' /\
                                   map.only_differ l (modVars body1) l')
          (mid2 := fun t' m' l' mc' => mid2 t' m' l' mc' /\
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
    - eapply @exec.seq with
          (mid := fun t' m' l' mc' => mid t' m' l' mc' /\ map.only_differ l (modVars s1) l').
      + eapply exec.intersect; eassumption.
      + simpl; intros. simp.
        eapply exec.weaken; [eapply H1; eauto|].
        simpl; intros.
        map_solver locals_ok.
  Qed.

End FlatImp2.
