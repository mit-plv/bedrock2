(* -*- eval: (load-file "live_verif_setup.el"); -*- *)
Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Z.Lia.
Require Import coqutil.Byte coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Datatypes.Inhabited.
Require Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.rewr coqutil.Tactics.rdelta.
Require Import Coq.Program.Tactics.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.autoforward.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.OfListWord.
Require coqutil.Map.SortedListString. (* for function env, other maps are kept abstract *)
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import bedrock2.groundcbv.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic bedrock2.Loops.
Require Import coqutil.Word.Bitwidth32.
Require Import Coq.Strings.String.
Require Import bedrock2.TacticError.
Require Import bedrock2Examples.LiveVerif.string_to_ident.
Require Import bedrock2.ident_to_string.
Require Import bedrock2.SepAutoArray bedrock2.SepAutoExports.
Require Import bedrock2.OperatorOverloading.
Local Open Scope oo_scope.
Close Scope sepcl_scope.

(* `vpattern x in H` is like `pattern x in H`, but x must be a variable and is
   used as the binder in the lambda being created *)
Ltac vpattern_in x H :=
  pattern x in H;
  lazymatch type of H with
  | ?f x => change ((fun x => ltac:(let r := eval cbv beta in (f x) in exact r)) x) in H
  end.
Tactic Notation "vpattern" ident(x) "in" ident(H) := vpattern_in x H.


Definition dlet{A B: Type}(rhs: A)(body: A -> B): B := body rhs.


Fixpoint ands(Ps: list Prop): Prop :=
  match Ps with
  | P :: rest => P /\ ands rest
  | nil => True
  end.

Lemma ands_nil: ands nil. Proof. cbn. auto. Qed.
Lemma ands_cons: forall [P: Prop] [Ps: list Prop], P -> ands Ps -> ands (P :: Ps).
Proof. cbn. auto. Qed.

Inductive get_option{A: Type}: option A -> (A -> Prop) -> Prop :=
| mk_get_option: forall (a: A) (post: A -> Prop), post a -> get_option (Some a) post.

Section SepLog.
  Context {width: Z} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma load_of_sep_cps: forall sz addr value (R: mem -> Prop) m (post: word -> Prop),
      (truncated_word sz addr value * R) m /\ post (truncate_word sz value) ->
      get_option (Memory.load sz m addr) post.
  Proof.
    intros. destruct H. eapply load_of_sep in H. rewrite H.
    constructor. assumption.
  Qed.

  Lemma load_word_of_sep_cps: forall addr value (R: mem -> Prop) m (post: word -> Prop),
      (addr ~> value * R) m /\ post value ->
      get_option (Memory.load Syntax.access_size.word m addr) post.
  Proof.
    intros. destruct H. eapply load_word_of_sep in H. rewrite H.
    constructor. assumption.
  Qed.

  Lemma store_truncated_word_of_sep_cps:
    forall (addr oldvalue newvalue: word) sz (R: mem -> Prop) m (post: mem -> Prop),
      (truncated_word sz addr oldvalue * R) m /\
      (forall m', (truncated_word sz addr newvalue * R) m' -> post m') ->
      get_option (Memory.store sz m addr newvalue) post.
  Proof.
    intros. destruct H. eapply Scalars.store_of_sep in H. 2: eassumption.
    destruct H as (m1 & E & P). rewrite E. constructor. exact P.
  Qed.

  Lemma store_byte_of_sep_cps: forall (addr: word) (oldvalue: byte) (newvalue: word)
                                      (R: mem -> Prop) (m: mem) (post: mem -> Prop),
      (ptsto addr oldvalue * R) m /\
      (forall m', (ptsto addr (byte.of_Z (word.unsigned newvalue)) * R) m' -> post m') ->
      get_option (Memory.store access_size.one m addr newvalue) post.
  Proof.
    intros. destruct H. eapply store_one_of_sep in H. 2: eassumption.
    destruct H as (m1 & E & P). rewrite E. constructor. exact P.
  Qed.

  Lemma store_word_of_sep_cps:
    forall (addr oldvalue newvalue: word) (R: mem -> Prop) m (post: mem -> Prop),
      (scalar addr oldvalue * R) m /\
      (forall m', (scalar addr newvalue * R) m' -> post m') ->
      get_option (Memory.store access_size.word m addr newvalue) post.
  Proof.
    intros. eapply store_truncated_word_of_sep_cps. eassumption.
  Qed.
End SepLog.

Section WithParams.
  Import bedrock2.Syntax.
  Context {word: word.word 32} {mem: map.map word byte} {locals: map.map string word}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {locals_ok: map.ok locals}.
  Context {ext_spec: ExtSpec} {ext_spec_ok : ext_spec.ok ext_spec}.

  (* non-unfoldable wrappers, their definition might be swapped with something else later,
     as long as it satisfies the lemmas that follow below *)

  Inductive wp_expr(m: mem)(l: locals)(e: expr)(post: word -> Prop): Prop :=
    mk_wp_expr: WeakestPrecondition.expr m l e post -> wp_expr m l e post.

  Definition wp_exprs(m: mem)(l: locals): list expr -> (list word -> Prop) -> Prop :=
    fix rec es post :=
      match es with
      | nil => post nil
      | cons e rest => wp_expr m l e (fun v => rec rest (fun vs => post (cons v vs)))
      end.

  Lemma wp_var: forall m l x v (post: word -> Prop),
      map.get l x = Some v ->
      post v ->
      wp_expr m l (expr.var x) post.
  Proof.
    intros. constructor. cbn. unfold WeakestPrecondition.get. eauto.
  Qed.

  Lemma wp_literal: forall m l z (post: word -> Prop),
      post (word.of_Z z) ->
      wp_expr m l (expr.literal z) post.
  Proof. intros. constructor. assumption. Qed.

  Lemma weaken_wp_expr: forall m l e (post1 post2: word -> Prop),
      wp_expr m l e post1 ->
      (forall v, post1 v -> post2 v) ->
      wp_expr m l e post2.
  Proof.
    intros. constructor. inversion H.
    eapply WeakestPreconditionProperties.Proper_expr; eassumption.
  Qed.

  Lemma wp_ite: forall m l c e1 e2 (post: word -> Prop),
      wp_expr m l c (fun b => exists v1 v2,
        (if Z.eqb (word.unsigned b) 0 then wp_expr m l e2 (eq v2) else wp_expr m l e1 (eq v1)) /\
        (post (if Z.eqb (word.unsigned b) 0 then v1 else v2))) ->
      wp_expr m l (expr.ite c e1 e2) post.
  Admitted.

  Lemma wp_lazy_and: forall m l e1 e2 (post: word -> Prop),
      wp_expr m l e1 (fun b1 => exists b,
        (if Z.eqb (word.unsigned b1) 0 then b = word.of_Z 0 else wp_expr m l e2 (eq b)) /\
        (post b)) ->
      wp_expr m l (expr.lazy_and e1 e2) post.
  Proof.
    intros. eapply wp_ite. eapply weaken_wp_expr. 1: exact H. clear H.
    cbv beta. intros. fwd. destruct_one_match; subst; do 2 eexists; split; try eassumption.
    eapply wp_literal. reflexivity.
  Qed.

  Lemma wp_lazy_or: forall m l e1 e2 (post: word -> Prop),
      wp_expr m l e1 (fun b1 => exists b,
        (if Z.eqb (word.unsigned b1) 0 then wp_expr m l e2 (eq b) else b = word.of_Z 1) /\
        (post b)) ->
      wp_expr m l (expr.lazy_or e1 e2) post.
  Proof.
    intros. eapply wp_ite. eapply weaken_wp_expr. 1: exact H. clear H.
    cbv beta. intros. fwd. destruct_one_match; subst; do 2 eexists; split; try eassumption.
    eapply wp_literal. reflexivity.
  Qed.

  Lemma wp_load: forall m l sz addr (post: word -> Prop),
      wp_expr m l addr (fun a => get_option (Memory.load sz m a) post) ->
      wp_expr m l (expr.load sz addr) post.
  Proof.
    intros. constructor. cbn. unfold load. inversion H.
    eapply WeakestPreconditionProperties.Proper_expr. 2: eassumption.
    cbv [Morphisms.pointwise_relation Basics.impl]. intros.
    inversion H1. subst. eauto.
  Qed.

  Lemma wp_op: forall m l bop ea eb (post: word -> Prop),
      wp_expr m l ea (fun a =>
        wp_expr m l eb (fun b =>
          post (interp_binop bop a b))) ->
      wp_expr m l (expr.op bop ea eb) post.
  Proof.
    intros. constructor. cbn.
    eapply weaken_wp_expr. 1: exact H. clear H. cbv beta.
    intros. destruct H. exact H.
  Qed.

  Lemma wp_expr_to_dexpr: forall m l e post,
      wp_expr m l e post ->
      exists v, dexpr m l e v /\ post v.
  Proof.
    intros. destruct H. eapply WeakestPreconditionProperties.dexpr_expr. assumption.
  Qed.

  Definition interp_bool_binop(bop: bopname)(a b: word): Prop :=
    match bop with
    | bopname.lts => word.signed a < word.signed b
    | bopname.ltu => word.unsigned a < word.unsigned b
    | bopname.eq => a = b
    | _ => False
    end.

  Definition interp_bool_prop(bop: bopname)(a b: word): Prop :=
    match bop with
    | bopname.lts => word.signed a < word.signed b
    | bopname.ltu => word.unsigned a < word.unsigned b
    | bopname.eq => a = b
    | _ => word.unsigned (interp_binop bop a b) <> 0
    end.

  Lemma dexpr_ite: forall m l e1 e2 e3 (b v: word),
      dexpr m l e1 b ->
      dexpr m l (if word.unsigned b =? 0 then e3 else e2) v ->
      dexpr m l (expr.ite e1 e2 e3) v.
  Proof.
    unfold dexpr. cbn. intros.
    eapply WeakestPreconditionProperties.Proper_expr. 2: eassumption.
    cbv [RelationClasses.Reflexive Morphisms.pointwise_relation
         Morphisms.respectful Basics.impl].
    intros. subst. eqapply H0.
    do 2 destruct_one_match; try reflexivity; exfalso.
    - apply E0. ZnWords.
    - apply E. apply word.unsigned_of_Z_0.
  Qed.

  Inductive dexpr_bool_prop(m: mem)(l: locals)(e: expr): Prop -> Prop :=
    mk_dexpr_bool_prop: forall b: word,
      dexpr m l e b ->
      dexpr_bool_prop m l e (word.unsigned b <> 0).

  Lemma dexpr_not: forall m l e (P: Prop),
      dexpr_bool_prop m l e P ->
      dexpr_bool_prop m l (expr.op bopname.eq e (expr.literal 0)) (~ P).
  Proof.
    intros. inversion H. clear H. subst P.
    eenough ((~ word.unsigned b <> 0) = _) as E. {
      rewrite E. econstructor.
      cbn. unfold dexpr in H0.
      eapply WeakestPreconditionProperties.Proper_expr. 2: eassumption.
      cbv [RelationClasses.Reflexive Morphisms.pointwise_relation
           Morphisms.respectful Basics.impl].
      intros. subst. unfold literal, dlet.dlet. reflexivity.
    }
    apply PropExtensionality.propositional_extensionality.
    destruct_one_match; split; try ZnWords.
    intros. intros _. apply E. ZnWords.
  Qed.

  Lemma dexpr_lazy_and: forall m l e1 e2 (P1 P2: Prop),
      dexpr_bool_prop m l e1 P1 ->
      (P1 -> dexpr_bool_prop m l e2 P2) ->
      dexpr_bool_prop m l (expr.lazy_and e1 e2) (P1 /\ P2).
  Proof.
    intros.
    inversion H; subst. destr (word.unsigned b =? 0).
    - replace (word.unsigned b <> 0 /\ P2) with (word.unsigned b <> 0).
      2: solve [apply PropExtensionality.propositional_extensionality; intuition idtac].
      eapply mk_dexpr_bool_prop.
      eapply dexpr_ite. 1: eassumption.
      destruct_one_match. 2: exfalso; congruence.
      unfold dexpr, WeakestPrecondition.expr, expr_body, literal, dlet.dlet.
      apply word.unsigned_inj. rewrite E. symmetry.
      apply word.unsigned_of_Z_0.
    - specialize (H0 E). inversion H0; subst.
      eassert (dexpr_bool_prop m l (expr.ite e1 e2 (expr.literal 0)) _) as A. {
        eapply mk_dexpr_bool_prop.
        eapply dexpr_ite. 1: eassumption.
        destruct_one_match. 1: exfalso; congruence. eassumption.
      }
      replace (word.unsigned b <> 0 /\ word.unsigned b0 <> 0) with (word.unsigned b0 <> 0).
      2: solve [apply PropExtensionality.propositional_extensionality; intuition idtac].
      exact A.
  Qed.

  Lemma dexpr_lazy_or: forall m l e1 e2 (P1 P2: Prop),
      dexpr_bool_prop m l e1 P1 ->
      (~P1 -> dexpr_bool_prop m l e2 P2) ->
      dexpr_bool_prop m l (expr.lazy_and e1 e2) (P1 \/ P2).
  Admitted.

  Lemma dexpr_var: forall m l x (v: word),
      map.get l x = Some v ->
      dexpr m l (expr.var x) v.
  Proof.
    intros. cbn. unfold WeakestPrecondition.get. eauto.
  Qed.

  Lemma dexpr_literal: forall (m: mem) (l: locals) z,
      dexpr m l (expr.literal z) (word.of_Z z).
  Proof. intros. reflexivity. Qed.

  Lemma dexpr_binop: forall m l op e1 e2 (v1 v2: word),
      dexpr m l e1 v1 ->
      dexpr m l e2 v2 ->
      dexpr m l (expr.op op e1 e2) (interp_binop op v1 v2).
  Proof.
    unfold dexpr. intros. cbn.
    eapply WeakestPreconditionProperties.Proper_expr. 2: eassumption.
    intros v E. subst v.
    eapply WeakestPreconditionProperties.Proper_expr. 2: eassumption.
    intros v E. subst v. reflexivity.
  Qed.

  Local Hint Rewrite @word.unsigned_ltu using typeclasses eauto: fwd_rewrites.
  Local Hint Rewrite @word.signed_lts using typeclasses eauto: fwd_rewrites.

  Lemma dexpr_bool_op_prop: forall m l op e1 e2 (v1 v2: word),
      dexpr m l e1 v1 ->
      dexpr m l e2 v2 ->
      dexpr_bool_prop m l (expr.op op e1 e2) (interp_bool_prop op v1 v2).
  Proof.
    intros.
    eassert (dexpr_bool_prop m l (expr.op op e1 e2) _) as A. {
      eapply mk_dexpr_bool_prop.
      eapply dexpr_binop; eassumption.
    }
    eqassumption.
    apply PropExtensionality.propositional_extensionality; split; destruct op; cbn;
      intros; auto; fwd; auto; destruct_one_match;
      rewrite ?word.unsigned_of_Z_1, ?word.unsigned_of_Z_0; try congruence; try Lia.lia.
  Qed.

  Definition dexpr_bool_op_prop_unf := ltac:(
    let t := type of dexpr_bool_op_prop in
    let t' := eval unfold interp_bool_prop in t in
    let p := constr:(dexpr_bool_op_prop : t') in
    exact p).

  Definition wp_expr_bool_prop(m: mem)(l: locals)(e: expr)(post: Prop -> Prop): Prop :=
    wp_expr m l e (fun b => post (word.unsigned b <> 0)).

  Lemma wp_bool_op''': forall m l op e1 e2 (post: Prop -> Prop),
      wp_expr m l e1 (fun v1 =>
        wp_expr m l e2 (fun v2 =>
          post (interp_bool_prop op v1 v2))) ->
      wp_expr_bool_prop m l (expr.op op e1 e2) post.
  Proof.
    unfold wp_expr_bool_prop. intros. eapply wp_op.
    eapply weaken_wp_expr. 1: exact H. clear H. cbv beta.
    intros. eapply weaken_wp_expr. 1: exact H. clear H. cbv beta.
    intros. unfold interp_bool_prop, interp_binop in *.
    destruct op; auto; destruct_one_match; fwd.
    all: rewrite ?word.unsigned_of_Z_nowrap by (vm_compute; intuition discriminate).
    all: try (eqassumption;
              apply PropExtensionality.propositional_extensionality; split; intros;
              (Lia.lia || congruence)).
  Qed.

  Inductive wp_cmd(call: (string -> trace -> mem -> list word ->
                          (trace -> mem -> list word -> Prop) -> Prop))
            (c: cmd)(t: trace)(m: mem)(l: locals)(post: trace -> mem -> locals -> Prop): Prop :=
    mk_wp_cmd: WeakestPrecondition.cmd call c t m l post -> wp_cmd call c t m l post.

  Lemma WWP_weaken_cmd: forall fs c t m l (post1 post2: _->_->_->Prop),
      WeakestPrecondition.cmd (call fs) c t m l post1 ->
      (forall t m l, post1 t m l -> post2 t m l) ->
      WeakestPrecondition.cmd (call fs) c t m l post2.
  Proof.
    intros.
    unshelve epose (env := _ : map.map string (list string * list string * cmd)).
    1: eapply SortedListString.map.
    (* TODO why are pairs printed back as prod rather than * ? *)
    assert (env_ok: map.ok env) by apply SortedListString.ok. clearbody env.
    eapply WeakestPreconditionProperties.Proper_cmd. 3: eassumption.
    1: eapply WeakestPreconditionProperties.Proper_call.
    cbv [RelationClasses.Reflexive Morphisms.pointwise_relation
         Morphisms.respectful Basics.impl].
    assumption.
  Qed.

  Lemma weaken_wp_cmd: forall fs c t m l (post1 post2: _->_->_->Prop),
      wp_cmd (call fs) c t m l post1 ->
      (forall t m l, post1 t m l -> post2 t m l) ->
      wp_cmd (call fs) c t m l post2.
  Proof. intros. constructor. inversion H. eapply WWP_weaken_cmd; eassumption. Qed.

  Lemma wp_set: forall fs x a t m l rest post,
      wp_expr m l a
        (fun v => wp_cmd (call fs) rest t m (map.put l x v) post) ->
      wp_cmd (call fs) (cmd.seq (cmd.set x a) rest) t m l post.
  Proof.
    intros. eapply wp_expr_to_dexpr in H. fwd. destruct Hp1.
    constructor. cbn. unfold dlet.dlet. eauto.
  Qed.

  Lemma wp_store: forall fs sz ea ev t m l rest post,
      wp_expr m l ea (fun a =>
        wp_expr m l ev (fun v =>
          get_option (Memory.store sz m a v) (fun m' =>
            wp_cmd (call fs) rest t m' l post))) ->
      wp_cmd (call fs) (cmd.seq (cmd.store sz ea ev) rest) t m l post.
  Proof.
    intros. constructor. cbn.
    eapply wp_expr_to_dexpr in H. unfold dexpr in *. fwd.
    eapply wp_expr_to_dexpr in Hp1. unfold dexpr in *. fwd.
    inversion Hp1p1. inversion H0. subst. unfold store. symmetry in H. eauto 10.
  Qed.

  Lemma wp_if0: forall fs c thn els rest t m l post,
      wp_expr m l c (fun b => exists Q1 Q2,
        ((word.unsigned b <> 0 -> wp_cmd (call fs) thn t m l Q1) /\
         (word.unsigned b =  0 -> wp_cmd (call fs) els t m l Q2)) /\
        (forall t' m' l', word.unsigned b <> 0 /\ Q1 t' m' l' \/
                          word.unsigned b =  0 /\ Q2 t' m' l' ->
                          wp_cmd (call fs) rest t' m' l' post)) ->
      wp_cmd (call fs) (cmd.seq (cmd.cond c thn els) rest) t m l post.
  Proof.
    intros. constructor. cbn.
    eapply wp_expr_to_dexpr in H. fwd.
    eexists. split; [eassumption| ]. split; intros.
    - eapply WWP_weaken_cmd. 1: eapply Hp1p0p0; eassumption.
      unfold Morphisms.pointwise_relation, Basics.impl. intros. eapply Hp1p1. eauto.
    - eapply WWP_weaken_cmd. 1: eapply Hp1p0p1; eassumption.
      unfold Morphisms.pointwise_relation, Basics.impl. intros. eapply Hp1p1. eauto.
  Qed.

  Lemma wp_if: forall fs c l vars vals thn els rest t m post,
      l = reconstruct vars vals ->
      wp_expr m l c (fun b =>
        exists (Q1 Q2: trace -> mem -> locals -> Prop),
          ((word.unsigned b <> 0 -> wp_cmd (call fs) thn t m l (fun t' m' l' =>
              exists vals', l' = reconstruct vars vals' /\ Q1 t' m' l')) /\
           (word.unsigned b =  0 -> wp_cmd (call fs) els t m l (fun t' m' l' =>
              exists vals', l' = reconstruct vars vals' /\ Q2 t' m' l'))) /\
          (forall t' m' vals', let l' := reconstruct vars vals' in
                               word.unsigned b <> 0 /\ Q1 t' m' l' \/
                               word.unsigned b =  0 /\ Q2 t' m' l' ->
                               wp_cmd (call fs) rest  t' m' l' post)) ->
      wp_cmd (call fs) (cmd.seq (cmd.cond c thn els) rest) t m l post.
  Proof.
    intros. subst. eapply wp_if0. eapply weaken_wp_expr. 1: exact H0. clear H0. cbv beta.
    intros v (Q1 & Q2 & A & B). eexists. eexists. split. 1: exact A. clear A. cbv beta.
    intros * [? | ?]; fwd; eapply B; eauto.
  Qed.

  (* Not using this one because it's not clear how to prove a wp_expr_bool_prop
     without invoking post twice *)
  Lemma wp_if_bool: forall fs c l vars vals thn els rest t m Q1 Q2 post,
      l = reconstruct vars vals ->
      wp_expr_bool_prop m l c (fun P =>
        ((P  -> wp_cmd (call fs) thn t m l (fun t' m' l' =>
                  exists vals', l' = reconstruct vars vals' /\ Q1 t' m' l')) /\
         (~P -> wp_cmd (call fs) els t m l (fun t' m' l' =>
                  exists vals', l' = reconstruct vars vals' /\ Q2 t' m' l'))) /\
        (forall t' m' vals', let l' := reconstruct vars vals' in
                             P  /\ Q1 t' m' l' \/
                             ~P /\ Q2 t' m' l' ->
                             wp_cmd (call fs) rest t' m' l' post)) ->
      wp_cmd (call fs) (cmd.seq (cmd.cond c thn els) rest) t m l post.
  Abort.

  Lemma wp_if_bool_dexpr: forall fs c vars vals0 thn els rest t0 m0 P Q1 Q2 post,
      dexpr_bool_prop m0 (reconstruct vars vals0) c P ->
      (P  -> wp_cmd (call fs) thn t0 m0 (reconstruct vars vals0) (fun t m l =>
               exists vals, l = reconstruct vars vals /\ Q1 t m l)) ->
      (~P -> wp_cmd (call fs) els t0 m0 (reconstruct vars vals0) (fun t m l =>
               exists vals, l = reconstruct vars vals /\ Q2 t m l)) ->
      (forall (cond0: bool) t m vals,
          (* (if cond0 then P else ~P) -> <-- already added to Q1/Q2 by automation *)
          (if cond0 then Q1 t m (reconstruct vars vals)
           else Q2 t m (reconstruct vars vals)) ->
          wp_cmd (call fs) rest t m (reconstruct vars vals) post) ->
      wp_cmd (call fs) (cmd.seq (cmd.cond c thn els) rest) t0 m0 (reconstruct vars vals0) post.
  Proof.
    intros. inversion H. subst P. eapply wp_if. 1: reflexivity.
    unfold dexpr in H3.
    eapply weaken_wp_expr. 1: constructor; eassumption.
    intros. subst v. do 2 eexists. ssplit.
    - eassumption.
    - intros. eapply H1. intro C. apply C. assumption.
    - cbv zeta. intros. destruct H4 as [(Ne & P) | (E & P)];
        [eapply (H2 true)| eapply (H2 false)]; assumption.
  Qed.

  Lemma wp_while {measure : Type} (v0 : measure) (e: expr) (c: cmd) t (m: mem) l fs rest
    (invariant: measure -> trace -> mem -> locals -> Prop) {lt}
    {post : trace -> mem -> locals -> Prop}
    (Hpre: invariant v0 t m l)
    (Hwf : well_founded lt)
    (Hbody : forall v t m l,
      invariant v t m l ->
      exists P, dexpr_bool_prop m l e P /\
         (P -> wp_cmd (call fs) c t m l
                      (fun t m l => exists v', invariant v' t m l /\ lt v' v)) /\
         (~P -> wp_cmd (call fs) rest t m l post))
    : wp_cmd (call fs) (cmd.seq (cmd.while e c) rest) t m l post.
  Proof.
    econstructor. cbn. exists measure, lt, invariant.
    split. 1: assumption.
    split. 1: eauto.
    clear Hpre v0 t m l.
    intros v t m l Hinv.
    specialize (Hbody v t m l Hinv).
    fwd.
    inversion Hbodyp0. subst P. exists b. split. 1: exact H. split.
    - intro NE. eapply Hbodyp1. assumption.
    - intro E. eapply Hbodyp2. intro C. apply C. exact E.
  Qed.

  (* The postcondition of the callee's spec will have a concrete shape that differs
     from the postcondition that we pass to `call`, so when using this lemma, we have
     to apply weakening for `call`, which generates two subgoals:
     1) call f t m argvals ?mid
     2) forall t' m' resvals, ?mid t' m' resvals -> the post of `call`
     To solve 1), we will apply the callee's spec, but that means that if we make
     changes to the context while solving the preconditions of the callee's spec,
     these changes will not be visible in subgoal 2 *)
  Lemma wp_call: forall fs binds f argexprs rest t m l post,
      wp_exprs m l argexprs (fun argvals =>
        call fs f t m argvals (fun t' m' resvals =>
          get_option (map.putmany_of_list_zip binds resvals l) (fun l' =>
            wp_cmd (call fs) rest t' m' l' post))) ->
      wp_cmd (call fs) (cmd.seq (cmd.call binds f argexprs) rest) t m l post.
  Proof.
  Admitted.

  (* It's not clear whether a change to wp_call can fix this.
     Right now, specs look like this:

  Instance spec_of_foo : spec_of "foo" := fun functions =>
    forall t m argvals ghosts,
      NonmemHyps ->
      (sepclause1 * ... * sepclauseN) m ->
      WeakestPrecondition.call functions "foo" t m argvals
        (fun t' m' rets => calleePost).

  If I want to use spec_of_foo, I'll have a WeakestPrecondition.call goal with callerPost, and to
  reconcile the callerPost with calleePost, I have to apply weakening/Proper for
  WeakestPrecondition.call, which results in two sugoals:

  1) WeakestPrecondition.call "foo" t m argvals ?mid
  2) forall t' m' resvals, ?mid t' m' resvals -> callerPost

  On 1), I will apply foo_ok (which proves spec_of_foo), so all hyps in spec_of_foo are proven
  in a subgoal separate from subgoal 2), so changes made to the context won't be visible in
  subgoal 2).

  Easiest to use would be this one:

  Instance spec_of_foo' : spec_of "foo" := fun functions =>
    forall t m argvals ghosts callerPost,
      seps [sepclause1; ...; sepclauseN; emp P1; ... emp PN;
         emp (forall t' m' retvals,
                  calleePost t' m' retvals ->
                  callerPost t' m' retvals)] m ->
      WeakestPrecondition.call functions "foo" t m argvals callerPost.

  because it has weakening built in and creates only one subgoal, so all context modifications
  remain visible.
  And using some notations, this form might even become ergonomic. *)

  Lemma wp_skip: forall fs t m l (post: trace -> mem -> locals -> Prop),
      post t m l ->
      wp_cmd (call fs) cmd.skip t m l post.
  Proof. intros. constructor. assumption. Qed.

  (* to avoid using `remember` and having to control which occurrence we want to remember *)
  Lemma wp_locals_put: forall fs c x v t m l post,
      (forall a, a = v -> wp_cmd (call fs) c t m (map.put l x a) post) ->
      wp_cmd (call fs) c t m (map.put l x v) post.
  Proof. auto. Qed.

  Definition vc_func fs '(innames, outnames, body) (t: trace) (m: mem) (argvs: list word)
                     (post : trace -> mem -> list word -> Prop) :=
    exists l, map.of_list_zip innames argvs = Some l /\
      wp_cmd (call fs) body t m l (fun t' m' l' =>
        exists retvs, map.getmany_of_list l' outnames = Some retvs /\ post t' m' retvs).

  Definition arguments_marker(args: list word): list word := args.

End WithParams.


(*
TODO: once we have C notations for function signatures,
put vernac between /*.   .*/ and ltac between /**.  .**/ so that
only Ltac gets hidden *)
Notation "'C_STARTS_HERE' /* *" := True (only parsing).
Notation "'!EOF' '.*' '*/' //" := True (only parsing).


Declare Scope live_scope.
Delimit Scope live_scope with live.
Local Open Scope live_scope.

Inductive scope_kind := FunctionBody | ThenBranch | ElseBranch | LoopBody | LoopInvariant.
Inductive scope_marker: scope_kind -> Set := mk_scope_marker sk : scope_marker sk.
Notation "'____' sk '____'" := (scope_marker sk) (only printing) : live_scope.

Ltac assert_scope_kind expected :=
  let sk := lazymatch goal with
            | H: scope_marker ?sk |- _ => sk
            | _ => fail "no scope marker found"
            end in
  tryif constr_eq sk expected then idtac
  else fail "This snippet is only allowed in a" expected "block, but we're in a" sk "block".

Declare Scope live_scope_prettier. (* prettier, but harder to debug *)
Local Open Scope live_scope_prettier.

Notation "'ready' 'for' 'next' 'command'" := (wp_cmd _ _ _ _ _ _)
  (at level 0, only printing) : live_scope_prettier.

Declare Scope reconstruct_locals_scope.
Delimit Scope reconstruct_locals_scope with reconstruct_locals.

Notation "[ x ]" := (PrimitivePair.pair.mk x tt)
  : reconstruct_locals_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (PrimitivePair.pair.mk x (PrimitivePair.pair.mk y .. (PrimitivePair.pair.mk z tt) ..))
  : reconstruct_locals_scope.

Notation "l" := (arguments_marker l)
  (at level 100, only printing) : live_scope.

Ltac put_into_current_locals is_decl :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.put ?l ?x ?v) _ =>
    let i := string_to_ident x in
    let old_i := fresh i "_0" in
    lazymatch is_decl with
    | true => idtac
    | false => rename i into old_i
    end;
    (* match again because there might have been a renaming *)
    lazymatch goal with
    | |- wp_cmd ?call ?c ?t ?m (map.put ?l ?x ?v) ?post =>
        (* tradeoff between goal size blowup and not having to follow too many aliases *)
        let v' := rdelta_var v in
        pose (i := v');
        change (wp_cmd call c t m (map.put l x i) post)
    end;
    lazymatch goal with
    | |- wp_cmd ?call ?c ?t ?m ?l ?post =>
        let keys := eval lazy in (map.keys l) in
        let values := eval hnf in
          (match map.getmany_of_list l keys with
           | Some vs => vs
           | None => nil
           end) in
        let values := eval cbn [tuple.of_list] in (tuple.of_list values) in
        change (wp_cmd call c t m (reconstruct keys values) post)
    end;
    lazymatch is_decl with
    | true => idtac
    | false => try clear old_i
    end
  end.

Ltac eval_expr_step :=
  lazymatch goal with
  | |- wp_expr _ _ (expr.load _ _) _ => eapply wp_load
  | |- wp_expr _ _ (expr.var _) _ => eapply wp_var; [ reflexivity | ]
  | |- wp_expr _ _ (expr.literal _) _ => eapply wp_literal
  | |- wp_expr _ _ (expr.op _ _ _) _ => eapply wp_op; cbv [interp_binop]
  | |- get_option (Memory.load access_size.word _ _) _ =>
      eapply load_word_of_sep_cps; scancel_asm; clear_split_sepclause_stack
  end.

Ltac eval_expr := repeat eval_expr_step.

Ltac eval_dexpr_step :=
  lazymatch goal with
  | |- dexpr_bool_prop _ _ (expr.lazy_and _ _) _ =>
      eapply dexpr_lazy_and; [ |intro]
  | |- dexpr_bool_prop _ _ (expr.op bopname.eq _ (expr.literal 0)) _ =>
      eapply dexpr_not
  | |- dexpr_bool_prop _ _ (expr.op _ _ _) _ =>
      eapply dexpr_bool_op_prop_unf
  | |- dexpr _ _ (expr.var _) _ => eapply dexpr_var; reflexivity
  | |- dexpr _ _ (expr.literal _) _ => eapply dexpr_literal
  end.

Ltac eval_dexpr := repeat eval_dexpr_step.

Ltac start :=
  lazymatch goal with
  | |- {_: prod (prod (list string) (list string)) Syntax.cmd & _ } => idtac
  | |- _ => fail "goal needs to be of shape {_: list string * list string * Syntax.cmd & _ }"
  end;
  let eargnames := open_constr:(_: list string) in
  refine (existT _ (eargnames, _, _) _);
  let fs := fresh "fs" in
  intro fs;
  let n := fresh "Scope0" in pose proof (mk_scope_marker FunctionBody) as n;
  intros;
  (* since the arguments will get renamed, it is useful to have a list of their
     names, so that we can always see their current renamed names *)
  let arguments := fresh "arguments" in
  lazymatch goal with
  | |- vc_func _ ?f ?t ?m ?argvalues ?post =>
    pose (arguments_marker argvalues) as arguments;
    let argnames := map_with_ltac varconstr_to_string argvalues in
    unify eargnames argnames;
    move arguments before n
  end;
  unfold vc_func;
  lazymatch goal with
  | |- exists l, map.of_list_zip ?keys ?values = Some l /\ _ =>
    let values := eval vm_compute in (tuple.of_list values) in
    exists (reconstruct keys values);
    split; [reflexivity| ]
  end.

(* Note: contrary to add_last_var_to_post, this one makes Post a goal rather
   than a hypothesis, because if it was a hypothesis, it wouldn't be possible
   to clear vars *)
Ltac add_last_hyp_to_post :=
  let last_hyp := match goal with H: _ |- _ => H end in
  let T := type of last_hyp in
  lazymatch T with
  | scope_marker _ => fail "done (scope marker reached)"
  | _ ?m => let t := type of m in
            lazymatch t with
            | @map.rep (@word.rep _ _) Init.Byte.byte _ => flatten_seps_in last_hyp
            | _ => idtac
            end
  | _ => idtac
  end;
  lazymatch type of T with
  | Prop => refine (ands_cons last_hyp _); clear last_hyp
  | _ => clear last_hyp
  end.

Ltac is_in_post_evar_scope x :=
  lazymatch goal with
  | |- ?E ?T ?M ?L =>
      lazymatch type of E with
      | ?Trace -> ?Mem -> ?Locals -> Prop =>
          assert_succeeds (unify E (fun (_: Trace) (_: Mem) (_: Locals) => x = x))
      end
  end.

Ltac add_equality_to_post x Post :=
  let y := fresh "etmp0" in
  (* using pose & context match instead of set because set adds the renaming @{x:=y}
     to the evar, so x will not be in the evar scope any more at the end, even though
     x was introduced before the evar was created *)
  pose (y := x);
  lazymatch goal with
  | |- context C[x] => let C' := context C[y] in change C'
  end;
  eapply (ands_cons (eq_refl y : y = x)) in Post;
  clearbody y.

Ltac add_equalities_to_post Post :=
  lazymatch goal with
  (* loop invariant *)
  | |- ?E ?Measure ?T ?M ?L =>
      add_equality_to_post L Post;
      add_equality_to_post T Post;
      add_equality_to_post Measure Post
  (* if branch post *)
  | |- ?E ?T ?M ?L =>
      add_equality_to_post L Post;
      add_equality_to_post T Post
  end.

Ltac add_var_to_post x Post :=
  first
    [ let rhs := eval cbv delta [x] in x in
      (tryif is_var rhs then idtac else (
        vpattern x in Post;
        lazymatch type of Post with
        | ?f x => change (dlet x f) in Post
        end));
      subst x
    | vpattern x in Post;
      eapply ex_intro in Post;
      clear x ].

Ltac add_last_var_to_post Post :=
  let lastvar :=
    match goal with
    | x: _ |- _ =>
        let __ := match constr:(Set) with
                  | _ => assert_fails (constr_eq x Post)
                  end in x
    end in
  let T := type of lastvar in
  lazymatch T with
  | scope_marker _ => fail "done (scope marker reached)"
  | _ => idtac
  end;
  lazymatch type of T with
  | Prop => clear lastvar
  | _ => lazymatch goal with
         (* at the beginning of a while loop, where we have to instantiate the
            loop invariant, the goal is of form (?invariant measure_tmp t_tmp m_tmp l_tmp *)
         | |- _ lastvar _ _ _ => move lastvar at top
         (* after an if branch, the goal is of form (?post t_tmp m_tmp l_tmp) *)
         | |- _ lastvar _ _ => move lastvar at top
         | |- _ _ lastvar _ => move lastvar at top
         | |- _ _ _ lastvar => move lastvar at top
         (* if lastvar is not a _tmp var to be patterned out later, add it to post: *)
         | |- _ => add_var_to_post lastvar Post
         end
  end.

Ltac package_context :=
  lazymatch goal with
  | H: _ ?m |- ?E ?t ?m ?l =>
      (* always package sep log assertion, even if memory was not changed in current block *)
      move H at bottom
  | |- ?E ?t ?m ?l => fail "No separation logic hypothesis about" m "found"
  end;
  let Post := fresh "Post" in
  eassert _ as Post by (repeat add_last_hyp_to_post; apply ands_nil);
  add_equalities_to_post Post;
  repeat add_last_var_to_post Post;
  lazymatch goal with
  | |- _ ?Measure ?T ?M ?L => pattern Measure, T, M, L in Post
  | |- _ ?T ?M ?L => pattern T, M, L in Post
  end;
  exact Post.

Section MergingAnd.
  Lemma if_dlet_l_inline: forall (b: bool) (T: Type) (rhs: T) (body: T -> Prop) (P: Prop),
      (if b then dlet rhs body else P) ->
      (if b then body rhs else P).
  Proof. unfold dlet. intros. assumption. Qed.

  Lemma if_dlet_r_inline: forall (b: bool) (T: Type) (rhs: T) (body: T -> Prop) (P: Prop),
      (if b then P else dlet rhs body) ->
      (if b then P else body rhs).
  Proof. unfold dlet. intros. assumption. Qed.

  Lemma pull_if_exists_l (b: bool) (T: Type) {inh: inhabited T} (body: T -> Prop) (P: Prop):
      (if b then (exists x, body x) else P) ->
      exists x, if b then body x else P.
  Proof. intros. destruct b; fwd; [exists x|exists default]; assumption. Qed.

  Lemma pull_if_exists_r (b: bool) (T: Type) {inh: inhabited T} (body: T -> Prop) (P: Prop):
      (if b then P else (exists x, body x)) ->
      exists x, if b then P else body x.
  Proof. intros. destruct b; fwd; [exists default|exists x]; assumption. Qed.

  Lemma if_ands_same_head: forall (b: bool) (P: Prop) (Qs1 Qs2: list Prop),
      (if b then ands (P :: Qs1) else ands (P :: Qs2)) ->
      P /\ (if b then ands Qs1 else ands Qs2).
  Proof. cbn. intros. destruct b; intuition idtac. Qed.

  Local Set Warnings "-notation-overridden".
  Local Infix "++" := SeparationLogic.app. Local Infix "++" := app : list_scope.
  Let nth n xs := SeparationLogic.hd True (SeparationLogic.skipn n xs).
  Let remove_nth n (xs : list Prop) :=
    (SeparationLogic.firstn n xs ++ SeparationLogic.tl (SeparationLogic.skipn n xs)).

  Lemma ands_app: forall Ps Qs, ands (Ps ++ Qs) = (ands Ps /\ ands Qs).
  Proof.
    induction Ps; cbn; intros; apply PropExtensionality.propositional_extensionality;
      rewrite ?IHPs; intuition idtac.
  Qed.

  Lemma ands_nth_to_head: forall (n: nat) (Ps: list Prop),
      (nth n Ps /\ ands (remove_nth n Ps)) = (ands Ps).
  Proof.
    intros. cbv [nth remove_nth].
    pose proof (List.firstn_skipn n Ps: (firstn n Ps ++ skipn n Ps) = Ps).
    forget (skipn n Ps) as Psr.
    forget (firstn n Ps) as Psl.
    subst Ps.
    apply PropExtensionality.propositional_extensionality.
    destruct Psr.
    { cbn. rewrite List.app_nil_r. intuition idtac. }
    cbn [hd tl]. rewrite ?ands_app. cbn [ands]. intuition idtac.
  Qed.

  Lemma merge_ands_at_indices: forall i j (P1 P2: Prop) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = P1 ->
      nth j Ps2 = P2 ->
      (if b then ands Ps1 else ands Ps2) ->
      (if b then P1 else P2) /\
      (if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2)).
  Proof.
    intros. subst.
    rewrite <- (ands_nth_to_head i Ps1) in H1.
    rewrite <- (ands_nth_to_head j Ps2) in H1.
    destruct b; intuition idtac.
  Qed.

  Lemma merge_ands_at_indices_same_lhs:
    forall i j {T: Type} (lhs rhs1 rhs2: T) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = (lhs = rhs1) ->
      nth j Ps2 = (lhs = rhs2) ->
      (if b then ands Ps1 else ands Ps2) ->
      lhs = (if b then rhs1 else rhs2) /\
      (if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2)).
  Proof.
    intros. eapply merge_ands_at_indices in H1; [ | eassumption.. ].
    destruct b; assumption.
  Qed.

  Lemma merge_ands_at_indices_same_prop: forall i j (P: Prop) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = P ->
      nth j Ps2 = P ->
      (if b then ands Ps1 else ands Ps2) ->
      P /\ (if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2)).
  Proof.
    intros. eapply merge_ands_at_indices in H1; [ | eassumption.. ].
    destruct b; assumption.
  Qed.

  Lemma merge_ands_at_indices_neg_prop: forall i j (P: Prop) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = P ->
      nth j Ps2 = (~P) ->
      (if b then ands Ps1 else ands Ps2) ->
      (if b then P else ~P) /\
        (if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2)).
  Proof.
    intros. eapply merge_ands_at_indices in H1; eassumption.
  Qed.

  Lemma merge_ands_at_indices_same_mem:
    forall i j (mem: Type) (m: mem) (P1 P2: mem -> Prop) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = P1 m ->
      nth j Ps2 = P2 m ->
      (if b then ands Ps1 else ands Ps2) ->
      (if b then P1 m else P2 m) /\
        (if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2)).
  Proof.
    intros. eapply merge_ands_at_indices in H1; [ | eassumption.. ].
    destruct b; assumption.
  Qed.

  Lemma merge_ands_at_indices_seps_same_mem:
    forall i j [word: Type] [mem: map.map word byte]
           (m: mem) (l1 l2: list (mem -> Prop)) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = seps l1 m ->
      nth j Ps2 = seps l2 m ->
      (if b then ands Ps1 else ands Ps2) ->
      seps [| seps (if b then l1 else l2) |] m /\
        if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2).
  Proof.
    intros. eapply merge_ands_at_indices in H1; [ | eassumption.. ].
    destruct b; assumption.
  Qed.
End MergingAnd.

Section MergingSep.
  Context {width: Z} {word: word.word width}
          {word_ok: word.ok word} {mem: map.map word byte} {ok: map.ok mem}.

  Local Set Warnings "-notation-overridden".
  Local Infix "++" := SeparationLogic.app. Local Infix "++" := app : list_scope.
  Let nth(n: nat)(xs: list (mem -> Prop)) :=
        SeparationLogic.hd (emp True) (SeparationLogic.skipn n xs).
  Let remove_nth(n: nat)(xs: list (mem -> Prop)) :=
    (SeparationLogic.firstn n xs ++ SeparationLogic.tl (SeparationLogic.skipn n xs)).

  Lemma merge_seps_at_indices (m: mem) (i j: nat)
        (P1 P2: mem -> Prop) (Ps1 Ps2 Qs: list (mem -> Prop)) (b: bool):
    nth i Ps1 = P1 ->
    nth j Ps2 = P2 ->
    seps ((seps (if b then Ps1 else Ps2)) :: Qs) m ->
    seps ((seps (if b then (remove_nth i Ps1) else (remove_nth j Ps2))) ::
          (if b then P1 else P2) :: Qs) m.
  Proof.
    intros. subst. eapply seps'_iff1_seps in H1. eapply seps'_iff1_seps.
    cbn [seps'] in *. unfold remove_nth, nth. destruct b.
    - pose proof (seps_nth_to_head i Ps1) as A.
      eapply iff1ToEq in A. rewrite <- A in H1. ecancel_assumption.
    - pose proof (seps_nth_to_head j Ps2) as A.
      eapply iff1ToEq in A. rewrite <- A in H1. ecancel_assumption.
  Qed.

  (* Note: if the two predicates are at the same address, but have different footprints,
     you might not want to merge them, but first combine them with other sep clauses
     until they both have the same footprint *)
  Lemma merge_seps_at_indices_same_addr_and_pred (m: mem) i j [V: Type] a (v1 v2: V)
        (pred: sep_predicate mem V) (Ps1 Ps2 Qs: list (mem -> Prop)) (b: bool):
    nth i Ps1 = pred a v1 ->
    nth j Ps2 = pred a v2 ->
    seps ((seps (if b then Ps1 else Ps2)) :: Qs) m ->
    seps ((seps (if b then (remove_nth i Ps1) else (remove_nth j Ps2)))
            :: pred a (if b then v1 else v2) :: Qs) m.
  Proof.
    intros. eapply (merge_seps_at_indices m i j) in H1; [ | eassumption.. ].
    destruct b; assumption.
  Qed.

  Lemma merge_seps_at_indices_same (m: mem) i j
        (P: mem -> Prop) (Ps1 Ps2 Qs: list (mem -> Prop)) (b: bool):
    nth i Ps1 = P ->
    nth j Ps2 = P ->
    seps ((seps (if b then Ps1 else Ps2)) :: Qs) m ->
    seps ((seps (if b then (remove_nth i Ps1) else (remove_nth j Ps2))) :: P :: Qs) m.
  Proof.
    intros. eapply (merge_seps_at_indices m i j P P) in H1; [ | eassumption.. ].
    destruct b; assumption.
  Qed.

  Lemma merge_seps_done (m: mem) (Qs: list (mem -> Prop)) (b: bool):
    seps ((seps (if b then [] else [])) :: Qs) m ->
    seps Qs m.
  Proof.
    intros.
    pose proof (seps'_iff1_seps (seps (if b then [] else []) :: Qs)) as A.
    eapply iff1ToEq in A.
    rewrite <- A in H. cbn [seps'] in H. clear A.
    pose proof (seps'_iff1_seps Qs) as A.
    eapply iff1ToEq in A.
    rewrite A in H. clear A.
    destruct b; cbn [seps] in H; eapply (proj1 (sep_emp_True_l _ _)) in H; exact H.
  Qed.

  Lemma expose_addr_of_then_in_else:
    forall (m: mem) (a: word) v (Ps1 Ps2 Rs Qs: list (mem -> Prop)) (b: bool),
    impl1 (seps Ps2) (seps ((v a) :: Rs)) ->
    seps ((seps (if b then Ps1 else Ps2)) :: Qs) m ->
    seps ((seps (if b then Ps1 else ((v a) :: Rs))) :: Qs) m.
  Proof.
    intros. destruct b.
    - assumption.
    - (* TODO make seprewrite_in work for impl1 *)
      pose proof (seps'_iff1_seps (seps Ps2 :: Qs)) as A. eapply iff1ToEq in A.
      rewrite <- A in H0. cbn [seps'] in H0. clear A.
      pose proof (seps'_iff1_seps (seps ((v a) :: Rs) :: Qs)) as A. eapply iff1ToEq in A.
      rewrite <- A. cbn [seps']. clear A.
      eassert (impl1 (sep (seps Ps2) (seps' Qs)) (sep (seps (v a :: Rs)) _)) as A. {
        ecancel.
      }
      eapply A. assumption.
  Qed.
End MergingSep.

Fixpoint zip_tuple_if{A: Type}(b: bool){n: nat}(t1 t2: tuple A n){struct n}: tuple A n.
  destruct n.
  - exact tt.
  - destruct t1 as (h1 & t1). destruct t2 as (h2 & t2).
    constructor.
    + exact (if b then h1 else h2).
    + exact (zip_tuple_if A b n t1 t2).
Defined.

Lemma zip_tuple_if_true: forall A n (t1 t2: tuple A n), zip_tuple_if true t1 t2 = t1.
Proof.
  induction n; cbn; intros; destruct t1; destruct t2.
  - reflexivity.
  - f_equal. eapply IHn.
Qed.

Lemma zip_tuple_if_false: forall A n (t1 t2: tuple A n), zip_tuple_if false t1 t2 = t2.
Proof.
  induction n; cbn; intros; destruct t1; destruct t2.
  - reflexivity.
  - f_equal. eapply IHn.
Qed.

Section ReconstructLemmas.
  Context {word: word.word 32} {mem: map.map word byte} {locals: map.map string word}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {locals_ok: map.ok locals}.

  Lemma push_if_reconstruct:
    forall varnames (valsThen valsElse: tuple word (List.length varnames)) (b: bool),
      (if b then reconstruct varnames valsThen else reconstruct varnames valsElse) =
        reconstruct varnames (zip_tuple_if b valsThen valsElse).
  Proof.
    intros. destruct b.
    - rewrite zip_tuple_if_true. reflexivity.
    - rewrite zip_tuple_if_false. reflexivity.
  Qed.

  Lemma reconstruct_cons(v: string)(vs: list string)(x: word)
        (xs: tuple word (List.length vs)):
    reconstruct (cons v vs) (PrimitivePair.pair.mk x xs) = map.put (reconstruct vs xs) v x.
  Proof. reflexivity. Qed.

  Lemma not_in_reconstruct: forall a vs (xs: tuple word (List.length vs)),
      ~ List.In a vs -> map.get (reconstruct vs xs) a = None.
  Proof.
    induction vs; intros.
    - cbn. apply map.get_empty.
    - destruct xs. rewrite reconstruct_cons.
      rewrite map.get_put_dec. destruct_one_match.
      + exfalso. apply H. cbn. auto.
      + eapply IHvs. intro C. apply H. cbn. auto.
  Qed.

  Lemma invert_reconstruct_eq_aux: forall vs (xs ys: tuple word (List.length vs)),
      List.NoDup vs ->
      reconstruct vs xs = reconstruct vs ys ->
      xs = ys.
  Proof.
    induction vs; intros; destruct xs; destruct ys.
    - reflexivity.
    - rewrite 2reconstruct_cons in H0.
      inversion H. subst.
      eapply map.invert_put_eq in H0.
      + destruct H0. f_equal. 1: assumption. eapply IHvs; eassumption.
      + cbn. apply not_in_reconstruct. assumption.
      + cbn. apply not_in_reconstruct. assumption.
  Qed.

  Lemma invert_reconstruct_eq(vs: list string)(xs ys: tuple word (List.length vs)):
    List.dedup String.eqb vs = vs ->
    reconstruct vs xs = reconstruct vs ys ->
    xs = ys.
  Proof.
    intros. eapply invert_reconstruct_eq_aux. 2: assumption. rewrite <- H.
    apply List.NoDup_dedup.
  Qed.

  Lemma invert_reconstruct_eq_if:
    forall (vs: list string)(xs ys zs: tuple word (List.length vs))(b: bool),
      List.dedup String.eqb vs = vs ->
      reconstruct vs xs = (if b then reconstruct vs ys else reconstruct vs zs) ->
      xs = (if b then ys else zs).
  Proof.
    intros. destruct b; eapply invert_reconstruct_eq; assumption.
  Qed.

  Lemma invert_tuple_eq{A B: Type}: forall (h1 h2: A) (t1 t2: B),
      PrimitivePair.pair.mk h1 t1 = PrimitivePair.pair.mk h2 t2 ->
      h1 = h2 /\ t1 = t2.
  Proof. intros. split; congruence. Qed.

  Lemma eq_if_same{A: Type}: forall (lhs rhs: A) (b: bool),
      lhs = (if b then rhs else rhs) ->
      lhs = rhs.
  Proof. intros; destruct b; assumption. Qed.
End ReconstructLemmas.

Ltac destruct_locals_norename tup names :=
  lazymatch names with
  | ?s :: ?rest =>
      let name := string_to_ident s in
      let t := fresh "tmp_" name in
      destruct tup as (t & tup); destruct_locals_norename tup rest
  | nil => destruct tup (* becomes tt *)
  end.

Ltac destruct_locals tup names :=
  lazymatch names with
  | ?s :: ?rest => let name := string_to_ident s in
                   make_fresh name; destruct tup as (name & tup); destruct_locals tup rest
  | nil => destruct tup (* becomes tt *)
  end.

Ltac destruct_locals_after_merge tup names :=
  lazymatch names with
  | ?s :: ?rest =>
      lazymatch goal with
      | H: tup = _ |- _ =>
          let name := string_to_ident s in
          let t := fresh "tmp_" name in
          destruct tup as (t & tup);
          eapply invert_tuple_eq in H;
          let F := fresh in
          destruct H as [F H];
          lazymatch type of F with
          | t = if _ then ?x else ?x => eapply eq_if_same in F
          | t = _ => idtac
          end;
          lazymatch type of F with
          | t = ?rhs => tryif is_var rhs then (
              subst t
            ) else (
              make_fresh name;
              (* compute type again because make_fresh might have changed it *)
              lazymatch type of F with
              | t = ?ite => subst t; set (name := ite)
              end
            )
          end;
          destruct_locals_after_merge tup rest
      end
  | nil => destruct tup (* becomes tt *)
  end.

Ltac pull_dlet_and_exists_step :=
  lazymatch goal with
  | H: if _ then dlet _ (fun x => _) else _ |- _ =>
      make_fresh x;
      lazymatch type of H with
      | if ?c then dlet ?rhs ?body else ?els =>
          pose (x := rhs);
          change (if c then dlet x body else els) in H;
          eapply if_dlet_l_inline in H
      end
  | H: if _ then _ else dlet _ (fun x => _) |- _ =>
      make_fresh x;
      lazymatch type of H with
      | if ?c then ?thn else dlet ?rhs ?body =>
          pose (x := rhs);
          change (if c then thn else dlet x body) in H;
          eapply if_dlet_r_inline in H
      end
  | H: if ?b then (exists x, _) else ?P |- _ =>
      eapply (pull_if_exists_l b _ _ P) in H;
      make_fresh x;
      destruct H as [x H]
  | H: if ?b then ?P else (exists x, _) |- _ =>
      eapply (pull_if_exists_r b _ _ P) in H;
      make_fresh x;
      destruct H as [x H]
  end.

Ltac merge_pair H Ps Qs is_match lem := once (
  lazymatch index_and_element_of Ps with
  | (?i, ?P) =>
      lazymatch find_in_list ltac:(fun Q => is_match P Q) Qs with
      | (?j, ?Q) =>
          eapply (lem i j) in H;
          [ cbn [app firstn tl skipn] in H
          | cbn [hd skipn]; reflexivity .. ]
      end
  end).

Ltac merge_and_pair is_match lem :=
  lazymatch goal with
  | H: if _ then ands ?Ps else ands ?Qs |- _ =>
      merge_pair H Ps Qs is_match lem; destruct H
  end.

Ltac same_lhs P Q :=
  lazymatch P with
  | ?lhs = _ =>
      lazymatch Q with
      | lhs = _ => constr:(true)
      | _ = _ => constr:(false)
      end
  end.

Ltac same_addr_and_pred P Q :=
  lazymatch P with
  | ?pred ?addr ?valueP =>
      lazymatch Q with
      | pred addr ?valueQ => constr:(true)
      | _ => constr:(false)
      end
  | _ => constr:(false)
  end.

Ltac neg_prop P Q :=
  lazymatch Q with
  | ~ P => constr:(true)
  | _ => constr:(false)
  end.

Ltac seps_about_same_mem x y :=
  lazymatch x with
  | seps _ ?m => lazymatch y with
                 | seps _ ?m => constr:(true)
                 | _ => constr:(false)
                 end
  | _ => constr:(false)
  end.

Ltac constr_eqb x y :=
  lazymatch x with
  | y => constr:(true)
  | _ => constr:(false)
  end.

Ltac merge_sep_pair_step :=
  lazymatch goal with
  | H: seps ((seps (if ?b then ?Ps else ?Qs)) :: ?Rs) ?m |- _ =>
      merge_pair H Ps Qs constr_eqb (merge_seps_at_indices_same m) ||
      merge_pair H Ps Qs same_addr_and_pred (merge_seps_at_indices_same_addr_and_pred m) ||
      (eapply merge_seps_done in H; cbn [seps] in H)
  end.

Ltac after_if :=
  repeat match goal with
         | H: sep _ _ ?M |- _ => clear M H
         end;
  intros;
  repeat pull_dlet_and_exists_step;
  repeat merge_and_pair constr_eqb merge_ands_at_indices_same_prop;
  repeat merge_and_pair neg_prop merge_ands_at_indices_neg_prop;
  repeat merge_and_pair same_lhs merge_ands_at_indices_same_lhs;
  repeat merge_and_pair seps_about_same_mem merge_ands_at_indices_seps_same_mem;
  repeat merge_sep_pair_step;
  repeat match goal with
  | H: if _ then ands nil else ands nil |- _ => clear H
  end;
  repeat lazymatch goal with
         | H: reconstruct _ _ = (if _ then _ else _) |- _ =>
             rewrite push_if_reconstruct in H; cbn [zip_tuple_if List.length] in H
         end;
  repeat lazymatch goal with
         | H: reconstruct _ _ = reconstruct _ _ |- _ =>
             eapply invert_reconstruct_eq in H; [ | reflexivity]
         end;
  try (lazymatch goal with
       | |- wp_cmd _ _ _ _ (reconstruct ?names ?tup) _ =>
           destruct_locals_after_merge tup names
       end).

Inductive snippet :=
| SAssign(is_decl: bool)(x: string)(e: Syntax.expr)
| SStore(sz: access_size)(addr val: Syntax.expr)
| SIf(cond: Syntax.expr)
| SElse
| SWhile(cond: Syntax.expr){Measure: Type}(measure0: Measure)
| SStart
| SEnd
| SRet(xs: list string)
| SEmpty.

Ltac assign is_decl name val :=
  eapply (wp_set _ name val);
  eval_expr;
  [.. (* maybe some unsolved side conditions *)
  | try ((* to simplify value that will become bound with :=, at which point
            rewrites will not apply any more *)
         repeat word_simpl_step_in_goal;
         put_into_current_locals is_decl) ].

Ltac store sz addr val :=
  eapply (wp_store _ sz addr val);
  eval_expr;
  [.. (* maybe some unsolved side conditions *)
  | lazymatch goal with
    | |- get_option (Memory.store access_size.one _ _ _) _ =>
        eapply store_byte_of_sep_cps; after_mem_modifying_lemma
    | |- get_option (Memory.store access_size.word _ _ _) _ =>
        eapply store_word_of_sep_cps; after_mem_modifying_lemma
    | |- get_option (Memory.store ?sz _ _ _) _ =>
        fail 10000 "storing" sz "not yet supported"
    | |- _ => pose_err Error:("eval_expr_step should not fail on this goal")
    end ].

Ltac cond c :=
  lazymatch goal with
  | |- wp_cmd _ _ ?t ?m (reconstruct ?vars ?vals) _ =>
    eapply (wp_if_bool_dexpr _ c vars vals);
    [ eval_dexpr
    | let b := fresh "Scope0" in pose proof (mk_scope_marker ThenBranch) as b; intro
    | let b := fresh "Scope0" in pose proof (mk_scope_marker ElseBranch) as b; intro
    | ]
  end.

Ltac els :=
  assert_scope_kind ThenBranch;
  eapply wp_skip;
  eexists; split; [ reflexivity | ];
  package_context.

Ltac clear_until_LoopInvariant_marker :=
  repeat match goal with
         | x: ?T |- _ => lazymatch T with
                         | scope_marker LoopInvariant => fail 1
                         | _ => clear x
                         end
         end;
  match goal with
  | x: ?T |- _ => lazymatch T with
                  | scope_marker LoopInvariant => clear x
                  end
  end.

Ltac expect_and_clear_last_marker expected :=
  lazymatch goal with
  | H: scope_marker ?sk |- _ =>
      tryif constr_eq sk expected then
        clear H
      else
        fail "Assertion failure: Expected last marker to be" expected "but got" sk
  end.

Ltac while cond measure0 :=
  eapply (wp_while measure0 cond);
  [ package_context
  | eauto with wf_of_type
  | repeat match goal with
           | H: sep _ _ ?M |- _ => clear M H
           end;
    clear_until_LoopInvariant_marker;
    cbv beta iota delta [ands];
    cbn [seps] in *;
    (* Note: will also appear after loop, where we'll have to clear it,
       but we have to pose it here because the foralls are shared between
       loop body and after the loop *)
    (let n := fresh "Scope0" in pose proof (mk_scope_marker LoopBody) as n);
    intros;
    fwd;
    lazymatch goal with
    | |- exists P, dexpr_bool_prop _ _ _ P /\
                   (P -> wp_cmd _ _ _ _ _ _) /\
                   (~P -> wp_cmd _ _ _ _ _ _) => idtac
    | |- _ => fail "assertion failure: hypothesis of wp_while has unexpected shape"
    end;
    eexists;
    split;
    [ (* evaluate condition *)
      repeat eval_dexpr_step
    | split; intros;
      [ (* loop body *)
      | (* after loop *)
        expect_and_clear_last_marker LoopBody ]
    ] ].

Create HintDb prove_post.

Ltac prove_concrete_post :=
    repeat match goal with
           | H: List.length ?l = S _ |- _ =>
               is_var l; destruct l;
               [ discriminate H
               | cbn [List.length] in H; eapply Nat.succ_inj in H ]
           | H: List.length ?l = O |- _ =>
               is_var l; destruct l;
               [ clear H
               | discriminate H ]
           end;
    repeat match goal with
           | x := _ |- _ => subst x
           end;
    destruct_bool_vars;
    repeat match goal with
           | H: ands (_ :: _) |- _ => destruct H
           | H: ands nil |- _ => clear H
           end;
    cbn [List.app List.firstn List.nth] in *;
    repeat match goal with
           | |- exists _, _ => eexists
           | |- _ /\ _ => split
           | |- ?x = ?x => reflexivity
           | |- sep _ _ _ => ecancel_assumption
           end;
    try congruence;
    try ZnWords;
    intuition (congruence || ZnWords || eauto with prove_post).

Ltac ret retnames :=
  lazymatch goal with
  | B: scope_marker ?sk |- _ =>
      lazymatch sk with
      | FunctionBody => idtac
      | ThenBranch => fail "return inside a then-branch is not supported"
      | ElseBranch => fail "return inside an else-branch is not supported"
      | LoopBody => fail "return inside a loop body is not supported"
      end
  | |- _ => fail "block structure lost (could not find a scope_marker)"
  end;
  eapply wp_skip;
  lazymatch goal with
  | |- exists _, map.getmany_of_list _ ?eretnames = Some _ /\ _ =>
    unify eretnames retnames;
    eexists; split; [reflexivity|cbn [PrimitivePair.pair._1 PrimitivePair.pair._2]]
  end.

Ltac close_block :=
  lazymatch goal with
  | B: scope_marker ?sk |- _ =>
      lazymatch sk with
      | ElseBranch =>
          eapply wp_skip;
          eexists; split; [ reflexivity | ];
          package_context
      | LoopBody =>
          eapply wp_skip;
          prove_concrete_post
      | FunctionBody =>
          lazymatch goal with
          | |- wp_cmd _ _ _ _ _ _ => ret (@nil string)
          | |- _ => idtac (* ret nonEmptyVarList was already called *)
          end;
          prove_concrete_post
      | _ => fail "Can't end a block here"
      end
  | _ => fail "no scope marker found"
  end.

Ltac prettify_goal :=
  lazymatch goal with
  | |- _ =>
      cbv beta in *;
      after_if
  end.

Ltac add_snippet s :=
  assert_no_error;
  lazymatch s with
  | SAssign ?is_decl ?y ?e => assign is_decl y e
  | SStore ?sz ?addr ?val => store sz addr val
  | SIf ?e => cond e
  | SElse => els
  | SWhile ?cond ?measure0 => while cond measure0
  | SStart => start
  | SEnd => close_block
  | SRet ?retnames => ret retnames
  | SEmpty => prettify_goal
  end.

Ltac after_snippet :=
  fwd;
  (* leftover from word_simpl_step_in_hyps, TODO where to put? in fwd? *)
  repeat match goal with
         | H: ?x = ?y |- _ => is_var x; is_var y; subst x
         end.

(* Note: An rhs_var appears in expressions and, in our setting, always has a corresponding
   var (of type word) bound in the current context, whereas an lhs_var may or may not be
   bound in the current context, if not bound, a new entry will be added to current_locals. *)

Declare Custom Entry rhs_var.
Notation "x" :=
  (match x with
   | _ => ltac2:(exact_varconstr_as_string (Ltac2.Constr.pretype x))
   end)
  (in custom rhs_var at level 0, x constr at level 0, only parsing).

Declare Custom Entry var_or_literal.
Notation "x" :=
  (match x with
   | _ => ltac:(lazymatch isZcst x with
                | true => refine (expr.literal _); exact x
                | false => refine (expr.var _); exact_varconstr_as_string x
                end)
   end)
  (in custom var_or_literal at level 0, x constr at level 0, only parsing).

Declare Custom Entry lhs_var.
Notation "x" := (ident_to_string x)
  (in custom lhs_var at level 0, x constr at level 0, only parsing).

Declare Custom Entry rhs_var_list.
Notation "x" := (cons x nil)
  (in custom rhs_var_list at level 0, x custom rhs_var at level 0, only parsing).
Notation "h , t" := (cons h t)
  (in custom rhs_var_list at level 0,
   h custom rhs_var at level 0,
   t custom rhs_var_list at level 0,
   only parsing).

Declare Custom Entry live_expr.

Notation "x" := x
  (in custom live_expr at level 0, x custom var_or_literal at level 0, only parsing).

Notation "live_expr:( e )" := e
  (e custom live_expr at level 100, only parsing).

Notation "( e )" := e (in custom live_expr, e custom live_expr at level 100).

(* Using the same precedences as https://en.cppreference.com/w/c/language/operator_precedence *)
Notation "! x" := (expr.op bopname.eq x (expr.literal 0))
  (in custom live_expr at level 2, x custom live_expr, right associativity, only parsing).
Infix "*" := (expr.op bopname.mul)
  (in custom live_expr at level 3, left associativity, only parsing).
Infix "/" := (expr.op bopname.divu)
  (in custom live_expr at level 3, left associativity, only parsing).
Infix "%" := (expr.op bopname.remu)
  (in custom live_expr at level 3, left associativity, only parsing).
Infix "+" := (expr.op bopname.add)
  (in custom live_expr at level 4, left associativity, only parsing).
Infix "-" := (expr.op bopname.sub)
  (in custom live_expr at level 4, left associativity, only parsing).
Infix "<<" := (expr.op bopname.slu)
  (in custom live_expr at level 5, left associativity, only parsing).
Infix ">>" := (expr.op bopname.sru)
  (in custom live_expr at level 5, left associativity, only parsing).
Infix "<" := (expr.op bopname.ltu)
  (in custom live_expr at level 6, no associativity, only parsing).
Notation "a <= b" := (expr.op bopname.eq (expr.op bopname.ltu b a) (expr.literal 0))
  (in custom live_expr at level 6, a custom live_expr, b custom live_expr,
   no associativity, only parsing).
Notation "a > b" := (expr.op bopname.ltu b a)
  (in custom live_expr at level 6, a custom live_expr, b custom live_expr,
   no associativity, only parsing).
Notation "a >= b" := (expr.op bopname.eq (expr.op bopname.ltu a b) (expr.literal 0))
  (in custom live_expr at level 6, a custom live_expr, b custom live_expr,
   no associativity, only parsing).
Infix "==" := (expr.op bopname.eq)
  (in custom live_expr at level 7, no associativity, only parsing).
Infix "&" := (expr.op bopname.and)
  (in custom live_expr at level 8, left associativity, only parsing).
Infix "^" := (expr.op bopname.xor)
  (in custom live_expr at level 9, left associativity, only parsing).
Infix "|" := (expr.op bopname.or)
  (in custom live_expr at level 10, left associativity, only parsing).
Infix "&&" := expr.lazy_and
  (in custom live_expr at level 11, left associativity, only parsing).
Infix "||" := expr.lazy_or
  (in custom live_expr at level 12, left associativity, only parsing).
Notation "c ? e1 : e2" := (expr.ite c e1 e2)
  (in custom live_expr at level 13, right associativity, only parsing).

Notation "load1( a )" := (expr.load access_size.one a)
  (in custom live_expr at level 0, a custom live_expr at level 100, only parsing).
Notation "load2( a )" := (expr.load access_size.two a)
  (in custom live_expr at level 0, a custom live_expr at level 100, only parsing).
Notation "load4( a )" := (expr.load access_size.four a)
  (in custom live_expr at level 0, a custom live_expr at level 100, only parsing).
Notation  "load( a )" := (expr.load access_size.word a)
  (in custom live_expr at level 0, a custom live_expr at level 100, only parsing).

Goal forall (word: Type) (x: word),
    live_expr:(x + 3) = expr.op bopname.add (expr.var "x") (expr.literal 3).
Proof. intros. reflexivity. Abort.

Goal forall (word: Type) (x: word),
  live_expr:(x <= 3) =
  expr.op bopname.eq (expr.op bopname.ltu (expr.literal 3) (expr.var "x")) (expr.literal 0).
Proof. intros. reflexivity. Abort.

Declare Custom Entry snippet.

Notation "*/ s /*" := s (s custom snippet at level 100).
Notation "*/ /*" := SEmpty.
Notation "x = e ;" := (SAssign false x e) (* rhs as in "already declared" (but still on lhs) *)
  (in custom snippet at level 0, x custom rhs_var at level 100, e custom live_expr at level 100).
Notation "'uintptr_t' x = e ;" := (SAssign true x e)
  (in custom snippet at level 0, x custom lhs_var at level 100, e custom live_expr at level 100).
Notation "store1( a , v ) ;" := (SStore access_size.one a v)
  (in custom snippet at level 0,
   a custom live_expr at level 100, v custom live_expr at level 100).
Notation "store2( a , v ) ;" := (SStore access_size.two a v)
  (in custom snippet at level 0,
   a custom live_expr at level 100, v custom live_expr at level 100).
Notation "store4( a , v ) ;" := (SStore access_size.four a v)
  (in custom snippet at level 0,
   a custom live_expr at level 100, v custom live_expr at level 100).
Notation "store( a , v ) ;" := (SStore access_size.word a v)
  (in custom snippet at level 0,
   a custom live_expr at level 100, v custom live_expr at level 100).
Notation "'return' l ;" := (SRet l)
  (in custom snippet at level 0, l custom rhs_var_list at level 1).

Notation "'if' ( e ) {" := (SIf e) (in custom snippet at level 0, e custom live_expr).
Notation "{" := SStart (in custom snippet at level 0).
Notation "}" := SEnd (in custom snippet at level 0).
Notation "} 'else' {" := SElse (in custom snippet at level 0).

Notation "'while' ( e ) /* 'decreases' m */ {" :=
  (SWhile e m) (in custom snippet at level 0, e custom live_expr, m constr at level 0).

Tactic Notation "#" constr(s) := add_snippet s; after_snippet.

Set Ltac Backtrace.

(* COQBUG (performance) https://github.com/coq/coq/issues/10743#issuecomment-530673037
   Probably fixed on master *)
Ltac cond_hyp_factor :=
  repeat match goal with
         | H : ?x -> _, H' : ?x -> _ |- _  =>
           pose proof (fun u : x => conj (H u) (H' u)); clear H H'
         end.

(* probably not needed any more in recent versions *)
Ltac adhoc_lia_performance_fixes :=
  repeat match goal with
         | H: ?P -> _ |- _ => assert_succeeds (assert (~ P) by (clear; Lia.lia)); clear H
         end;
  repeat match goal with
         | H: ?P -> _ |- _ => let A := fresh in (assert P as A by (clear; Lia.lia));
                              specialize (H A); clear A
         end;
  cond_hyp_factor;
  subst.

Require Import coqutil.Sorting.Permutation.

Load LiveVerif.
Close Scope sepcl_scope.

(* Note: If you re-import ZnWords after this, you'll get the old better_lia again *)
Ltac better_lia ::=
  Z.div_mod_to_equations;
  adhoc_lia_performance_fixes;
  Lia.lia.

Local Set Default Goal Selector "1".

Tactic Notation ".*" constr(s) "*" := add_snippet s; after_snippet.

Comments C_STARTS_HERE
/**.

Definition u_min: {f: list string * list string * cmd &
  forall fs t m a b (R: mem -> Prop),
    R m ->
    vc_func fs f t m [| a; b |] (fun t' m' retvs =>
      t' = t /\ R m' /\
      (word.unsigned a <  word.unsigned b /\ retvs = [a] \/
       word.unsigned b <= word.unsigned a /\ retvs = [b])
  )}.                                                                           .**/
{                                                                          /**. .**/
  uintptr_t r = 0;                                                         /**. .**/
  if (a < b) {                                                             /**. .**/
    r = a;                                                                 /**. .**/
  } else {                                                                 /**. .**/
    r = b;                                                                 /**. .**/
  }                                                                        /**. .**/
                                                                           /**. .**/
  return r;                                                                /**. .**/
}                                                                          /**.
Defined.

Close Scope live_scope_prettier.
Unset Implicit Arguments.

  Require Import FunctionalExtensionality.
  Require Import Coq.Logic.PropExtensionality.

  Lemma word__ltu_wf: well_founded (fun x y: word => word.unsigned x < word.unsigned y).
  Proof.
    epose proof (well_founded_ltof _ (fun (w: word) => Z.to_nat (word.unsigned w))) as P.
    unfold ltof in P.
    eqapply P.
    extensionality a. extensionality b. eapply propositional_extensionality.
    split; ZnWords.
  Qed.

(* Assigns default well_founded relations to types.
   Use lower costs to override existing entries. *)
Create HintDb wf_of_type.
Hint Resolve word__ltu_wf | 4 : wf_of_type.

Section WithNonmaximallyInsertedA.
  Context [A: Type].

  Lemma List__repeat_0: forall (a: A), List.repeat a 0 = [].
  Proof. intros. reflexivity. Qed.
End WithNonmaximallyInsertedA.

Hint Rewrite List__repeat_0 : fwd_rewrites.

Ltac word_simpl_step_in_goal ::=
  match goal with
  | |- context[@word.add ?wi ?wo ?x ?y] => progress (ring_simplify (@word.add wi wo x y))
  | |- context[@word.sub ?wi ?wo ?x ?y] => progress (ring_simplify (@word.sub wi wo x y))
  | |- context[@word.opp ?wi ?wo ?x   ] => progress (ring_simplify (@word.opp wi wo x  ))
  | |- context[@word.mul ?wi ?wo ?x ?y] => progress (ring_simplify (@word.mul wi wo x y))
  | |- context C[word.unsigned ?x] =>
      let x' := rdelta_var x in
      lazymatch x' with
      | word.of_Z ?z =>
          (tryif constr_eq x x' then idtac
           (* don't subst x everywhere, but only where the rewrite can simplify something *)
           else let C' := context C[word.unsigned x'] in change C');
          rewrite (word.unsigned_of_Z_nowrap z) by Lia.lia
      end
  | _ => progress groundcbv_in_goal
  end.

Require Import coqutil.Tactics.syntactic_unify.

Ltac solve_list_eq :=
  list_simpl_in_goal; try syntactic_exact_deltavar (@eq_refl _ _).

(* make t1 a constr instead of pattern because typeclass-based notations
   don't work in patterns *)
Tactic Notation "Replace" constr(t1) "with" constr(t2) "in" ident(H) :=
  replace t1 with t2 in H.
Tactic Notation "Replace" constr(t1) "with" constr(t2) "in" "*" :=
  replace t1 with t2 in *.
Tactic Notation "Replace" constr(t1) "with" constr(t2) :=
  replace t1 with t2.
Tactic Notation "Replace" constr(t1) "with" constr(t2) "in" ident(H) "by" tactic(tac) :=
  replace t1 with t2 in H by tac.
Tactic Notation "Replace" constr(t1) "with" constr(t2) "in" "*" "by" tactic(tac) :=
  replace t1 with t2 in * by tac.
Tactic Notation "Replace" constr(t1) "with" constr(t2) "by" tactic(tac) :=
  replace t1 with t2 by tac.

Tactic Notation "loop" "invariant" "above" ident(i) :=
  let n := fresh "Scope0" in pose proof (mk_scope_marker LoopInvariant) as n;
  move n after i.

Definition memset: {f: list string * list string * cmd &
  forall fs t m (a b n: word) (bs: list byte) (R: mem -> Prop),
    <{ * a --> bs
       * R }> m ->
    word.unsigned n = Z.of_nat (List.length bs) ->
    vc_func fs f t m [| a; b; n |] (fun t' m' retvs =>
      t' = t /\
      <{ * a --> List.repeat (byte.of_Z (word.unsigned b)) (List.length bs)
         * R }> m' /\
      retvs = nil)
  }.
.**/
{                                                                        /**. .**/
  uintptr_t i = 0;                                                       /**.

Replace bs with (repeat (b to byte) (i to nat) ++ bs[i to nat :]) in H by solve_list_eq.
loop invariant above i.
move H0 before R. (* not strictly needed *)
assert (0 <= i to Z <= n to Z) by ZnWords.
clearbody i.
.**/
  while (i < n) /* decreases (n - i) */ {                                /**. .**/
    store1(a + i, b);                                                    /**.

(* TODO: automate prettification steps below *)
rewrite Z.div_1_r in *.
rewrite List.repeat_length in *.
Replace (S (i to nat) - i to nat + i to nat) with (i to nat + 1%nat) in * by ZnWords.

.**/
     i = i + 1;                                                          /**. .**/
  }                                                                      /**.

{
  Replace ((i_0 + 1 to word) to nat) with (i_0 to nat + 1 to nat) by ZnWords.
  rewrite List.repeat_app.
  rewrite <- List.app_assoc.
  assumption.
}

  fwd.
  Replace (i to nat) with (List.length bs) in * by ZnWords.
.**/
}                                                                        /**.
Defined.

Goal False.
  let r := eval unfold memset in
  match memset with
  | existT _ f _ => f
  end in pose r.
Abort.

Definition merge_tests: {f: list string * list string * cmd &
  forall fs t (m: mem) (a: word) (vs: list word) R,
    <{ * a --> vs
       * R }> m ->
    List.length vs = 3%nat ->
    vc_func fs f t m [| a |] (fun t' m' retvs => False)
  }. .**/
{                                                                        /**. .**/
  uintptr_t w0 = load(a);                                                /**. .**/
  uintptr_t w1 = load(a+4);                                              /**. .**/
  uintptr_t w2 = load(a+8);                                              /**. .**/
  if (w1 < w0 && w1 < w2) {                                              /**. .**/
    store(a, w1);                                                        /**. .**/
    w1 = w0;                                                             /**.

assert (exists foo: Z, foo + foo = 2) as Foo. {
  exists 1. reflexivity.
}
destruct Foo as (foo & Foo).

move m at bottom.
move w1 at bottom.

assert (exists bar: nat, (bar + bar = 4 * Z.to_nat foo)%nat) as Bar. {
  exists 2%nat. blia.
}
destruct Bar as (bar & Bar).
pose (baz := foo + foo).
assert (w1 + w0 + word.of_Z baz = word.of_Z baz + w1 + w1) as E by ZnWords.
rename w1 into w1tmp.
pose (w1 := w0 + word.of_Z baz - word.of_Z baz).
move w1 after w1tmp.
replace w1tmp with w1 in * by ZnWords. clear w1tmp.

.**/
  } else {                                                               /**. .**/
}                                                                        /**. .**/
                                                                         /**.
Abort.

Hint Extern 4 (Permutation _ _) =>
  eauto using perm_nil, perm_skip, perm_swap, perm_trans
: prove_post.

Definition sort3: {f: list string * list string * cmd &
  forall fs t (m: mem) (a: word) (vs: list word) R,
    <{ * a --> vs
       * R }> m ->
    List.length vs = 3%nat ->
    vc_func fs f t m [| a |] (fun t' m' retvs =>
      exists v0 v1 v2,
        t' = t /\
        Permutation vs [| v0; v1; v2 |] /\
        v0 to Z <= v1 to Z <= v2 to Z /\
        <{ * a --> [| v0; v1; v2 |]
           * R }> m'
  )}. .**/
{                                                                        /**. .**/
  uintptr_t w0 = load(a);                                                /**. .**/
  uintptr_t w1 = load(a+4);                                              /**. .**/
  uintptr_t w2 = load(a+8);                                              /**. .**/
  if (w1 <= w0 && w1 <= w2) {                                            /**. .**/
    store(a, w1);                                                        /**. .**/
    w1 = w0;                                                             /**. .**/
  } else {                                                               /**. .**/
    if (w2 <= w0 && w2 <= w1) {                                          /**. .**/
      store(a, w2);                                                      /**. .**/
      w2 = w0;                                                           /**. .**/
    } else {                                                             /**. .**/
    }                                                          /**. .**/ /**. .**/
  }                                                            /**. .**/ /**. .**/
  if (w2 < w1) {                                                         /**. .**/
    store(a+4, w2);                                                      /**. .**/
    store(a+8, w1);                                                      /**. .**/
  } else {                                                               /**. .**/
    store(a+4, w1);                                                      /**. .**/
    store(a+8, w2);                                                      /**. .**/
  }                                                            /**. .**/ /**. .**/
}                                                                        /**.
Defined.

(* Print Assumptions sort3. *)

(* TODO: write down postcondition only at end *)
Definition swap_locals: {f: list string * list string * cmd &
  forall fs tr m a b,
    vc_func fs f tr m [| a; b |] (fun tr' m' retvs =>
      tr' = tr /\ m' = m /\ retvs = [| b; a |]
  )}.
  (* note: we could just do skip and return ["b", "a"] *)                       .**/
{                                                                          /**. .**/
  uintptr_t t = a;                                                         /**. .**/
  a = b;                                                                   /**. .**/
  b = t;                                                                   /**. .**/
  uintptr_t res1 = a;                                                      /**. .**/
  uintptr_t res2 = b;                                                      /**. .**/
  return res1, res2;                                                       /**. .**/
}                                                                          /**.
Defined.

(* TODO: write down postcondition only at end *)
Definition swap: {f: list string * list string * cmd &
  forall fs t (m: mem) (a_addr b_addr a b: word) R,
    <{ * a_addr ~> a
       * b_addr ~> b
       * R
    }> m ->
    vc_func fs f t m [| a_addr; b_addr |] (fun t' m' retvs =>
      <{ * a_addr ~> b
         * b_addr ~> a
         * R
      }> m' /\ retvs = [] /\ t' = t
  )}.
#*/ {                                                                        /*.
#*/   uintptr_t t = load(a_addr);                                            /*.
#*/   store(a_addr, load(b_addr));                                           /*.
#*/   store(b_addr, t);                                                      /*.
#*/ }                                                                        /*.
Defined.

Goal False.
  let r := eval unfold swap_locals in
  match swap_locals with
  | existT _ f _ => f
  end in pose r.
Abort.

Definition foo(a b: word): word := a + b.

Lemma test: forall a b, foo a b = foo b a.
Proof. unfold foo. intros. ring. Qed.

About test.
(* test : forall a b : word, foo a b = foo b a *)

End LiveVerif.

About test.
(*
test :
forall
  {word : word
            (BinNums.Zpos
               (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO (BinNums.xO BinNums.xH))))))},
word.ok word -> forall a b : word, foo a b = foo b a
 *)

Comments !EOF .**/ //.
