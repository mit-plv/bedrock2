Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import Coq.Init.Byte.
Require Import Coq.Strings.String.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require coqutil.Map.SortedListString. (* for function env, other maps are kept abstract *)
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Tactics.Tactics coqutil.Tactics.fwd.
Require Import coqutil.Datatypes.ListSet.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic bedrock2.Loops.
Require Import bedrock2.ZnWords.
Require Import bedrock2.SepLib.

(* A let-binding using an equality instead of :=, living in Prop.
   Equivalent to (exists x, x = rhs /\ body x).
   We don't use regular exists to make the intention recognizable by tactics.
   In particular, note that
     if c then exists x, x = rhs /\ P x else F
   implies
     exists x, if c then x = rhs /\ P x else F
   but this step is a bad step to apply, because it loses information:
   After destructing the exists, we can't pull the `x = rhs` out of the then-branch
   any more.
   However, if we pull out the exist and the equality at the same time, it works.
   (All of this assumes that the type of x is inhabited). *)
Inductive elet{A: Type}(rhs: A)(body: A -> Prop): Prop :=
| mk_elet(x: A)(_: x = rhs)(_: body x).

Section WithParams.
  Import bedrock2.Syntax.
  Context {width: Z} {BW: Bitwidth width} {word: word.word width} {word_ok: word.ok word}
          {mem: map.map word byte} {mem_ok: map.ok mem}
          {locals: map.map string word} {locals_ok: map.ok locals}
          {ext_spec: ExtSpec} {ext_spec_ok : ext_spec.ok ext_spec}.

  Lemma weaken_expr: forall m l e (post1 post2: word -> Prop),
      WeakestPrecondition.expr m l e post1 ->
      (forall v, post1 v -> post2 v) ->
      WeakestPrecondition.expr m l e post2.
  Proof.
    intros. eapply WeakestPreconditionProperties.Proper_expr; eassumption.
  Qed.

  (* "sealed" behind an Inductive, only the defining lemmas below unfold this definition *)
  Inductive dexpr{BW: Bitwidth width}(m: mem)(l: locals)(e: expr)(w: word): Prop :=
    mk_dexpr(_: WeakestPrecondition.dexpr m l e w).

  Lemma dexpr_literal: forall (m: mem) (l: locals) z,
      dexpr m l (expr.literal z) (word.of_Z z).
  Proof.
    intros. econstructor. cbn. unfold literal, dlet.dlet. reflexivity.
  Qed.

  Lemma dexpr_var: forall m (l: locals) x v,
      map.get l x = Some v ->
      dexpr m l (expr.var x) v.
  Proof.
    intros. econstructor. hnf. eauto.
  Qed.

  (* Notation instead of definition so that it auto-simplifies when applied to
     a concrete sz *)
  Notation access_size_to_nbits sz :=
    match sz with
    | access_size.one => 8
    | access_size.two => 16
    | access_size.four => 32
    | access_size.word => width
    end.

  (* Note: no conversion needed between v in sepclause and v returned,
     and sep already enforces bounds on v *)
  Lemma dexpr_load_uintptr: forall m l e addr v R,
      dexpr m l e addr ->
      sep (uintptr v addr) R m ->
      dexpr m l (expr.load access_size.word e) v.
  Proof.
    intros. constructor. hnf. inversion H; clear H. hnf in H1.
    eapply weaken_expr. 1: eassumption.
    intros. subst v0. hnf. eexists. split; [ | reflexivity].
    unfold uintptr, Scalars.scalar in *.
    rewrite Scalars.load_of_sep with (value := v) (R := R). 2: assumption.
    unfold Scalars.truncate_word, Scalars.truncate_Z.
    rewrite Z.land_ones by lia. f_equal.
    unfold bytes_per, bytes_per_word.
    destruct width_cases as [E|E]; subst width;
      try change (2 ^ _) with (2 ^ 32);
      try change (2 ^ _) with (2 ^ 64);
      ZnWords.
  Qed.

  (* Note: no conversion needed between v in sepclause and v returned,
     and sep already enforces bounds on v *)
  Lemma dexpr_load_uint: forall m l e addr sz v R,
      dexpr m l e addr ->
      sep (uint (access_size_to_nbits sz) v addr) R m ->
      dexpr m l (expr.load sz e) (word.of_Z v).
  Proof.
    intros. constructor. hnf. inversion H; clear H. hnf in H1.
    eapply weaken_expr. 1: eassumption.
    intros. subst v0. hnf. eexists. split; [ | reflexivity].
    unfold uint in *. eapply sep_assoc in H0. eapply sep_emp_l in H0.
    destruct H0 as (B & M).
    rewrite Scalars.load_of_sep with (value := word.of_Z v) (R := R).
    - unfold Scalars.truncate_word, Scalars.truncate_Z.
      rewrite Z.land_ones by lia. f_equal.
      unfold bytes_per, bytes_per_word.
      destruct sz; destruct width_cases as [E|E]; subst width;
        try change (2 ^ _) with (2 ^ 32);
        try change (2 ^ _) with (2 ^ 64);
        ZnWords.
    - unfold Scalars.truncated_word, Scalars.truncated_scalar, bytes_per.
      destruct sz; cbn in M;
        (rewrite word.unsigned_of_Z_nowrap;
         [try assumption|destruct width_cases as [E|E]; subst width; lia]).
      eqapply M. f_equal.
      destruct width_cases as [E|E]; subst width; reflexivity.
  Qed.

  (* TODO later: dexpr_inlinetable *)

  Lemma dexpr_binop: forall m l op e1 e2 (v1 v2: word),
      dexpr m l e1 v1 ->
      dexpr m l e2 v2 ->
      dexpr m l (expr.op op e1 e2) (interp_binop op v1 v2).
  Proof.
    intros. inversion H; clear H. inversion H0; clear H0.
    constructor. hnf in H, H1|-*.
    eapply weaken_expr. 1: eassumption.
    intros. subst.
    eapply weaken_expr. 1: eassumption.
    intros. subst. reflexivity.
  Qed.

  Definition dexpr_binop_unf :=
    ltac:(let T := type of dexpr_binop in
          let Tu := eval unfold interp_binop in T in
          exact (dexpr_binop: Tu)).

  Lemma dexpr_ite: forall m l e1 e2 e3 (b v: word),
      dexpr m l e1 b ->
      dexpr m l (if word.eqb b (word.of_Z 0) then e3 else e2) v ->
      dexpr m l (expr.ite e1 e2 e3) v.
  Proof.
    intros. inversion H; clear H. inversion H0; clear H0. constructor.
    hnf in H1,H|-*. eapply weaken_expr. 1: eassumption.
    intros. subst v0. assumption.
  Qed.

  (* Like dexpr, but with an additional P that needs to hold. P tags along
     because it doesn't want to miss the updates to the symbolic state that
     evaluating e might make. *)
  Inductive dexpr1(m: mem)(l: locals)(e: expr)(v: word)(P: Prop): Prop :=
  | mk_dexpr1(Hde: dexpr m l e v)(Hp: P).

  Lemma dexpr1_literal: forall (m: mem) (l: locals) z (P: Prop),
      P -> dexpr1 m l (expr.literal z) (word.of_Z z) P.
  Proof.
    intros. constructor. 2: assumption. eapply dexpr_literal.
  Qed.

  Lemma dexpr1_var: forall m (l: locals) x v (P: Prop),
      map.get l x = Some v ->
      P ->
      dexpr1 m l (expr.var x) v P.
  Proof.
    intros. constructor. 2: assumption. eapply dexpr_var; eassumption.
  Qed.

  Lemma dexpr1_load_uintptr: forall m l e addr v (R: mem -> Prop) (P: Prop),
      dexpr1 m l e addr (sep (uintptr v addr) R m /\ P) ->
      dexpr1 m l (expr.load access_size.word e) v P.
  Proof.
    intros. inversion H; clear H. fwd. constructor. 2: assumption.
    eapply dexpr_load_uintptr; eassumption.
  Qed.

  Lemma dexpr1_load_uint: forall m l e addr sz v (R: mem -> Prop) (P: Prop),
      dexpr1 m l e addr (sep (uint (access_size_to_nbits sz) v addr) R m /\ P) ->
      dexpr1 m l (expr.load sz e) (word.of_Z v) P.
  Proof.
    intros. inversion H; clear H. fwd. constructor. 2: assumption.
    eapply dexpr_load_uint; eassumption.
  Qed.

  (* TODO later: dexpr1_inlinetable *)

  Lemma dexpr1_binop: forall m l op e1 e2 (v1 v2: word) P,
      dexpr1 m l e1 v1 (dexpr1 m l e2 v2 P) ->
      dexpr1 m l (expr.op op e1 e2) (interp_binop op v1 v2) P.
  Proof.
    intros.
    inversion H. clear H. inversion Hp. clear Hp.
    constructor. 2: assumption. eapply dexpr_binop; assumption.
  Qed.

  Definition dexpr1_binop_unf :=
    ltac:(let T := type of dexpr1_binop in
          let Tu := eval unfold interp_binop in T in
          exact (dexpr1_binop: Tu)).

  Definition bool_expr_branches(b: bool)(Pt Pf Pa: Prop): Prop :=
    (if b then Pt else Pf) /\ Pa.

  (* `dexpr_bool3 m l e c Ptrue Pfalse Palways` means "expression e evaluates to
     boolean c and if c is true, Ptrue holds, if c is false, Pfalse holds, and
     Palways always holds".
     The three Props Ptrue, Pfalse, Palways are included so that changes made to
     the symbolic state while evaluating e are still visible when continuing the
     evaluation of the program as specified by the three Props.
     They are split into three Props rather than one in order to propagate changes
     to the symbolic state made while evaluating the condition of an if into the
     then and else branches. *)
  Inductive dexpr_bool3(m: mem)(l: locals)(e: expr): bool -> Prop -> Prop -> Prop -> Prop :=
    mk_dexpr_bool3: forall (v: word) (c: bool) (Ptrue Pfalse Palways: Prop),
      dexpr m l e v ->
      c = negb (word.eqb v (word.of_Z 0)) ->
      bool_expr_branches c Ptrue Pfalse Palways ->
      dexpr_bool3 m l e c Ptrue Pfalse Palways.

  Lemma dexpr_bool3_not: forall m l e b (Pt Pf Pa: Prop),
      dexpr_bool3 m l e b
        True True (* <-- can't use these because that would flip proving order *)
        (bool_expr_branches (negb b) Pt Pf Pa) ->
      dexpr_bool3 m l (expr.not e) (negb b) Pt Pf Pa.
  Proof.
    intros. inversion H. clear H. subst.
    rewrite Bool.negb_involutive in *. unfold bool_expr_branches in *. fwd.
    econstructor.
    - eapply dexpr_binop. 1: eassumption.
      eapply dexpr_literal.
    - cbn. destruct_one_match;
        rewrite word.unsigned_eqb;
        rewrite !word.unsigned_of_Z_nowrap by
          (destruct width_cases as [W|W]; rewrite W in *; lia);
        reflexivity.
    - unfold bool_expr_branches. destruct_one_match; eauto.
  Qed.

  (* note how each of Pt, Pf, Pa is only mentioned once in the hyp, and that Pt is
     as deep down as possible, so that it can see all memory modifications once it
     gets proven *)
  Lemma dexpr_bool3_lazy_and: forall m l e1 e2 (b1 b2: bool) (Pt Pf Pa: Prop),
      dexpr_bool3 m l e1 b1
        (dexpr_bool3 m l e2 b2 Pt True True)
        True
        (bool_expr_branches (andb b1 b2) True Pf Pa) ->
      dexpr_bool3 m l (expr.lazy_and e1 e2) (andb b1 b2) Pt Pf Pa.
  Proof.
    intros.
    inversion H; subst. clear H. unfold bool_expr_branches in *. fwd.
    destruct (word.eqb v (word.of_Z 0)) eqn: E.
    - econstructor; [eapply dexpr_ite; [eassumption | rewrite E ]
                    | unfold bool_expr_branches; auto .. ].
      1: eapply dexpr_literal. rewrite word.eqb_eq; reflexivity.
    - cbn in *.
      inversion H2p0. clear H2p0. unfold bool_expr_branches in *. subst.
      econstructor.
      1: eapply dexpr_ite. 1: eassumption. 1: rewrite E.
      1: eapply dexpr_binop. 1: eapply dexpr_literal. 1: eassumption.
      { cbn. rewrite word.unsigned_ltu.
        destr (word.eqb v0 (word.of_Z 0));
          rewrite !word.unsigned_of_Z_nowrap by
          (destruct width_cases as [W|W]; rewrite W in *; lia); cbn.
        - rewrite word.eqb_eq; reflexivity.
        - destruct_one_match; rewrite word.unsigned_eqb;
            rewrite !word.unsigned_of_Z_nowrap by
            (destruct width_cases as [W|W]; rewrite W in *; lia).
          + reflexivity.
          + exfalso. pose proof (word.unsigned_range v0).
            apply E0. eapply word.unsigned_inj. rewrite word.unsigned_of_Z_0. lia. }
      { unfold bool_expr_branches. destruct_one_match; fwd; auto. }
  Qed.

  Lemma dexpr_bool3_lazy_or: forall m l e1 e2 (b1 b2: bool) (Pt Pf Pa: Prop),
      dexpr_bool3 m l e1 b1
        True
        (dexpr_bool3 m l e2 b2 True True True)
        (bool_expr_branches (orb b1 b2) Pt Pf Pa) ->
      dexpr_bool3 m l (expr.lazy_or e1 e2) (orb b1 b2) Pt Pf Pa.
  Proof.
    intros.
    inversion H; subst. clear H. unfold bool_expr_branches in *. fwd.
    destruct (word.eqb v (word.of_Z 0)) eqn: E.
    - cbn in *.
      inversion H2p0. subst. clear H2p0.
      econstructor. 1: eapply dexpr_ite. 1: eassumption. 1: rewrite E.
      1: eapply dexpr_binop. 1: eapply dexpr_literal.
      1: eassumption.
      1: cbn.
      2: destruct (word.eqb v0 (word.of_Z 0)); cbn; unfold bool_expr_branches in *;
         intuition auto.
      cbn. rewrite word.unsigned_ltu.
      destr (word.eqb v0 (word.of_Z 0));
        rewrite !word.unsigned_of_Z_nowrap by
        (destruct width_cases as [W|W]; rewrite W in *; lia); cbn.
      + rewrite word.eqb_eq; reflexivity.
      + destruct_one_match; rewrite word.unsigned_eqb;
          rewrite !word.unsigned_of_Z_nowrap by
          (destruct width_cases as [W|W]; rewrite W in *; lia).
        * reflexivity.
        * exfalso. pose proof (word.unsigned_range v0).
          apply E0. eapply word.unsigned_inj. rewrite word.unsigned_of_Z_0. lia.
    - cbn in *.
      econstructor. 3: unfold bool_expr_branches; auto.
      1: eapply dexpr_ite. 1: eassumption. 1: rewrite E.
      1: eapply dexpr_literal.
      rewrite word.unsigned_eqb;
        rewrite !word.unsigned_of_Z_nowrap by
        (destruct width_cases as [W|W]; rewrite W in *; lia).
      reflexivity.
  Qed.

  Lemma dexpr_bool3_to_dexpr1: forall m l e b (Pt Pf Pa: Prop),
      dexpr1 m l e b (bool_expr_branches (negb (word.eqb b (word.of_Z 0))) Pt Pf Pa) ->
      dexpr_bool3 m l e (negb (word.eqb b (word.of_Z 0))) Pt Pf Pa.
  Proof.
    intros. inversion H. clear H. inversion Hp. clear Hp.
    econstructor.
    - eassumption.
    - reflexivity.
    - unfold bool_expr_branches. split; assumption.
  Qed.

  Lemma dexpr_bool3_ltu: forall m l e1 e2 v1 v2 (Pt Pf Pa: Prop),
      dexpr1 m l e1 v1 (dexpr1 m l e2 v2 (bool_expr_branches (word.ltu v1 v2) Pt Pf Pa)) ->
      dexpr_bool3 m l (expr.op bopname.ltu e1 e2) (word.ltu v1 v2) Pt Pf Pa.
  Proof.
    intros. inversion H. clear H. inversion Hp. clear Hp.
    econstructor.
    - eapply dexpr_binop; eassumption.
    - cbn. destruct_one_match;
        rewrite word.unsigned_eqb, ?word.unsigned_of_Z_1, ?word.unsigned_of_Z_0;
        reflexivity.
    - assumption.
  Qed.

  Lemma dexpr_bool3_eq: forall m l e1 e2 v1 v2 (Pt Pf Pa: Prop),
      dexpr1 m l e1 v1 (dexpr1 m l e2 v2 (bool_expr_branches (word.eqb v1 v2) Pt Pf Pa)) ->
      dexpr_bool3 m l (expr.op bopname.eq e1 e2) (word.eqb v1 v2) Pt Pf Pa.
  Proof.
    intros. inversion H. clear H. inversion Hp. clear Hp.
    econstructor.
    - eapply dexpr_binop; eassumption.
    - cbn. destruct_one_match;
        rewrite word.unsigned_eqb, ?word.unsigned_of_Z_1, ?word.unsigned_of_Z_0;
        reflexivity.
    - assumption.
  Qed.

  Ltac pose_env :=
    let env := fresh "env" in
    unshelve epose (env := _ : map.map string (list string * list string * cmd));
    [ eapply SortedListString.map
    | assert (env_ok: map.ok env) by apply SortedListString.ok; clearbody env ].

  Lemma WP_weaken_cmd: forall fs c t m l (post1 post2: _->_->_->Prop),
      WeakestPrecondition.cmd (call fs) c t m l post1 ->
      (forall t m l, post1 t m l -> post2 t m l) ->
      WeakestPrecondition.cmd (call fs) c t m l post2.
  Proof.
    pose_env. intros.
    eapply WeakestPreconditionProperties.Proper_cmd. 3: eassumption.
    1: eapply WeakestPreconditionProperties.Proper_call.
    cbv [RelationClasses.Reflexive Morphisms.pointwise_relation
         Morphisms.respectful Basics.impl].
    assumption.
  Qed.

  Inductive wp_cmd(fs: list (string * (list string * list string * cmd)))
            (c: cmd)(t: trace)(m: mem)(l: locals)(post: trace -> mem -> locals -> Prop):
    Prop := mk_wp_cmd(_: WeakestPrecondition.cmd (call fs) c t m l post).

  Lemma invert_wp_cmd: forall fs c t m l post,
      wp_cmd fs c t m l post -> WeakestPrecondition.cmd (call fs) c t m l post.
  Proof. intros. inversion H; assumption. Qed.

  Lemma weaken_wp_cmd: forall fs c t m l (post1 post2: _->_->_->Prop),
      wp_cmd fs c t m l post1 ->
      (forall t m l, post1 t m l -> post2 t m l) ->
      wp_cmd fs c t m l post2.
  Proof. intros. constructor. inversion H. eapply WP_weaken_cmd; eassumption. Qed.

  Lemma wp_skip: forall fs t m l (post: trace -> mem -> locals -> Prop),
      post t m l ->
      wp_cmd fs cmd.skip t m l post.
  Proof. intros. constructor. hnf. assumption. Qed.

  Lemma wp_seq: forall fs c1 c2 t m l post,
      wp_cmd fs c1 t m l (fun t' m' l' => wp_cmd fs c2 t' m' l' post) ->
      wp_cmd fs (cmd.seq c1 c2) t m l post.
  Proof.
    intros. constructor. cbn. inversion H. clear H.
    eapply WP_weaken_cmd. 1: eassumption. cbv beta. intros.
    inversion H. assumption.
  Qed.

  Fixpoint update_locals(keys: list string)(vals: list word)
    (l: locals)(post: locals -> Prop) :=
    match keys, vals with
    | cons k ks, cons v vs => update_locals ks vs (map.put l k v) post
    | nil, nil => post l
    | _, _ => False
    end.

  Lemma update_locals_spec: forall keys vals l post,
      update_locals keys vals l post <->
      (exists l', map.putmany_of_list_zip keys vals l = Some l' /\ post l').
  Proof.
    induction keys; intros; split; simpl; intros; destruct vals;
      fwd; try contradiction; try discriminate; eauto; try eapply IHkeys; eauto.
  Qed.

  Lemma update_one_local_eq: forall s v l (post: locals -> Prop),
      (forall x, x = v -> post (map.put l s x)) ->
      update_locals (cons s nil) (cons v nil) l post.
  Proof. unfold update_locals. intros. apply (H _ eq_refl). Qed.

  Lemma wp_set0: forall fs x e v t m l rest post,
      dexpr m l e v ->
      wp_cmd fs rest t m (map.put l x v) post ->
      wp_cmd fs (cmd.seq (cmd.set x e) rest) t m l post.
  Proof.
    intros. inversion H; clear H. inversion H0; clear H0. econstructor.
    cbn -[map.put]. eexists. split. 1: eassumption. unfold dlet.dlet. assumption.
  Qed.

  Lemma wp_store_uintptr0: forall fs ea ev a v R t m l rest (post: _->_->_->Prop),
      dexpr m l ea a ->
      dexpr m l ev v ->
      sep (uintptr ? a) R m ->
      (forall m', sep (uintptr v a) R m' -> wp_cmd fs rest t m' l post) ->
      wp_cmd fs (cmd.seq (cmd.store access_size.word ea ev) rest) t m l post.
  Proof.
    intros. inversion H; clear H. inversion H0; clear H0.
    constructor. hnf.
    eexists. split. 1: eassumption.
    unfold anyval in H1. eapply sep_ex1_l in H1. destruct H1 as (v_old & H1).
    eexists. split. 1: eassumption.
    unfold store.
    unfold uintptr, Scalars.scalar in *.
    eapply Scalars.store_of_sep. 1: eassumption.
    intros. eapply H2. assumption.
  Qed.

  Lemma wp_store_uint0: forall fs sz ea ev a v R t m l rest (post: _->_->_->Prop),
      dexpr m l ea a ->
      dexpr m l ev v ->
      0 <= word.unsigned v < 2 ^ access_size_to_nbits sz ->
      sep (uint (access_size_to_nbits sz) ? a) R m ->
      (forall m', sep (uint (access_size_to_nbits sz) (word.unsigned v) a) R m' ->
                  wp_cmd fs rest t m' l post) ->
      wp_cmd fs (cmd.seq (cmd.store sz ea ev) rest) t m l post.
  Proof.
    intros. inversion H; clear H. inversion H0; clear H0.
    constructor. hnf.
    eexists. split. 1: eassumption.
    unfold anyval in H2. eapply sep_ex1_l in H2. destruct H2 as (v_old & H2).
    eexists. split. 1: eassumption.
    unfold store.
    unfold uint in H2. eapply sep_assoc in H2. eapply sep_emp_l in H2.
    destruct H2 as (B & M).
    eapply Scalars.store_of_sep.
    - unfold Scalars.truncated_word, Scalars.truncated_scalar.
      destruct sz; cbn in *;
      rewrite <- (word.unsigned_of_Z_nowrap v_old) in M
        by (destruct width_cases as [W|W]; rewrite W in *; lia);
      try exact M.
      eqapply M. f_equal.
      destruct width_cases as [W|W]; rewrite W in *; reflexivity.
    - intros. eapply H3. unfold uint. eapply sep_assoc. eapply sep_emp_l.
      split. 1: assumption. unfold Scalars.truncated_word, Scalars.truncated_scalar in *.
      destruct sz; try assumption.
      eqapply H0. clear -BW word_ok.
      destruct width_cases as [W|W]; subst width; reflexivity.
  Qed.

  Definition merge_locals(c: bool):
    list (string * word) -> list (string * word) -> (list (string * word) -> Prop) -> Prop :=
    fix rec l1 l2 post :=
      match l1, l2 with
      | cons (x1, v1) t1, cons (x2, v2) t2 =>
          if String.eqb x1 x2
          then (forall v, v = (if c then v1 else v2) ->
                          rec t1 t2 (fun l => post (cons (x1, v) l)))
          else False
      | nil, nil => post nil
      | _, _ => False
      end.

  Lemma push_if_into_merge_locals: forall c kvs1 kvs2 post,
    merge_locals c kvs1 kvs2 post ->
    post (if c then kvs1 else kvs2).
  Proof.
    induction kvs1; intros; destruct kvs2; destruct c;
      repeat match goal with
        | a: _ * _ |- _ => destruct a
        end;
      simpl in *;
      repeat destruct_one_match_hyp;
      eauto; try contradiction;
      repeat match goal with
        | H: forall _, _ -> _ |- _ => specialize (H _ eq_refl)
        | IH: _, H: _ |- _ => specialize IH with (1 := H)
        end;
      cbv beta in *;
      assumption.
  Qed.

  Lemma merge_locals_same: forall c h t1 t2 post,
      merge_locals c t1 t2 (fun l => post (cons h l)) ->
      merge_locals c (cons h t1) (cons h t2) post.
  Proof.
    simpl. intros. destruct h as [x v]. rewrite String.eqb_refl. intros. subst.
    destruct c; assumption.
  Qed.

  Lemma wp_if0: forall fs c thn els rest b Q1 Q2 t m l post,
      dexpr m l c b ->
      (word.unsigned b <> 0 -> wp_cmd fs thn t m l Q1) ->
      (word.unsigned b =  0 -> wp_cmd fs els t m l Q2) ->
      (forall t' m' l', word.unsigned b <> 0 /\ Q1 t' m' l' \/
                        word.unsigned b =  0 /\ Q2 t' m' l' ->
                        wp_cmd fs rest t' m' l' post) ->
      wp_cmd fs (cmd.seq (cmd.cond c thn els) rest) t m l post.
  Proof.
    intros. inversion H; clear H. constructor. hnf.
    eexists. split. 1: eassumption.
    split; intro A;
      match goal with
      | H: _ -> _ |- _ => specialize (H A); inversion H; clear H
      end;
      (eapply WP_weaken_cmd; [eauto|intros; eauto using invert_wp_cmd]).
  Qed.

  Definition after_loop: list (string * (list string * list string * cmd)) ->
    cmd -> trace -> mem -> locals -> (trace -> mem -> locals -> Prop) -> Prop := wp_cmd.

  Lemma wp_set: forall fs x e v t m l rest post,
      dexpr1 m l e v (update_locals (cons x nil) (cons v nil) l
                        (fun l' => wp_cmd fs rest t m l' post)) ->
      wp_cmd fs (cmd.seq (cmd.set x e) rest) t m l post.
  Proof.
    unfold update_locals. intros. inversion H. eapply wp_set0; eassumption.
  Qed.

  Lemma wp_unset: forall fs x t m l rest post,
      wp_cmd fs rest t m (map.remove l x) post ->
      wp_cmd fs (cmd.seq (cmd.unset x) rest) t m l post.
  Proof. intros. constructor. inversion H. clear H. assumption. Qed.

  Definition unset_many: list string -> cmd :=
    List.fold_right (fun v c => (cmd.seq (cmd.unset v) c)) cmd.skip.

  Lemma wp_unset_many0: forall fs t m vars l (post: trace -> mem -> locals -> Prop),
      post t m (map.remove_many l vars) ->
      wp_cmd fs (unset_many vars) t m l post.
  Proof.
    induction vars; intros.
    - eapply wp_skip. assumption.
    - eapply wp_unset. eapply IHvars. rewrite map.remove_many_remove_commute. assumption.
  Qed.

  Lemma wp_unset_many: forall vars fs t m l rest post,
      wp_cmd fs rest t m (map.remove_many l vars) post ->
      wp_cmd fs (cmd.seq (unset_many vars) rest) t m l post.
  Proof. intros. eapply wp_seq. eapply wp_unset_many0. assumption. Qed.

  Lemma wp_unset_many_after_if: forall vars (b: bool) fs t m l l1 l2 li1 li2 rest post,
      l = (if b then l1 else l2) ->
      map.remove_many l1 vars = map.of_list li1 ->
      map.remove_many l2 vars = map.of_list li2 ->
      wp_cmd fs rest t m (map.of_list (if b then li1 else li2)) post ->
      wp_cmd fs (cmd.seq (unset_many vars) rest) t m l post.
  Proof.
    intros. subst. eapply wp_unset_many. destruct b; congruence.
  Qed.

  Lemma wp_store_uintptr: forall fs ea ev a v R t m l rest (post: _->_->_->Prop),
      dexpr1 m l ea a
        (dexpr1 m l ev v
           (sep (uintptr ? a) R m /\
            (forall m, sep (uintptr v a) R m -> wp_cmd fs rest t m l post))) ->
      wp_cmd fs (cmd.seq (cmd.store access_size.word ea ev) rest) t m l post.
  Proof.
    intros. inversion H; clear H. inversion Hp; clear Hp. destruct Hp0 as (H & C).
    eapply wp_store_uintptr0; eassumption.
  Qed.

  Lemma wp_store_uint: forall fs sz ea ev a v R t m l rest (post: _->_->_->Prop),
      dexpr1 m l ea a
        (dexpr1 m l ev v
           (0 <= word.unsigned v < 2 ^ access_size_to_nbits sz /\
            sep (uint (access_size_to_nbits sz) ? a) R m /\
            (forall m,
                sep (uint (access_size_to_nbits sz) (word.unsigned v) a) R m ->
                wp_cmd fs rest t m l post))) ->
      wp_cmd fs (cmd.seq (cmd.store sz ea ev) rest) t m l post.
  Proof.
    intros. inversion H; clear H. inversion Hp; clear Hp. destruct Hp0 as (B & H & C).
    eapply wp_store_uint0; eassumption.
  Qed.

  Definition then_branch_marker(P: Prop) := P.
  Definition else_branch_marker(P: Prop) := P.
  Definition after_if fs (b: bool) (Q1 Q2: trace -> mem -> locals -> Prop) rest post :=
    forall t m l, elet b (fun c =>
      if c then Q1 t m l else Q2 t m l) ->
      wp_cmd fs rest t m l post.
  Definition pop_scope_marker(P: Prop) := P.

  Definition cons_structure_exposing_reversing_equality[A: Type](lhs rhs: list A): Prop :=
    match List.rev' rhs with
    | cons h t => lhs = cons h t
    | nil => lhs = nil
    end.
  Remark explanation:
    exists l, cons_structure_exposing_reversing_equality
                l (List.app (cons (1+1) (cons (2+2) nil)) (cons (3+3) (cons (4+4) nil)))
              /\ l = l.
  Proof.
    eexists. split. 1: reflexivity.
    (* Note how the evar got instantiated to a list whose cons structure is fully exposed,
       but the elements were not simplified at all *)
    reflexivity.
  Succeed Qed. Abort.

  Lemma cons_structure_exposing_reversing_equality_spec[A: Type](lhs rhs: list A):
    cons_structure_exposing_reversing_equality lhs rhs <-> lhs = List.rev rhs.
  Proof.
    rewrite List.rev_alt.
    unfold cons_structure_exposing_reversing_equality. unfold List.rev'.
    destruct_one_match; reflexivity.
  Qed.

  Definition branch_post(initial_locals: locals)(new_vars: list string)
                        (Q: trace -> mem -> locals -> Prop)
                        (t: trace)(m: mem)(l: locals): Prop :=
    cons_structure_exposing_reversing_equality new_vars
      (list_diff String.eqb (map.keys l) (map.keys initial_locals)) /\
    (* ^- Note: the above equality is not needed to make the proof of wp_if_bool_dexpr work:
          We are free to unset whatever variables we want at the end of a branch.
          But picking new_vars such that the equality holds is what's consistent
          with C scoping rules: if a variable was declared in both branches, but
          not before the if, it's not available after the if. *)
    Q t m (map.remove_many l new_vars).

  Lemma wp_if_bool_dexpr fs c thn els rest t0 m0 l0 b new_thn_vars new_els_vars Q1 Q2 post:
      dexpr_bool3 m0 l0 c b
        (then_branch_marker (wp_cmd fs thn t0 m0 l0 (branch_post l0 new_thn_vars Q1)))
        (else_branch_marker (wp_cmd fs els t0 m0 l0 (branch_post l0 new_els_vars Q2)))
        (pop_scope_marker (after_if fs b Q1 Q2 rest post)) ->
      wp_cmd fs (cmd.seq (cmd.cond c (cmd.seq thn (unset_many new_thn_vars))
                                     (cmd.seq els (unset_many new_els_vars)))
                         rest) t0 m0 l0 post.
  Proof.
    intros. inversion H. subst. clear H.
    unfold then_branch_marker, else_branch_marker, pop_scope_marker,
      after_if, bool_expr_branches in *.
    destruct H2.
    destr (word.eqb v (word.of_Z 0)); (eapply wp_if0; [ eassumption | .. ]).
    all: try (intro C; rewrite ?word.unsigned_of_Z_nowrap in C
                  by (destruct width_cases as [W|W]; rewrite W in *; lia); try congruence).
    4: {
      exfalso. eapply E. eapply word.unsigned_inj.
      rewrite word.unsigned_of_Z_nowrap
          by (destruct width_cases as [W|W]; rewrite W in *; lia).
      exact C.
    }
    2,4: intros * [(? & ?) | (? & ?)].
    2-5: eapply H1; econstructor; try reflexivity; simpl; eassumption.
    all: eapply wp_seq.
    all: eapply weaken_wp_cmd.
    all: simpl in *.
    1,3: exact H.
    all: unfold branch_post.
    all: intros * [? ?]; subst.
    all: eapply wp_unset_many0.
    all: assumption.
  Qed.

  Lemma after_if_skip {Bt Bf b} {_: BoolSpec Bt Bf b} fs
    (PThen PElse Post: trace -> mem -> locals -> Prop):
    (Bt -> forall t m l, PThen t m l -> Post t m l) ->
    (Bf -> forall t m l, PElse t m l -> Post t m l) ->
    after_if fs b PThen PElse cmd.skip Post.
  Proof.
    intros.
    unfold after_if.
    intros ? ? ? [? ? ?]. subst x.
    eapply wp_skip.
    destruct H; eauto.
  Qed.

  Definition loop_body_marker(P: Prop) := P.

  Lemma wp_while {measure : Type} (v0 : measure) (e: expr) (c: cmd) t (m: mem) l fs rest
    (invariant: measure -> trace -> mem -> locals -> Prop) {lt}
    {post : trace -> mem -> locals -> Prop}
    (Hpre: invariant v0 t m l)
    (Hwf : well_founded lt)
    (Hbody : forall v t m l,
      invariant v t m l ->
      exists b, dexpr_bool3 m l e b
                  (loop_body_marker (wp_cmd fs c t m l
                      (fun t m l => exists v', invariant v' t m l /\ lt v' v)))
                  (pop_scope_marker (after_loop fs rest t m l post))
                  True)
    : wp_cmd fs (cmd.seq (cmd.while e c) rest) t m l post.
  Proof.
    econstructor. cbn. exists measure, lt, invariant.
    split. 1: assumption.
    split. 1: eauto.
    clear Hpre v0 t m l.
    intros v t m l Hinv.
    specialize (Hbody v t m l Hinv).
    fwd.
    inversion Hbody. subst. clear Hbody. inversion H. clear H.
    eexists. split. 1: eassumption.
    unfold bool_expr_branches in *. apply proj1 in H1. split.
    - intro NE. rewrite word.eqb_ne in H1. 1: eapply H1. intro C. subst v0.
      apply NE. apply word.unsigned_of_Z_0.
    - intro E. rewrite word.eqb_eq in H1. 1: eapply invert_wp_cmd; eapply H1.
      eapply word.unsigned_inj. rewrite word.unsigned_of_Z_0. exact E.
  Qed.

  Lemma wp_while_tailrec {measure: Type} {Ghost: Type} (v0: measure) (g0: Ghost)
    (e: expr) (c: cmd) t0 (m0: mem) l0 fs rest
    (pre post: measure -> Ghost -> trace -> mem -> locals -> Prop) {lt}
    {finalpost: trace -> mem -> locals -> Prop}
    (Hwf: well_founded lt)
    (* packaging generalized context at entry of loop determines pre: *)
    (Hpre: pre v0 g0 t0 m0 l0)
    (Hbody: forall v g t m l,
      pre v g t m l ->
      exists b, dexpr_bool3 m l e b
                  (* can't put loop body under context of b=true because we
                     first need to treat the b=false case (which determines post): *)
                  True
                  (* packaging generalized context at exit of loop (with final, smallest
                     measure) determines post: *)
                  (post v g t m l)
                  (loop_body_marker (bool_expr_branches b (wp_cmd fs c t m l
                      (fun t' m' l' => exists v' g',
                           pre v' g' t' m' l' /\
                           lt v' v /\
                           (forall t'' m'' l'', post v' g' t'' m'' l'' ->
                                                post v  g  t'' m'' l''))) True True)))
    (Hrest: forall t m l, post v0 g0 t m l -> wp_cmd fs rest t m l finalpost)
    : wp_cmd fs (cmd.seq (cmd.while e c) rest) t0 m0 l0 finalpost.
  Proof.
    eapply wp_seq.
    econstructor. cbn.
    pose_env.
    eapply tailrec_localsmap_1ghost.
    1: eapply Hwf.
    1: eapply Hpre.
    2: eapply Hrest.
    intros.
    specialize Hbody with (1 := H).
    destruct Hbody as (b & Hbody).
    inversion Hbody. subst c0 b Ptrue Pfalse Palways. clear Hbody.
    destruct H2 as (HDone & HAgain).
    inversion H0. unfold WeakestPrecondition.dexpr in *.
    eexists. split. 1: eassumption.
    unfold loop_body_marker in *.
    split; intro Hv; destruct_one_match_hyp.
    - apply proj1 in HAgain. inversion HAgain. eapply WP_weaken_cmd. 1: eassumption.
      cbv beta. intros *. exact id.
    - exfalso. apply Hv. apply word.unsigned_of_Z_0.
    - exfalso. apply E. eapply word.unsigned_inj. rewrite Hv. symmetry.
      apply word.unsigned_of_Z_0.
    - exact HDone.
  Qed.

  Definition dexprs(m: mem)(l: locals): list expr -> list word -> Prop :=
    List.Forall2 (dexpr m l).

  Inductive dexprs1(m: mem)(l: locals)(es: list expr)(vs: list word)(P: Prop): Prop :=
  | mk_dexprs1(Hde: dexprs m l es vs)(Hp: P).

  Lemma dexprs1_nil: forall m l (P: Prop), P -> dexprs1 m l nil nil P.
  Proof. intros. constructor. 1: constructor. assumption. Qed.

  Lemma dexprs1_cons: forall m l e es v vs P,
      dexpr1 m l e v (dexprs1 m l es vs P) ->
      dexprs1 m l (cons e es) (cons v vs) P.
  Proof.
    intros.
    inversion H; clear H. inversion Hp. clear Hp.
    constructor. 2: assumption. constructor. 1: assumption. assumption.
  Qed.

  Lemma cpsify_dexprs: forall m l es vs (post: list word -> Prop),
      dexprs m l es vs ->
      post vs ->
      list_map (WeakestPrecondition.expr m l) es post.
  Proof.
    induction es; intros.
    - cbn in *. inversion H. subst. assumption.
    - cbn in *. inversion H. subst. clear H.
      inversion H3. clear H3. unfold WeakestPrecondition.dexpr in H.
      eapply weaken_expr. 1: eassumption. intros. subst. eapply IHes; eassumption.
  Qed.

  Lemma wp_call0 fs t m l fname resnames es vs (post: trace -> mem -> locals -> Prop):
      dexprs m l es vs ->
      call fs fname t m vs (fun t' m' rets =>
        exists l', map.putmany_of_list_zip resnames rets l = Some l' /\ post t' m' l') ->
      wp_cmd fs (cmd.call resnames fname es) t m l post.
  Proof.
    intros.
    constructor. cbn. exists vs. split. 2: assumption.
    unfold WeakestPrecondition.dexprs. eapply cpsify_dexprs. 1: eassumption. reflexivity.
  Qed.

  Lemma wp_call: forall fs fname t m resnames arges argvs l rest
      (calleePre: Prop)
      (calleePost: trace -> mem -> list word -> Prop)
      (finalPost: trace -> mem -> locals -> Prop),
      (* definition-site format: *)
      (calleePre -> WeakestPrecondition.call fs fname t m argvs calleePost) ->
      (* use-site format: *)
      dexprs1 m l arges argvs (calleePre /\
         forall t' m' retvs, calleePost t' m' retvs ->
                             update_locals resnames retvs l (fun l' =>
                                 wp_cmd fs rest t' m' l' finalPost)) ->
      (* conclusion: *)
      wp_cmd fs (cmd.seq (cmd.call resnames fname arges) rest) t m l finalPost.
  Proof.
    intros. inversion H0. clear H0. destruct Hp as (Pre & Impl).
    setoid_rewrite update_locals_spec in Impl.
    specialize (H Pre). clear Pre.
    eapply wp_seq.
    eapply wp_call0. 1: eassumption.
    unshelve epose (env := _ : map.map string func).
    1: eapply SortedListString.map.
    assert (env_ok: map.ok env) by apply SortedListString.ok. clearbody env.
    eapply WeakestPreconditionProperties.Proper_call. 2: eassumption. exact Impl.
  Qed.

  Lemma cpsify_getmany_of_list: forall retnames retvs (post: list word -> Prop) l,
      map.getmany_of_list l retnames = Some retvs ->
      post retvs ->
      list_map (get l) retnames post.
  Proof.
    induction retnames; intros.
    - cbn in *. inversion H. subst. assumption.
    - cbn in *. fwd. unfold get. eexists. split. 1: eassumption.
      eapply IHretnames; eassumption.
  Qed.

  Lemma prove_func: forall fs argnames retnames body t m argvals l post,
      map.of_list_zip argnames argvals = Some l ->
      wp_cmd fs body t m l (fun t' m' l' => exists retvals,
                                map.getmany_of_list l' retnames = Some retvals /\
                                  post t' m' retvals) ->
      WeakestPrecondition.func (call fs) (argnames, retnames, body) t m argvals post.
  Proof.
    intros.
    unfold func.
    eexists. split. 1: eassumption.
    eapply invert_wp_cmd.
    eapply weaken_wp_cmd. 1: eassumption.
    cbv beta. intros. fwd.
    eapply cpsify_getmany_of_list; eassumption.
  Qed.

End WithParams.
