From Coq Require Import ZArith. Local Open Scope Z_scope.
From Coq Require Import Lia.
From Coq.Init Require Import Byte.
From Coq Require Import String.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require coqutil.Map.SortedListString. (* for function env, other maps are kept abstract *)
Require Import coqutil.Word.Interface coqutil.Word.Properties coqutil.Word.Bitwidth.
Require Import coqutil.Tactics.Tactics coqutil.Tactics.fwd.
Require Import coqutil.Datatypes.ListSet.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic.
Require bedrock2.Loops.
Require Import bedrock2.ZnWords.
Require Import bedrock2.SepLib.
Require Import bedrock2.enable_frame_trick.
Require Import LiveVerif.LiveExpr.

Module Import Semantics.
  Module exec.
    Section WithParams.
      Context {width: Z} {BW: Bitwidth width} {word: word.word width}
        {mem: map.map word byte} {locals: map.map String.string word}.
      Context {ext_spec: ExtSpec}.

      Lemma dowhile: forall e body cond t m l post,
          exec e body t m l (fun t' m' l' => exists v,
            eval_expr m' l' cond = Some v /\
            (word.unsigned v <> 0 -> exec e (cmd.dowhile body cond) t' m' l' post) /\
            (word.unsigned v =  0 -> post t' m' l')) ->
          exec e (cmd.dowhile body cond) t m l post.
      Proof.
        unfold cmd.dowhile. intros. eapply exec.seq. 1: eassumption.
        cbv beta. clear H. intros. fwd. destr (Z.eqb (word.unsigned v) 0).
        - specialize (Hp2 E).
          eapply exec.while_false; eassumption.
        - specialize (Hp1 E). inversion Hp1. subst.
          eapply exec.while_true; eassumption.
      Qed.
    End WithParams.
  End exec.
End Semantics.

Notation wp_cmd := Semantics.exec (only parsing).

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

  Lemma invert_dexpr: forall m l e w, dexpr m l e w -> WeakestPrecondition.dexpr m l e w.
  Proof. intros. inversion H. assumption. Qed.

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

  (* Note: (fun _ => True) instead of a frame to make it really clear that
     no one cares about the value of this frame, so heapletwise will not waste
     any effort on collecting all the remaining facts *)
  Lemma dexpr1_load_uintptr: forall m l e addr v (P: Prop),
      dexpr1 m l e addr (sep (uintptr v addr) (fun _ => True) m /\ P) ->
      dexpr1 m l (expr.load access_size.word e) v P.
  Proof.
    intros. inversion H; clear H. fwd. constructor. 2: assumption.
    eapply dexpr_load_uintptr; eassumption.
  Qed.

  Lemma dexpr1_load_uint: forall m l e addr sz v (P: Prop),
      dexpr1 m l e addr
        (sep (uint (access_size_to_nbits sz) v addr) (fun _ => True) m /\ P) ->
      dexpr1 m l (expr.load sz e) (word.of_Z v) P.
  Proof.
    intros. inversion H; clear H. fwd. constructor. 2: assumption.
    eapply dexpr_load_uint; eassumption.
  Qed.

  Lemma dexpr1_deref_uintptr: forall m l e addr v (P: Prop),
      dexpr1 m l e addr True ->
      sep (uintptr v addr) (fun _ => True) m ->
      P ->
      dexpr1 m l (deref access_size.word e) v P.
  Proof.
    intros. inversion H; clear H. fwd. constructor. 2: assumption.
    eapply dexpr_load_uintptr; eassumption.
  Qed.

  Lemma dexpr1_deref_uint: forall m l e addr sz v (P: Prop),
      dexpr1 m l e addr True ->
      sep (uint (access_size_to_nbits sz) v addr) (fun _ => True) m ->
      P ->
      dexpr1 m l (deref sz e) (word.of_Z v) P.
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

  Lemma wp_skip: forall fs t m l (post: trace -> mem -> locals -> Prop),
      post t m l ->
      wp_cmd fs cmd.skip t m l post.
  Proof. intros. constructor. hnf. assumption. Qed.

  Lemma wp_seq: forall fs c1 c2 t m l post,
      wp_cmd fs c1 t m l (fun t' m' l' => wp_cmd fs c2 t' m' l' post) ->
      wp_cmd fs (cmd.seq c1 c2) t m l post.
  Proof. intros. econstructor; eauto. Qed.

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

  Lemma wp_set00: forall fs x e v t m l (post: trace -> mem -> locals -> Prop),
      dexpr m l e v ->
      post t m (map.put l x v) ->
      wp_cmd fs (cmd.set x e) t m l post.
  Proof.
    intros. inversion H; clear H.
    eapply WeakestPreconditionProperties.expr_sound in H1. fwd.
    econstructor; eassumption.
  Qed.

  Lemma wp_set0: forall fs x e v t m l rest post,
      dexpr m l e v ->
      wp_cmd fs rest t m (map.put l x v) post ->
      wp_cmd fs (cmd.seq (cmd.set x e) rest) t m l post.
  Proof.
    intros. eapply wp_seq. eapply wp_set00; eassumption.
  Qed.

  Lemma wp_store_uintptr0: forall fs ea ev a v R t m l rest (post: _->_->_->Prop),
      dexpr m l ea a ->
      dexpr m l ev v ->
      sep (uintptr ? a) R m ->
      (forall m', sep (uintptr v a) R m' -> wp_cmd fs rest t m' l post) ->
      wp_cmd fs (cmd.seq (cmd.store access_size.word ea ev) rest) t m l post.
  Proof.
    intros. inversion H; clear H. inversion H0; clear H0.
    eapply WeakestPreconditionProperties.expr_sound in H3. fwd.
    eapply WeakestPreconditionProperties.expr_sound in H. fwd.
    eapply exec.seq with (mid := fun t' m' l' => t' = t /\ l' = l /\ _).
    2: {
      intros * (? & ? & HM). subst. eapply H2. exact HM.
    }
    unfold anyval in H1. eapply sep_ex1_l in H1. destruct H1 as (v_old & H1).
    unfold uintptr, Scalars.scalar in *.
    eapply Scalars.store_of_sep in H1.
    { destruct H1 as (m' & ? & HP).
      econstructor; try eassumption.
      ssplit. 1,2: reflexivity.
      exact HP. }
    intros ?. exact id.
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
    eapply WeakestPreconditionProperties.expr_sound in H4. fwd.
    eapply WeakestPreconditionProperties.expr_sound in H. fwd.
    eapply exec.seq with (mid := fun t' m' l' => t' = t /\ l' = l /\ _).
    2: {
      intros * (? & ? & HM). subst. eapply H3. exact HM.
    }
    unfold anyval in H2. eapply sep_ex1_l in H2. destruct H2 as (v_old & H2).
    unfold uint in H2. eapply sep_assoc in H2. eapply sep_emp_l in H2.
    destruct H2 as (B & M).
    pose proof Scalars.store_of_sep as P.
    unfold Scalars.truncated_word, Scalars.truncated_scalar in P.
    specialize (P sz v0 (word.of_Z v_old)).
    replace (Z.to_nat (nbits_to_nbytes (access_size_to_nbits sz))) with
      (bytes_per (width := width) sz) in M.
    2: {
      destruct sz; cbn; try reflexivity.
      destruct width_cases as [W | W]; rewrite W; reflexivity.
    }
    rewrite word.unsigned_of_Z_nowrap in P.
    2: {
      destruct width_cases as [W|W]; rewrite W in *; destruct sz; lia.
    }
    eapply P in M.
    { destruct M as (m' & ? & HP).
      econstructor; try eassumption.
      ssplit. 1,2: reflexivity.
      exact HP. }
    { clear P.
      intros. unfold uint. eapply sep_assoc. eapply sep_emp_l.
      split. 1: assumption. unfold Scalars.truncated_word, Scalars.truncated_scalar in *.
      destruct sz; try assumption.
      eqapply H. clear -BW word_ok.
      destruct width_cases as [W|W]; subst width; reflexivity. }
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

  Lemma wp_push_if_into_merge_locals: forall fs t m rest c kvs1 kvs2 post,
    merge_locals c kvs1 kvs2 (fun kvs => wp_cmd fs rest t m (map.of_list kvs) post) ->
    wp_cmd fs rest t m (if c then map.of_list kvs1 else map.of_list kvs2) post.
  Proof.
    intros. eapply push_if_into_merge_locals in H. destruct c; exact H.
  Qed.

  Lemma merge_locals_same: forall c h t1 t2 post,
      merge_locals c t1 t2 (fun l => post (cons h l)) ->
      merge_locals c (cons h t1) (cons h t2) post.
  Proof.
    simpl. intros. destruct h as [x v]. rewrite String.eqb_refl. intros. subst.
    destruct c; assumption.
  Qed.

  Lemma wp_if00: forall fs c thn els b t m l post,
      dexpr m l c b ->
      (word.unsigned b <> 0 -> wp_cmd fs thn t m l post) ->
      (word.unsigned b =  0 -> wp_cmd fs els t m l post) ->
      wp_cmd fs (cmd.cond c thn els) t m l post.
  Proof.
    intros. inversion H; clear H.
    eapply WeakestPreconditionProperties.expr_sound in H2. fwd.
    destr (word.unsigned v =? 0).
    - eapply exec.if_false; eauto.
    - eapply exec.if_true; eauto.
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
    intros. eapply wp_seq. eapply wp_if00. 1: eassumption.
    all: intro A; match goal with
      | H: _ -> _ |- _ => specialize (H A)
      end.
    all: eauto using exec.weaken.
  Qed.

  Definition after_loop: Semantics.env ->
    cmd -> trace -> mem -> locals -> (trace -> mem -> locals -> Prop) -> Prop := wp_cmd.

  Lemma wp_set: forall fs x e v t m l rest post,
      dexpr1 m l e v (update_locals (cons x nil) (cons v nil) l
                        (fun l' => wp_cmd fs rest t m l' post)) ->
      wp_cmd fs (cmd.seq (cmd.set x e) rest) t m l post.
  Proof.
    unfold update_locals. intros. inversion H. eapply wp_set0; eassumption.
  Qed.

  Lemma wp_unset00: forall fs x t m l (post: trace -> mem -> locals -> Prop),
      post t m (map.remove l x) ->
      wp_cmd fs (cmd.unset x) t m l post.
  Proof. intros. constructor. assumption. Qed.

  Lemma wp_unset: forall fs x t m l rest post,
      wp_cmd fs rest t m (map.remove l x) post ->
      wp_cmd fs (cmd.seq (cmd.unset x) rest) t m l post.
  Proof. intros. eapply wp_seq. eapply wp_unset00. assumption. Qed.

  (* when setting a new variable, we will first use this lemma to also unset it at the end of
     the block, so that proper scoping is maintained *)
  Lemma wp_unset_at_end: forall fs x t m l rest post,
      wp_cmd fs rest t m l (fun t' m' l' => post t' m' (map.remove l' x)) ->
      wp_cmd fs (cmd.seq rest (cmd.unset x)) t m l post.
  Proof.
    intros. eapply wp_seq. eapply exec.weaken. 1: eassumption.
    cbv beta. intros. eapply wp_unset00. assumption.
  Qed.

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

  Lemma wp_store_uintptr: forall fs ea ev a v R t m l rest (post: _->_->_->Prop),
      dexpr1 m l ea a
        (dexpr1 m l ev v
           (sep (uintptr ? a) R m /\ enable_frame_trick
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
            sep (uint (access_size_to_nbits sz) ? a) R m /\ enable_frame_trick
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

  Definition package_context_marker(Q: trace -> mem -> locals -> Prop)
    (t: trace)(m: mem)(l: locals): Prop := Q t m l.

  Lemma wp_if_bool_dexpr fs c thn els rest t0 m0 l0 b Q1 Q2 post:
      dexpr_bool3 m0 l0 c b
        (then_branch_marker (wp_cmd fs thn t0 m0 l0 (package_context_marker Q1)))
        (else_branch_marker (wp_cmd fs els t0 m0 l0 (package_context_marker Q2)))
        (pop_scope_marker (after_if fs b Q1 Q2 rest post)) ->
      wp_cmd fs (cmd.seq (cmd.cond c thn els) rest) t0 m0 l0 post.
  Proof.
    intros. inversion H. subst. clear H.
    unfold then_branch_marker, else_branch_marker, pop_scope_marker,
      after_if, bool_expr_branches, package_context_marker in *.
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
    all: simpl in *.
    all: exact H.
  Qed.

  (* TODO use or remove, but make sure it doesn't prevent expect_1expr_return from being
     recognized *)
  Definition needs_to_be_closed_by_single_rbrace(P: Prop) := P.

  Definition needs_opening_else_and_lbrace(P: Prop) := P.

  Lemma wp_if_bool_dexpr_split fs c thn els t0 m0 l0 b post:
      dexpr_bool3 m0 l0 c b
        (then_branch_marker (wp_cmd fs thn t0 m0 l0 post))
        (else_branch_marker (needs_opening_else_and_lbrace (wp_cmd fs els t0 m0 l0 post)))
        (* Contrary to most other lemmas, this lemma doesn't have a (cmd.seq _ rest)
           and a corresponding subgoal for rest, in which the closing brace for the
           current block can be consumed. So we add a dummy goal to consume that
           closing brace: *)
        (pop_scope_marker (wp_cmd fs cmd.skip t0 m0 l0 (fun _ _ _ => True))) ->
      wp_cmd fs (cmd.cond c thn els) t0 m0 l0 post.
  Proof.
    intros. inversion H. subst. clear H.
    unfold then_branch_marker, else_branch_marker, pop_scope_marker,
      after_if, bool_expr_branches,
      needs_to_be_closed_by_single_rbrace, needs_opening_else_and_lbrace in *.
    apply proj1 in H2.
    destr (word.eqb v (word.of_Z 0)); simpl in H2; (eapply wp_if00; [ eassumption | .. ]).
    all: try (intro C; rewrite ?word.unsigned_of_Z_nowrap in C
                  by (destruct width_cases as [W|W]; rewrite W in *; lia); try congruence).
    exfalso. eapply E. eapply word.unsigned_inj.
    rewrite word.unsigned_of_Z_nowrap
      by (destruct width_cases as [W|W]; rewrite W in *; lia).
    exact C.
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

  Lemma wp_while0: forall fs e c t m l (post: _ -> _ -> _ -> Prop) {measure: Type}
                          (lt: measure -> measure -> Prop)
                          (inv: measure -> trace -> mem -> locals -> Prop)
                          (v0: measure),
      well_founded lt ->
      inv v0 t m l ->
      (forall v t m l,
          inv v t m l ->
          exists b, dexpr m l e b /\
                    (word.unsigned b <> 0%Z -> wp_cmd fs c t m l (fun t' m' l' =>
                       exists v', inv v' t' m' l' /\ lt v' v)) /\
                    (word.unsigned b = 0%Z -> post t m l)) ->
     wp_cmd fs (cmd.while e c) t m l post.
  Proof.
    intros * Hwf HInit Hbody.
    revert t m l HInit. pattern v0. revert v0.
    eapply (well_founded_ind Hwf). intros.
    specialize Hbody with (1 := HInit). destruct Hbody as (b & Hb & Ht & Hf).
    eapply invert_dexpr in Hb.
    eapply WeakestPreconditionProperties.expr_sound in Hb.
    destruct Hb as (b' & Hb & ?). subst b'.
    destr.destr (Z.eqb (word.unsigned b) 0).
    - specialize Hf with (1 := E). eapply exec.while_false; eassumption.
    - specialize Ht with (1 := E). eapply exec.while_true; eauto.
      cbv beta. intros * (v' & HInv & HLt). eauto.
  Qed.

  Lemma wp_dowhile0: forall fs e c t m l (post: _ -> _ -> _ -> Prop) {measure: Type}
                          (lt: measure -> measure -> Prop)
                          (inv: measure -> trace -> mem -> locals -> Prop)
                          (v0: measure),
      well_founded lt ->
      inv v0 t m l ->
      (forall v t m l,
          inv v t m l ->
          wp_cmd fs c t m l (fun t' m' l' =>
            exists b, dexpr m' l' e b /\
                      (word.unsigned b <> 0 -> exists v', inv v' t' m' l' /\ lt v' v) /\
                      (word.unsigned b = 0 -> post t' m' l'))) ->
     wp_cmd fs (cmd.dowhile c e) t m l post.
  Proof.
    intros * Hwf HInit Hbody.
    revert t m l HInit. pattern v0. revert v0.
    eapply (well_founded_ind Hwf). intros.
    specialize Hbody with (1 := HInit).
    eapply exec.dowhile.
    eapply exec.weaken. 1: exact Hbody.
    cbv beta. clear Hbody HInit. intros. fwd.
    eapply invert_dexpr in H0p0.
    eapply WeakestPreconditionProperties.expr_sound in H0p0. fwd.
    eexists. ssplit. 1: eassumption.
    - intro E. specialize (H0p1 E). fwd. eauto.
    - intro E. specialize (H0p2 E). assumption.
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
    eapply wp_seq. eapply wp_while0. 1,2: eassumption.
    intros * Hinv. specialize Hbody with (1 := Hinv).
    destruct Hbody as (b & Hbody).
    inversion Hbody. subst. clear Hbody.
    eexists. split. 1: eassumption.
    unfold bool_expr_branches in *. apply proj1 in H1. split.
    - intro NE.
      rewrite word.eqb_ne in H1. 1: eapply H1. intro C. subst v1.
      apply NE. apply word.unsigned_of_Z_0.
    - intro E. rewrite word.eqb_eq in H1. 1: eapply H1.
      eapply word.unsigned_inj. rewrite word.unsigned_of_Z_0. exact E.
  Qed.

  Lemma wp_dowhile {measure : Type} (v0 : measure) (e: expr) (c: cmd) t (m: mem) l fs rest
    (invariant: measure -> trace -> mem -> locals -> Prop) {lt}
    {post : trace -> mem -> locals -> Prop}
    (Hpre: invariant v0 t m l)
    (Hwf : well_founded lt)
    (Hbody : forall v t m l,
      invariant v t m l ->
      loop_body_marker (wp_cmd fs c t m l (fun t' m' l' =>
        exists b, dexpr_bool3 m' l' e b
                    (exists v', invariant v' t' m' l' /\ lt v' v)
                    (pop_scope_marker (after_loop fs rest t' m' l' post))
                    True)))
    : wp_cmd fs (cmd.seq (cmd.dowhile c e) rest) t m l post.
  Proof.
    eapply wp_seq. eapply wp_dowhile0. 1,2: eassumption.
    intros * Hinv. specialize Hbody with (1 := Hinv).
    eapply exec.weaken. 1: exact Hbody.
    clear Hinv Hbody t t0 m0 l0 Hpre.
    cbv beta. intros ? ? ? [b H]. inversion H. subst. clear H.
    eexists. split. 1: eassumption.
    unfold bool_expr_branches in *. apply proj1 in H2. split.
    - intro NE.
      rewrite word.eqb_ne in H2. 1: eapply H2. intro C. subst v1.
      apply NE. apply word.unsigned_of_Z_0.
    - intro E. rewrite word.eqb_eq in H2. 1: eapply H2.
      eapply word.unsigned_inj. rewrite word.unsigned_of_Z_0. exact E.
  Qed.

  (* alias of "exists" to mark ghost vars of tailrecursive loop body calls that need
     to be provided (at least partially) manually *)
  Definition provide_new_ghosts{Ghosts: Type}: (Ghosts -> Prop) -> Prop := @ex Ghosts.

  (* marker for tactics to detect that before proving this implication, we can
     clear all other state
     (TODO: could also be used for Hbody, Hrest hyps of while lemmas, and for remainder
     in call lemmas) *)
  Definition state_implication(P1 P2: trace -> mem -> locals -> Prop): Prop :=
    forall t m l, P1 t m l -> P2 t m l.

  Lemma wp_while_tailrec {measure: Type} {Ghost: Type} (v0: measure) (g0: Ghost)
    (e: expr) (c: cmd) t0 (m0: mem) l0 fs rest
    (pre post: Ghost * measure * trace * mem * locals -> Prop) {lt}
    {finalpost: trace -> mem -> locals -> Prop}
    (Hwf: well_founded lt)
    (* packaging generalized context at entry of loop determines pre: *)
    (Hpre: pre (g0, v0, t0, m0, l0))
    (Hbody: forall v g t m l,
      pre (g, v, t, m, l) ->
      exists b, dexpr_bool3 m l e b
                  (* can't put loop body under context of b=true because we
                     first need to treat the b=false case (which determines post): *)
                  True
                  (* packaging generalized context at exit of loop (with final, smallest
                     measure) determines post: *)
                  (post (g, v, t, m, l))
                  (loop_body_marker (bool_expr_branches b (wp_cmd fs c t m l
                      (fun t' m' l' => exists v', provide_new_ghosts (fun g' =>
                         pre (g', v', t', m', l') /\
                         lt v' v /\
                         state_implication (fun t'' m'' l'' => post (g', v', t'', m'', l''))
                                           (fun t'' m'' l'' => post (g , v , t'', m'', l''))
                      ))) True True)))
    (Hrest: forall t m l, post (g0, v0, t, m, l) -> wp_cmd fs rest t m l finalpost)
    : wp_cmd fs (cmd.seq (cmd.while e c) rest) t0 m0 l0 finalpost.
  Proof.
    unfold provide_new_ghosts in *.
    eapply wp_seq. eapply WeakestPreconditionProperties.sound_cmd.
    eapply Loops.tailrec_localsmap_1ghost with
      (P := fun v g t m l => pre (g, v, t, m, l))
      (Q := fun v g t m l => post (g, v, t, m, l)).
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
    - apply proj1 in HAgain. eapply WeakestPreconditionProperties.complete_cmd. assumption.
    - exfalso. apply Hv. apply word.unsigned_of_Z_0.
    - exfalso. apply E. eapply word.unsigned_inj. rewrite Hv. symmetry.
      apply word.unsigned_of_Z_0.
    - exact HDone.
  Qed.

  Lemma wp_while_tailrec_use_functionpost{measure: Type}{Ghost: Type}(v0: measure)(g0: Ghost)
    (e: expr) (c: cmd) t0 (m0: mem) l0 fs rest
    (pre: Ghost * measure * trace * mem * locals -> Prop) {lt}
    {functionpost: Ghost -> measure -> trace -> mem -> locals -> Prop}
    (Hwf: well_founded lt)
    (* packaging generalized context at entry of loop determines pre: *)
    (Hpre: pre (g0, v0, t0, m0, l0))
    (Hbody: forall v g t m l,
      pre (g, v, t, m, l) ->
      exists b, dexpr_bool3 m l e b
                  (loop_body_marker (wp_cmd fs c t m l
                      (fun t' m' l' => exists v', provide_new_ghosts (fun g' =>
                           pre (g', v', t', m', l') /\
                           lt v' v /\
                           state_implication (functionpost g' v')
                                             (functionpost g  v )))))
                  (pop_scope_marker (after_loop fs rest t m l (functionpost g v)))
                  True)
    : wp_cmd fs (cmd.seq (cmd.while e c) rest) t0 m0 l0 (functionpost g0 v0).
  Proof.
    unfold provide_new_ghosts in *.
    eapply wp_seq.
    eapply wp_while0 with (inv := fun v t m l =>
      exists g, pre (g, v, t, m, l) /\
                (forall t' m' l', functionpost g v t' m' l' -> functionpost g0 v0 t' m' l')).
    1: exact Hwf.
    { eexists. split. 1: eassumption. intros *. exact id. }
    intros * (g & HPre & HPostImpl).
    specialize Hbody with (1 := HPre).
    destruct Hbody as (b & Hbody).
    inversion Hbody. subst. clear Hbody.
    unfold bool_expr_branches, loop_body_marker in *. apply proj1 in H1.
    eexists. split. 1: eassumption. split.
    - intro NE.
      rewrite word.eqb_ne in H1.
      { simpl in H1. eapply exec.weaken. 1: eapply H1.
        cbv beta. clear -HPostImpl. intros. fwd. eauto 10. }
      intro C. subst v1.
      apply NE. apply word.unsigned_of_Z_0.
    - intro E. eapply exec.weaken. 2: eapply HPostImpl.
      rewrite word.eqb_eq in H1. 1: eapply H1.
      eapply word.unsigned_inj. rewrite word.unsigned_of_Z_0. exact E.
  Qed.

  Lemma wp_dowhile_tailrec_use_functionpost{measure: Type}{Ghost: Type}(v0: measure)(g0: Ghost)
    (e: expr) (c: cmd) t0 (m0: mem) l0 fs rest
    (pre: Ghost * measure * trace * mem * locals -> Prop) {lt}
    {functionpost: Ghost -> measure -> trace -> mem -> locals -> Prop}
    (Hwf: well_founded lt)
    (* packaging generalized context at entry of loop determines pre: *)
    (Hpre: pre (g0, v0, t0, m0, l0))
    (Hbody: forall v g t m l,
      pre (g, v, t, m, l) ->
      loop_body_marker (wp_cmd fs c t m l (fun t' m' l' =>
        exists b, dexpr_bool3 m' l' e b
                    (exists v', provide_new_ghosts (fun g' =>
                        pre (g', v', t', m', l') /\
                        lt v' v /\
                        state_implication (functionpost g' v')
                                          (functionpost g  v )))
                    (pop_scope_marker (after_loop fs rest t' m' l' (functionpost g v)))
                    True)))
    : wp_cmd fs (cmd.seq (cmd.dowhile c e) rest) t0 m0 l0 (functionpost g0 v0).
  Proof.
    unfold provide_new_ghosts in *.
    eapply wp_seq.
    eapply wp_dowhile0 with (inv := fun v t m l =>
      exists g, pre (g, v, t, m, l) /\
          (forall t' m' l', functionpost g v t' m' l' -> functionpost g0 v0 t' m' l')).
    1: exact Hwf.
    { eexists. split. 1: eassumption. intros *. exact id. }
    intros * (g & HPre & HPostImpl).
    specialize Hbody with (1 := HPre).
    unfold loop_body_marker in *.
    eapply exec.weaken. 1: eassumption.
    clear Hbody. cbv beta. intros. fwd. inversion H. subst. clear H.
    unfold bool_expr_branches in *. apply proj1 in H2.
    eexists. split. 1: eassumption. split.
    - intro NE.
      rewrite word.eqb_ne in H2.
      { simpl in H2. fwd. eauto 10. }
      intro C. subst v1.
      apply NE. apply word.unsigned_of_Z_0.
    - intro E.
      rewrite word.eqb_eq in H2.
      { eapply exec.weaken. 1: exact H2. exact HPostImpl. }
      eapply word.unsigned_inj. rewrite word.unsigned_of_Z_0. exact E.
  Qed.

  Definition with_again_flag{T: Type}(R: T -> T -> Prop): bool * T -> bool * T -> Prop :=
    fun '(again1, x1) '(again2, x2) =>
      if again2 then
        if again1 then R x1 x2 else True
      else
        if again1 then False else R x1 x2.

  Lemma well_founded_with_again_flag T (R: T -> T -> Prop) (Hwf: well_founded R):
    well_founded (with_again_flag R).
  Proof.
    unfold well_founded.
    assert (false_Acc: forall x2, Acc (with_again_flag R) (false, x2)). {
      intros x2. remember false as b2. revert b2 Heqb2. pattern x2. revert x2.
      eapply well_founded_ind. 1: exact Hwf.
      intros x2 IH b2 Eb2. subst b2. eapply Acc_intro. intros (b1 & x1) HR.
      destruct b1; simpl in HR.
      1: contradiction.
      eapply IH. 1: exact HR. reflexivity.
    }
    intros (b2 & x2). destruct b2. 2: eapply false_Acc.
    remember true as b2. revert b2 Heqb2. pattern x2. revert x2.
    eapply well_founded_ind. 1: exact Hwf.
    intros x2 IH b2 Eb2. subst b2. eapply Acc_intro. intros (b1 & x1) HR.
    destruct b1; simpl in HR.
    + eapply IH. 1: exact HR. reflexivity.
    + eapply false_Acc.
  Qed.

  (* Often, after the last iteration, pre doesn't hold any more.
     For such cases, this lemma allows proving post instead. *)
  Lemma wp_while_tailrec_skip_last_pre {measure: Type} {Ghost: Type}
    (v0: measure) (g0: Ghost)
    (e: expr) (c: cmd) t0 (m0: mem) l0 fs rest
    (pre post: Ghost * measure * trace * mem * locals -> Prop) {lt}
    {finalpost: trace -> mem -> locals -> Prop}
    (Hwf: well_founded lt)
    (* packaging generalized context at entry of loop determines pre: *)
    (Hpre: pre (g0, v0, t0, m0, l0))
    (Hbody: forall v g t m l,
      pre (g, v, t, m, l) ->
      exists b, dexpr_bool3 m l e b
                  (* can't put loop body under context of b=true because we
                     first need to treat the b=false case (which determines post): *)
                  True
                  (* packaging generalized context at exit of loop (with final, smallest
                     measure) determines post: *)
                  (post (g, v, t, m, l))
                  (loop_body_marker (bool_expr_branches b (wp_cmd fs c t m l
                      (fun t' m' l' => exists b',
                         (* evaluating condition e again!! *)
                         dexpr_bool3 m' l' e b'
                           (exists v', provide_new_ghosts (fun g' =>
                               pre (g', v', t', m', l') /\
                               lt v' v /\
                               state_implication
                                 (fun t'' m'' l'' => post (g', v', t'', m'', l''))
                                 (fun t'' m'' l'' => post (g , v , t'', m'', l''))))
                           (post (g, v, t', m', l'))
                           True)) True True)))
    (Hrest: forall t m l, post (g0, v0, t, m, l) -> wp_cmd fs rest t m l finalpost)
    : wp_cmd fs (cmd.seq (cmd.while e c) rest) t0 m0 l0 finalpost.
  Proof.
    unfold provide_new_ghosts in *.
    pose proof Hbody as Hinit.
    specialize Hinit with (1 := Hpre). destruct Hinit as (b & Hinit).
    inversion Hinit. subst. clear Hinit. unfold bool_expr_branches in H1.
    apply proj1 in H1.
    eapply wp_while_tailrec with
      (v0 := (negb (word.eqb v (word.of_Z 0)), v0))
      (pre := fun '(g, (again, v), t, m, l) =>
                (exists w, dexpr m l e w /\ again = negb (word.eqb w (word.of_Z 0))) /\
                if again then  pre (g, v, t, m, l) else post (g, v, t, m, l))
      (post := fun '(g, (again, v), t, m, l) => post (g, v, t, m, l)).
    { eapply well_founded_with_again_flag. eapply Hwf. }
    { split.
      { eexists. split. 1: eassumption. reflexivity. }
      destr (word.eqb v (word.of_Z 0)); simpl in *.
      1: eassumption. assumption. }
    { intros. fwd. destr (word.eqb w (word.of_Z 0)); simpl in *.
      { exists false. econstructor. 1: eassumption.
        { rewrite word.eqb_eq; reflexivity. }
        { unfold bool_expr_branches, loop_body_marker. auto. } }
      { specialize Hbody with (1 := H0p1). destruct Hbody as (b & Hbody).
        inversion Hbody. subst c0. exists b. clear Hbody. subst.
        econstructor. 1: eassumption. 1: reflexivity.
        unfold bool_expr_branches in *.
        destr (word.eqb v1 (word.of_Z 0)); simpl in *.
        1: assumption.
        split. 1: constructor. apply proj2 in H3. unfold loop_body_marker in *.
        apply proj1 in H3. split. 2: constructor.
        eapply Semantics.exec.weaken. 1: eassumption.
        cbv beta. clear H3. intros. fwd. inversion H2. subst. clear H2.
        unfold bool_expr_branches in *. apply proj1 in H5.
        destr (word.eqb v2 (word.of_Z 0)); simpl in *.
        { eexists (false, m1(* old, big measure! *)), _.
          ssplit.
          { eexists. split. 1: eassumption. rewrite word.eqb_eq; reflexivity. }
          { eassumption. }
          { exact I. }
          intros ? ? ?. exact id. }
        { fwd.
          eexists (true, v'(* new, smaller measure *)), _.
          ssplit.
          { eexists. split. 1: eassumption. rewrite word.eqb_ne by assumption.
            reflexivity. }
          { eassumption. }
          { simpl. assumption. }
          assumption. } } }
      { assumption. }
  Qed.

  (* Note: cannot have any code after the loop because it would have to be
     stepped through twice! *)
  Lemma wp_while_tailrec_skip_last_pre_use_functionpost{measure: Type}{Ghost: Type}
    (v0: measure)(g0: Ghost)
    (e: expr) (c: cmd) t0 (m0: mem) l0 fs
    (pre: Ghost * measure * trace * mem * locals -> Prop) {lt}
    {functionpost: Ghost -> measure -> trace -> mem -> locals -> Prop}
    (Hwf: well_founded lt)
    (* packaging generalized context at entry of loop determines pre: *)
    (Hpre: pre (g0, v0, t0, m0, l0))
    (Hbody: forall v g t m l,
      pre (g, v, t, m, l) ->
      exists b, dexpr_bool3 m l e b
                  (loop_body_marker (wp_cmd fs c t m l
                      (fun t' m' l' => exists v',
                           (* executing condition e again! *)
                           exists b', dexpr_bool3 m' l' e b'
                              (provide_new_ghosts (fun g' =>
                                 pre (g', v', t', m', l') /\
                                 lt v' v /\
                                   state_implication (functionpost g' v')
                                     (functionpost g  v )))
                              (functionpost g v t' m' l')
                              True)))
                  (functionpost g v t m l)
                  True)
    : wp_cmd fs (cmd.while e c) t0 m0 l0 (functionpost g0 v0).
  Proof.
    enough (exec fs (cmd.seq (cmd.while e c) cmd.skip) t0 m0 l0 (functionpost g0 v0)). {
      inversion H. subst. eapply exec.weaken. 1: eassumption.
      intros. specialize (H7 _ _ _ H0). inversion H7. subst. assumption.
    }
    eapply wp_while_tailrec_skip_last_pre with
      (post := fun '(g, v, t, m, l) => functionpost g v t m l).
    1: exact Hwf.
    1: exact Hpre.
    2: { clear. intros. eapply exec.skip. assumption. }
    intros * HPre.
    specialize Hbody with (1 := HPre).
    destruct Hbody as (b & Hbody).
    inversion Hbody. subst. clear Hbody.
    unfold bool_expr_branches, loop_body_marker in *. apply proj1 in H1.
    eexists. destruct_one_match_hyp;
      (econstructor; [eassumption | reflexivity | unfold bool_expr_branches]);
      ssplit; rewrite ?word.eqb_ne, ?word.eqb_eq by congruence; simpl; try exact I.
    2: assumption.
    eapply exec.weaken. 1: eassumption.
    cbv beta. clear H1. intros. fwd. inversion H0. subst. clear H0.
    eexists. econstructor. 1: eassumption. 1: reflexivity.
    unfold bool_expr_branches, provide_new_ghosts, state_implication in *.
    destruct_one_match_hyp; fwd; eauto 10.
  Qed.

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
    constructor. 2: assumption. inversion Hde. unfold WeakestPrecondition.dexpr in *.
    cbn. eapply weaken_expr. 1: eassumption. intros. subst.
    unfold dexprs in Hde0. eapply WeakestPreconditionProperties.Proper_list_map.
    3: eassumption.
    { intros ? ? ? ? ? . eapply weaken_expr. 1: eassumption. assumption. }
    { intros ? ?. subst. reflexivity. }
  Qed.

  Lemma wp_call0 fs t m l fname resnames es vs (post: trace -> mem -> locals -> Prop):
      dexprs m l es vs ->
      call fs fname t m vs (fun t' m' rets =>
        exists l', map.putmany_of_list_zip resnames rets l = Some l' /\ post t' m' l') ->
      wp_cmd fs (cmd.call resnames fname es) t m l post.
  Proof.
    intros. unfold call in *. fwd.
    unfold dexprs, WeakestPrecondition.dexprs in *.
    eapply WeakestPreconditionProperties.sound_args in H. fwd.
    econstructor; try eassumption.
    cbv beta. intros *. exact id.
  Qed.

  Lemma wp_call: forall fs fname t m resnames arges argvs l rest
      (calleePre: Prop)
      (calleePost: trace -> mem -> list word -> Prop)
      (finalPost: trace -> mem -> locals -> Prop),
      (* definition-site format: *)
      (calleePre -> WeakestPrecondition.call fs fname t m argvs calleePost) ->
      (* use-site format: *)
      dexprs1 m l arges argvs (calleePre /\ enable_frame_trick (
         forall t' m' retvs, calleePost t' m' retvs ->
                             update_locals resnames retvs l (fun l' =>
                                 wp_cmd fs rest t' m' l' finalPost))) ->
      (* conclusion: *)
      wp_cmd fs (cmd.seq (cmd.call resnames fname arges) rest) t m l finalPost.
  Proof.
    intros. inversion H0. clear H0. destruct Hp as (Pre & Impl).
    unfold enable_frame_trick in *.
    setoid_rewrite update_locals_spec in Impl.
    specialize (H Pre). clear Pre.
    eapply wp_seq.
    eapply wp_call0. 1: eassumption.
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

  Lemma prove_func: forall fs f argnames retnames body t m argvals l post,
      map.get fs f = Some (argnames, retnames, body) ->
      map.of_list_zip argnames argvals = Some l ->
      wp_cmd fs body t m l (fun t' m' l' => exists retvals,
                                map.getmany_of_list l' retnames = Some retvals /\
                                  post t' m' retvals) ->
      WeakestPrecondition.call fs f t m argvals post.
  Proof.
    intros.
    do 4 eexists. 1: eassumption. do 2 eexists. 1: eassumption.
    assumption.
  Qed.

  (* applied at beginning of void functions *)
  Lemma simplify_no_return_post: forall fs body t m l P,
      wp_cmd fs body t m l (fun t' m' l' => P t' m') ->
      wp_cmd fs body t m l (fun t' m' l' =>
        exists retvals: list word,
        map.getmany_of_list l' nil = Some retvals /\
        (retvals = nil /\ P t' m')).
  Proof.
    intros. eapply Semantics.exec.weaken. 1: eassumption.
    cbv beta. intros. fwd. eexists.
    split. 1: reflexivity. auto.
  Qed.

  Definition RETNAME := "RET"%string.

  Inductive expect_1expr_return
    (P: trace -> mem -> word -> Prop)(t: trace)(m: mem)(l: locals): Prop :=
  | mk_expect_1expr_return(retv: word)(G: map.get l RETNAME = Some retv)(HP: P t m retv).

  (* applied at the beginning of functions with 1 return value *)
  Lemma simplify_1retval_post: forall fs body t m l P,
      wp_cmd fs body t m l (expect_1expr_return P) ->
      wp_cmd fs body t m l (fun t' m' l' =>
        exists retvals : list word,
        map.getmany_of_list l' (cons RETNAME nil) = Some retvals /\
        (exists retv, retvals = cons retv nil /\ P t' m' retv)).
  Proof.
    intros. eapply Semantics.exec.weaken. 1: eassumption.
    intros. inversion H0. subst. clear H0. eexists.
    split. {
      simpl. unfold map.getmany_of_list. simpl. rewrite G. reflexivity.
    }
    eauto.
  Qed.

  (* Applied at the end of a function with one return value,
     when the user provides a return statement.
     post will have a shape like
     (fun t' m' l' => expect_1expr_return P t' m' (map.remove (.. (map.remove l' x) ..) y))
     ie all the locals (except the function arguments) were removed for scoping reasons,
     and l will have a shape like
     (map.of_list (cons (_, _) (.. (cons (_, _) nil) ..))).
     Therefore, the first two goals should be solvable by reflexivity. *)
  Lemma wp_return: forall fs e t m l lShrunk retv P post,
      post t m (map.put l RETNAME retv) = expect_1expr_return P t m lShrunk ->
      map.get lShrunk RETNAME = Some retv ->
      (* Note: this would be simpler, but for uniformity, we insert a superfluous
         cmd.skip, so that the closing brace always applies wp_skip
      dexpr1 m l e (fun retv => P t m retv) *)
      dexpr1 m l e retv (wp_cmd fs cmd.skip t m l (fun _ _ _ => P t m retv)) ->
      wp_cmd fs (cmd.set RETNAME e) t m l post.
  Proof.
    intros. inversion H1. clear H1.
    eapply wp_set00. 1: eassumption.
    inversion Hp. cbn in H1.
    rewrite H. econstructor. 2: eassumption. assumption.
  Qed.

End WithParams.
