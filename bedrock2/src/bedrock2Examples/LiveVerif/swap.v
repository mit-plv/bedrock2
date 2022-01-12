Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Z.Lia.
Require Import coqutil.Byte coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Datatypes.Inhabited.
Require Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.rewr coqutil.Tactics.rdelta.
Require Import Coq.Program.Tactics.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.OfListWord.
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
Require Import bedrock2Examples.LiveVerif.string_to_ident.
Require Import bedrock2Examples.LiveVerif.ident_to_string.
Import List.ListNotations. Local Open Scope list_scope.

Ltac eqapply A :=
  let t := type of A in
  let g := lazymatch goal with |- ?G => G end in
  replace g with t; [exact A|f_equal..].

Ltac head t :=
  lazymatch t with
  | ?f _ => head f
  | _ => t
  end.

Ltac eqassumption :=
  multimatch goal with
  | H: ?T |- ?U => let hT := head T in let hU := head U in constr_eq hT hU; eqapply H
  end.


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


Require Import Coq.Program.Tactics.
Require Import coqutil.Tactics.autoforward.

#[export] Hint Extern 1
  (autoforward (word.unsigned (if _ then (word.of_Z 1) else (word.of_Z 0)) = 0) _)
  => rapply @word.if_zero : typeclass_instances.

#[export] Hint Extern 1
  (autoforward (word.unsigned (if _ then (word.of_Z 1) else (word.of_Z 0)) <> 0) _)
  => rapply @word.if_nonzero : typeclass_instances.

(*#[export] not supported in 8.13 yet*)
Hint Rewrite @word.unsigned_ltu using typeclasses eauto: fwd_rewrites.
Hint Rewrite @word.signed_lts using typeclasses eauto: fwd_rewrites.

Ltac fwd_rewrites ::= fwd_rewrites_autorewrite.


Inductive get_option{A: Type}: option A -> (A -> Prop) -> Prop :=
| mk_get_option: forall (a: A) (post: A -> Prop), post a -> get_option (Some a) post.

Module Import SepLogPredsWithAddrLast. Section __.
  Context {width : Z} {word : Word.Interface.word width} {mem : map.map word byte}.

  Definition at_addr(addr: word)(clause: word -> mem -> Prop): mem -> Prop := clause addr.

  (* Redefinitions to change order of arguments to put address last *)

  Definition ptsto_bytes (n : nat) (value : tuple byte n) (addr : word) : mem -> Prop :=
    ptsto_bytes n addr value.

  Definition littleendian (n : nat) (value : Z) (addr : word) : mem -> Prop :=
    littleendian n addr value.

  Definition truncated_scalar sz (value : Z) addr : mem -> Prop :=
    truncated_scalar sz addr value.

  Definition truncated_word sz (value: word) addr : mem -> Prop :=
    truncated_word sz addr value.

  Definition scalar16 := truncated_word Syntax.access_size.two.
  Definition scalar32 := truncated_word Syntax.access_size.four.
  Definition scalar := truncated_word Syntax.access_size.word.

  Definition word_array(vs: list word)(addr: word): mem -> Prop :=
    array Scalars.scalar (word.of_Z (bytes_per_word width)) addr vs.
End __. End SepLogPredsWithAddrLast.

(* `*` is at level 40, and we want to bind stronger than `*`,
   and moreover, `^` is at level 30, and for consistency, we also want to bind stronger than `^`,
   so we choose 25 *)
Notation "addr |-> clause" := (at_addr addr clause)
  (at level 25,
   format "addr  |->  '[' clause ']'").

Module expr.
  Axiom ite : expr.expr -> expr.expr -> expr.expr -> expr.expr.
  Definition lazy_and(e1 e2: expr.expr) := ite e1 e2 (expr.literal 0).
  (* If e1 is nonzero, both returning 1 and returning e1 could make sense,
     but we follow C, which returns 1:
     https://stackoverflow.com/questions/30621389/short-circuiting-of-non-booleans *)
  Definition lazy_or(e1 e2: expr.expr) := ite e1 (expr.literal 1) e2.
End expr.

Module bopname.
  Axiom eager_and: bopname.
End bopname.

Section SepLog.
  Context {word: word.word 32} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma load_of_sep_cps: forall sz addr value R m (post: word -> Prop),
      sep (addr |-> truncated_word sz value) R m /\ post (truncate_word sz value) ->
      get_option (Memory.load sz m addr) post.
  Proof.
    intros. destruct H. eapply load_of_sep in H. rewrite H.
    constructor. assumption.
  Qed.

  Lemma load_word_of_sep_cps: forall addr value R m (post: word -> Prop),
      sep (addr |-> scalar value) R m /\ post value ->
      get_option (Memory.load Syntax.access_size.word m addr) post.
  Proof.
    intros. destruct H. eapply load_word_of_sep in H. rewrite H.
    constructor. assumption.
  Qed.

  Lemma store_word_of_sep_cps_two_subgoals: forall addr oldvalue newvalue R m (post: mem -> Prop),
      seps [addr |-> scalar oldvalue; R] m ->
      (forall m', seps [addr |-> scalar newvalue; R] m' -> post m') ->
      get_option (Memory.store access_size.word m addr newvalue) post.
  Proof.
    intros. eapply Scalars.store_word_of_sep in H. 2: eassumption.
    destruct H as (m1 & E & P). rewrite E. constructor. exact P.
  Qed.

  Lemma store_word_of_sep_cps: forall addr oldvalue newvalue R m (post: mem -> Prop),
      seps [addr |-> scalar oldvalue; R;
            emp (forall m', seps [addr |-> scalar newvalue; R] m' -> post m')] m ->
      get_option (Memory.store access_size.word m addr newvalue) post.
  Proof.
    intros. unfold seps in H. apply sep_assoc in H. apply sep_emp_r in H. destruct H.
    eapply store_word_of_sep_cps_two_subgoals. 1: unfold seps. 1: eassumption. eassumption.
  Qed.

  (* R, typically instantiated to `seps [whatever; is; left]`, appears twice:
     On the left of the impl1 (this determines its value), and as the first
     element of the `seps` on the right (there, it is an evar for the frame).
     P is the continuation postcondition. *)
  Lemma impl1_done: forall (R: mem -> Prop) (P: Prop),
      P -> impl1 R (seps [R; emp P]).
  Proof.
    unfold impl1, seps. intros. apply sep_emp_r. auto.
  Qed.

  (* Intended usage:
     P:  input without evars
     P1: input with some evars
     P2: evar (output) *)
  Definition split_sepclause(P P1: mem -> Prop)(P2: list (mem -> Prop)): Prop :=
    iff1 P (seps (P1 :: P2)).

  Local Infix "++" := SeparationLogic.app. Local Infix "++" := app : list_scope.
  Let nth n xs := SeparationLogic.hd (emp(map:=mem) True) (SeparationLogic.skipn n xs).
  Let remove_nth n (xs : list (mem -> Prop)) :=
    (SeparationLogic.firstn n xs ++ SeparationLogic.tl (SeparationLogic.skipn n xs)).

  Lemma impl1_cancel_part_of_ith_left_with_first_right: forall i L F R1 RRest,
      split_sepclause (nth i L) R1 F ->
      impl1 (seps (remove_nth i L ++ F)) (seps RRest) ->
      impl1 (seps L) (seps (R1 :: RRest)).
  Proof.
    intros.
    unfold nth, remove_nth, split_sepclause in *.
    rewrite <-(seps_nth_to_head i L).
    rewrite H.
    rewrite <-seps'_iff1_seps.
    cbn [seps'].
    rewrite seps_app in H0.
    rewrite <-(seps'_iff1_seps (R1 :: RRest)).
    cbn [seps'].
    cancel.
    ecancel_step_by_implication.
    cbn [seps].
    rewrite !seps'_iff1_seps.
    etransitivity. 2: eassumption.
    ecancel.
  Qed.

  Lemma access_word_array: forall a a' vs,
      let i := Z.to_nat (word.unsigned (word.sub a' a) / 4) in
      (i < List.length vs)%nat ->
      a' = word.add a (word.of_Z (4 * Z.of_nat i)) ->
      split_sepclause (a |-> word_array vs)
        (a' |-> scalar (List.nth i vs (word.of_Z 0)))
        [a |-> word_array (List.firstn i vs);
         word.add a (word.of_Z (4 * Z.of_nat (S i))) |-> word_array (List.skipn (S i) vs)].
  Proof.
    unfold split_sepclause. intros.
    rewrite <- (List.firstn_nth_skipn _ _ vs (word.of_Z 0)) at 1 by eassumption.
    unfold word_array, scalar, truncated_word, Scalars.scalar, at_addr, seps.
    cbn [List.app].
    etransitivity.
    1: eapply array_append.
    cbn [array].
    change (bytes_per_word _) with 4.
    cancel.
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. ZnWords.
    }
    cancel_seps_at_indices 0%nat 0%nat. {
      f_equal. ZnWords.
    }
    reflexivity.
  Qed.
End SepLog.

Existing Class split_sepclause.

#[export] Hint Extern 1 (split_sepclause (_ |-> word_array _) (_ |-> scalar _) _) =>
  rapply access_word_array; ZnWords : typeclass_instances.

Section WithParams.
  Import bedrock2.Syntax.
  Context {word: word.word 32} {mem: map.map word byte} {locals: map.map string word}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {locals_ok: map.ok locals}.
  Context {ext_spec: ExtSpec}.

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
    unfold expr.lazy_and. intros. eapply wp_ite. eapply weaken_wp_expr. 1: exact H. clear H.
    cbv beta. intros. fwd. destruct_one_match; subst; do 2 eexists; split; try eassumption.
    eapply wp_literal. reflexivity.
  Qed.

  Lemma wp_lazy_or: forall m l e1 e2 (post: word -> Prop),
      wp_expr m l e1 (fun b1 => exists b,
        (if Z.eqb (word.unsigned b1) 0 then wp_expr m l e2 (eq b) else b = word.of_Z 1) /\
        (post b)) ->
      wp_expr m l (expr.lazy_or e1 e2) post.
  Proof.
    unfold expr.lazy_or. intros. eapply wp_ite. eapply weaken_wp_expr. 1: exact H. clear H.
    cbv beta. intros. fwd. destruct_one_match; subst; do 2 eexists; split; try eassumption.
    eapply wp_literal. reflexivity.
  Qed.

  Lemma wp_load_anysize: forall m l sz addr (post: word -> Prop),
      wp_expr m l addr (fun a =>
        exists v R, seps [a |-> truncated_word sz v; R; emp (post (truncate_word sz v))] m) ->
      wp_expr m l (expr.load sz addr) post.
  Proof.
    intros. constructor. cbn. unfold load. inversion H.
    eapply WeakestPreconditionProperties.Proper_expr. 2: eassumption.
    cbv [Morphisms.pointwise_relation Basics.impl]. intros.
    destruct H1 as (v & R & H1). cbn [seps] in H1.
    apply sep_assoc in H1.
    apply sep_emp_r in H1.
    destruct H1 as [Hm Hpost].
    eapply load_of_sep in Hm.
    eauto.
  Qed.

  Lemma wp_load_word: forall m l addr (post: word -> Prop),
      wp_expr m l addr (fun a =>
        exists v R, seps [a |-> scalar v; R; emp (post v)] m) ->
      wp_expr m l (expr.load access_size.word addr) post.
  Proof.
    intros. eapply wp_load_anysize.
    eapply weaken_wp_expr. 1: exact H. cbv beta.
    unfold scalar, truncate_word, truncate_Z.
    clear H.
    intros. destruct H as (val & R & H). exists val, R.
    rewrite Z.land_ones.
    2: cbv; discriminate.
    rewrite Z.mod_small.
    2: apply word.unsigned_range.
    rewrite word.of_Z_unsigned.
    exact H.
  Qed.

  Lemma wp_load_old: forall m l sz addr (post: word -> Prop),
      wp_expr m l addr (fun a => get_option (Memory.load sz m a) post) ->
      wp_expr m l (expr.load sz addr) post.
  Proof.
    intros. constructor. cbn. unfold load. inversion H.
    eapply WeakestPreconditionProperties.Proper_expr. 2: eassumption.
    cbv [Morphisms.pointwise_relation Basics.impl]. intros. inversion H1. subst. eauto.
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
    intros. destruct H. unfold dexpr. revert e post H.
    induction e; cbn;
    unfold literal, dlet.dlet, WeakestPrecondition.get;
    intros;
    fwd;
    eauto.
    { unfold load in *.
      specialize IHe with (1 := H).
      fwd.
      exists v0. split. 2: assumption.
      eapply WeakestPreconditionProperties.Proper_expr.
      2: eapply WeakestPreconditionProperties.intersect_expr.
      2: eapply IHep0.
      2: eapply H.
      unfold Morphisms.pointwise_relation, Basics.impl. intros. fwd.
      eexists. split. 1: eassumption. congruence. }
    { unfold load in *.
      specialize IHe with (1 := H).
      fwd.
      exists v0. split. 2: assumption.
      eapply WeakestPreconditionProperties.Proper_expr.
      2: eapply WeakestPreconditionProperties.intersect_expr.
      2: eapply IHep0.
      2: eapply H.
      unfold Morphisms.pointwise_relation, Basics.impl. intros. fwd.
      eexists. split. 1: eassumption. congruence. }
    { specialize IHe1 with (1 := H).
      fwd.
      specialize IHe2 with (1 := IHe1p1).
      fwd.
      eexists. split. 2: eassumption.
      eapply WeakestPreconditionProperties.Proper_expr.
      2: eapply WeakestPreconditionProperties.intersect_expr.
      2: eapply IHe1p0.
      2: eapply H.
      unfold Morphisms.pointwise_relation, Basics.impl. intros. fwd.
      eapply WeakestPreconditionProperties.Proper_expr.
      2: eapply WeakestPreconditionProperties.intersect_expr.
      2: eapply IHe2p0.
      2: eapply H0p1.
      unfold Morphisms.pointwise_relation, Basics.impl. intros. fwd.
      reflexivity. }
  Qed.

  Definition interp_expr_total_body(rec: expr -> word)(m: mem)(l: locals)(e: expr): word :=
    match e with
    | expr.literal v => word.of_Z v
    | expr.var x => Option.force (map.get l x)
    | expr.load sz a => Option.force (Memory.load sz m (rec a))
    | expr.inlinetable sz bs i =>
        Option.force (Memory.load sz (map.of_list_word bs) (rec i))
    | expr.op op a b => interp_binop op (rec a) (rec b)
    end.

  Definition interp_expr_total(m: mem)(l: locals): expr -> word :=
    fix rec(e: expr) := interp_expr_total_body rec m l e.

  Axiom interp_expr_total_ite: forall m l e1 e2 e3,
      interp_expr_total m l (expr.ite e1 e2 e3) =
      interp_expr_total m l
        (if word.unsigned (interp_expr_total m l e1) =? 0 then e3 else e2).

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
  Admitted.

  Inductive dexpr_bool_prop(m: mem)(l: locals)(e: expr): Prop -> Prop :=
    mk_dexpr_bool_prop: forall b: word,
      dexpr m l e b ->
      dexpr_bool_prop m l e (word.unsigned b <> 0).

  Lemma dexpr_lazy_and: forall m l e1 e2 (P1 P2: Prop),
      dexpr_bool_prop m l e1 P1 ->
      (P1 -> dexpr_bool_prop m l e2 P2) ->
      dexpr_bool_prop m l (expr.lazy_and e1 e2) (P1 /\ P2).
  Proof.
    unfold expr.lazy_and. intros.
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

  Axiom interp_eager_and: forall (x y: word),
      interp_binop bopname.eager_and x y =
        if andb (negb (word.eqb x (word.of_Z 0)))
                (negb (word.eqb y (word.of_Z 0)))
        then word.of_Z 1 else word.of_Z 0.

  Lemma wp_bool_eager_and''': forall m l e1 e2 (post: Prop -> Prop),
      wp_expr_bool_prop m l e1 (fun P1 =>
        wp_expr_bool_prop m l e2 (fun P2 =>
          post (P1 /\ P2))) ->
      wp_expr_bool_prop m l (expr.op bopname.eager_and e1 e2) post.
  Proof.
    unfold wp_expr_bool_prop. intros. eapply wp_op.
    eapply weaken_wp_expr. 1: exact H. clear H. cbv beta.
    intros. eapply weaken_wp_expr. 1: exact H. clear H. cbv beta.
    intros. rewrite interp_eager_and.
    destr (word.eqb v (word.of_Z 0)); destr (word.eqb v0 (word.of_Z 0)); simpl;
      rewrite ?word.unsigned_of_Z_0, ?word.unsigned_of_Z_1 in *.
    all: eqassumption.
    all: apply PropExtensionality.propositional_extensionality; split; intros;
      (Lia.lia || congruence || auto).
    split; intro C.
    - apply E. ZnWords.
    - apply E0. ZnWords.
  Qed.

  Inductive wp_cmd(call: (string -> trace -> mem -> list word ->
                          (trace -> mem -> list word -> Prop) -> Prop))
            (c: cmd)(t: trace)(m: mem)(l: locals)(post: trace -> mem -> locals -> Prop): Prop :=
    mk_wp_cmd: WeakestPrecondition.cmd call c t m l post -> wp_cmd call c t m l post.

  Lemma weaken_wp_cmd: forall call c t m l (post1 post2: _->_->_->Prop),
      wp_cmd call c t m l post1 ->
      (forall t m l, post1 t m l -> post2 t m l) ->
      wp_cmd call c t m l post2.
  Proof.
    intros. constructor. inversion H.
    eapply WeakestPreconditionProperties.Proper_cmd. 3: eassumption.
    1: admit.
    cbv [RelationClasses.Reflexive Morphisms.pointwise_relation Morphisms.respectful Basics.impl].
    assumption.
  Admitted. (* TODO some Proper_call and some shelved params *)

  Lemma wp_set: forall call x a t m l rest post,
      wp_expr m l a
        (fun v => wp_cmd call rest t m (map.put l x v) post) ->
      wp_cmd call (cmd.seq (cmd.set x a) rest) t m l post.
  Proof.
    intros. eapply wp_expr_to_dexpr in H. fwd. destruct Hp1.
    constructor. cbn. unfold dlet.dlet. eauto.
  Qed.

  Notation "'let/c' x := r 'in' b" := (r (fun x => b)) (x binder, at level 200, only parsing).

  Lemma wp_store: forall call sz ea ev t m l rest post,
      (let/c a := wp_expr m l ea in
       let/c v := wp_expr m l ev in
       let/c m' := get_option (Memory.store sz m a v) in
       wp_cmd call rest t m' l post) ->
      wp_cmd call (cmd.seq (cmd.store sz ea ev) rest) t m l post.
  Proof.
    intros *.
  Abort.
  (* TODO can we disable Coq's auto-eta-expansion to make this notation print like written above?*)

  Lemma wp_store0: forall call sz ea ev t m l rest post,
      wp_expr m l ea (fun a =>
        wp_expr m l ev (fun v =>
          get_option (Memory.store sz m a v) (fun m' =>
            wp_cmd call rest t m' l post))) ->
      wp_cmd call (cmd.seq (cmd.store sz ea ev) rest) t m l post.
  Proof.
    intros. constructor. cbn.
    eapply wp_expr_to_dexpr in H. unfold dexpr in *. fwd.
    eapply wp_expr_to_dexpr in Hp1. unfold dexpr in *. fwd.
    inversion Hp1p1. inversion H0. subst. unfold store. symmetry in H. eauto 10.
  Qed.

  Lemma wp_store: forall call ea ev t m l rest post,
      wp_expr m l ea (fun addr =>
        wp_expr m l ev (fun newvalue => exists oldvalue R,
          seps [addr |-> scalar oldvalue; R;
                emp (forall m', seps [addr |-> scalar newvalue; R] m' ->
                                wp_cmd call rest t m' l post)] m)) ->
      wp_cmd call (cmd.seq (cmd.store access_size.word ea ev) rest) t m l post.
  Proof.
    intros.
    eapply wp_store0.
    eapply weaken_wp_expr. 1: eassumption. clear H. cbv beta. intros.
    eapply weaken_wp_expr. 1: eassumption. clear H. cbv beta. intros. fwd.
    eapply store_word_of_sep_cps. eassumption.
  Qed.

  Lemma wp_if0: forall call c thn els rest t m l post,
      wp_expr m l c (fun b => exists Q1 Q2,
        ((word.unsigned b <> 0 -> wp_cmd call thn t m l Q1) /\
         (word.unsigned b =  0 -> wp_cmd call els t m l Q2)) /\
        (forall t' m' l', word.unsigned b <> 0 /\ Q1 t' m' l' \/
                          word.unsigned b =  0 /\ Q2 t' m' l' ->
                          wp_cmd call rest t' m' l' post)) ->
      wp_cmd call (cmd.seq (cmd.cond c thn els) rest) t m l post.
  Proof.
    intros. constructor. cbn.
    eapply wp_expr_to_dexpr in H. fwd.
    eexists. split; [eassumption|]. split; intros.
    - eapply WeakestPreconditionProperties.Proper_cmd. 3: eapply Hp1p0p0; eassumption.
      1: admit.
      unfold Morphisms.pointwise_relation, Basics.impl. intros. eapply Hp1p1. eauto.
    - eapply WeakestPreconditionProperties.Proper_cmd. 3: eapply Hp1p0p1; eassumption.
      1: admit.
      unfold Morphisms.pointwise_relation, Basics.impl. intros. eapply Hp1p1. eauto.
  Admitted.

  Lemma wp_if: forall call c l vars vals thn els rest t m post,
      l = reconstruct vars vals ->
      wp_expr m l c (fun b =>
        exists (Q1 Q2: trace -> mem -> locals -> Prop),
          ((word.unsigned b <> 0 -> wp_cmd call thn t m l (fun t' m' l' =>
              exists vals', l' = reconstruct vars vals' /\ Q1 t' m' l')) /\
           (word.unsigned b =  0 -> wp_cmd call els t m l (fun t' m' l' =>
              exists vals', l' = reconstruct vars vals' /\ Q2 t' m' l'))) /\
          (forall t' m' vals', let l' := reconstruct vars vals' in
                               word.unsigned b <> 0 /\ Q1 t' m' l' \/
                               word.unsigned b =  0 /\ Q2 t' m' l' ->
                               wp_cmd call rest t' m' l' post)) ->
      wp_cmd call (cmd.seq (cmd.cond c thn els) rest) t m l post.
  Proof.
    intros. subst. eapply wp_if0. eapply weaken_wp_expr. 1: exact H0. clear H0. cbv beta.
    intros v (Q1 & Q2 & A & B). eexists. eexists. split. 1: exact A. clear A. cbv beta.
    intros * [? | ?]; fwd; eapply B; eauto.
  Qed.

  Lemma wp_if_bool: forall call c l vars vals thn els rest t m Q1 Q2 post,
      l = reconstruct vars vals ->
      wp_expr_bool_prop m l c (fun P =>
        ((P  -> wp_cmd call thn t m l (fun t' m' l' =>
                  exists vals', l' = reconstruct vars vals' /\ Q1 t' m' l')) /\
         (~P -> wp_cmd call els t m l (fun t' m' l' =>
                  exists vals', l' = reconstruct vars vals' /\ Q2 t' m' l'))) /\
        (forall t' m' vals', let l' := reconstruct vars vals' in
                             P  /\ Q1 t' m' l' \/
                             ~P /\ Q2 t' m' l' ->
                             wp_cmd call rest t' m' l' post)) ->
      wp_cmd call (cmd.seq (cmd.cond c thn els) rest) t m l post.
  Admitted.

  Lemma wp_if_bool_dexpr: forall call c vars vals thn els rest t m P Q1 Q2 post,
      dexpr_bool_prop m (reconstruct vars vals) c P ->
      (P  -> wp_cmd call thn t m (reconstruct vars vals) (fun t' m' l' =>
               exists vals', l' = reconstruct vars vals' /\ Q1 t' m' l')) ->
      (~P -> wp_cmd call els t m (reconstruct vars vals) (fun t' m' l' =>
               exists vals', l' = reconstruct vars vals' /\ Q2 t' m' l')) ->
      (forall (cond0: bool) t' m' vals',
          (* (if cond0 then P else ~P) -> <-- already added to Q1/Q2 by automation *)
          (if cond0 then Q1 t' m' (reconstruct vars vals')
           else Q2 t' m' (reconstruct vars vals')) ->
          wp_cmd call rest t' m' (reconstruct vars vals') post) ->
      wp_cmd call (cmd.seq (cmd.cond c thn els) rest) t m (reconstruct vars vals) post.
  Admitted.

  (* The postcondition of the callee's spec will have a concrete shape that differs
     from the postcondition that we pass to `call`, so when using this lemma, we have
     to apply weakening for `call`, which generates two subgoals:
     1) call f t m argvals ?mid
     2) forall t' m' resvals, ?mid t' m' resvals -> the post of `call`
     To solve 1), we will apply the callee's spec, but that means that if we make
     changes to the context while solving the preconditions of the callee's spec,
     these changes will not be visible in subgoal 2 *)
  Lemma wp_call: forall call binds f argexprs rest t m l post,
      wp_exprs m l argexprs (fun argvals =>
        call f t m argvals (fun t' m' resvals =>
          get_option (map.putmany_of_list_zip binds resvals l) (fun l' =>
            wp_cmd call rest t' m' l' post))) ->
      wp_cmd call (cmd.seq (cmd.call binds f argexprs) rest) t m l post.
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

  Lemma wp_skip: forall call t m l (post: trace -> mem -> locals -> Prop),
      post t m l ->
      wp_cmd call cmd.skip t m l post.
  Proof. intros. constructor. assumption. Qed.

  (* to avoid using `remember` and having to control which occurrence we want to remember *)
  Lemma wp_locals_put: forall call c x v t m l post,
      (forall a, a = v -> wp_cmd call c t m (map.put l x a) post) ->
      wp_cmd call c t m (map.put l x v) post.
  Proof. auto. Qed.

  Definition vc_func call '(innames, outnames, body) (t: trace) (m: mem) (argvs: list word)
                     (post : trace -> mem -> list word -> Prop) :=
    exists l, map.of_list_zip innames argvs = Some l /\
      wp_cmd call body t m l (fun t' m' l' =>
        exists retvs, map.getmany_of_list l' outnames = Some retvs /\ post t' m' retvs).

  Definition arguments_marker(args: list word): list word := args.

End WithParams.

Declare Scope live_scope.
Delimit Scope live_scope with live.
Local Open Scope live_scope.

Inductive scope_kind := FunctionBody | ThenBranch | ElseBranch | LoopBody.
Inductive scope_marker: scope_kind -> Set := mk_scope_marker sk : scope_marker sk.
Notation "'____' sk '____'" := (scope_marker sk) (only printing) : live_scope.

Ltac assert_scope_kind expected :=
  let sk := lazymatch goal with
            | H: scope_marker ?sk |- _ => sk
            | _ => fail "no scope marker found"
            end in
  tryif constr_eq sk expected then idtac
  else fail "This snippet is only allowed in a" expected "block, but we're in a" sk "block".

(*
Notation "'ready' 'for' 'next' 'command'" := (wp_cmd _ _ _ _ _ _)
  (at level 0, only printing) : live_scope.
*)

Declare Scope reconstruct_locals_scope.
Delimit Scope reconstruct_locals_scope with reconstruct_locals.

Notation "[ x ]" := (PrimitivePair.pair.mk x tt)
  (only printing) : reconstruct_locals_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (PrimitivePair.pair.mk x (PrimitivePair.pair.mk y .. (PrimitivePair.pair.mk z tt) ..))
  (only printing) : reconstruct_locals_scope.

Notation "l" := (arguments_marker l)
  (at level 100, only printing) : live_scope.

Module Import MySepNotations.

Declare Scope sep_list_scope.
Delimit Scope sep_list_scope with sep_list.

Notation "* x * y * .. * z" :=
  (@cons (@map.rep _ _ _ -> Prop) x
    (@cons (@map.rep _ _ _ -> Prop) y
      .. (@cons (@map.rep _ _ _ -> Prop) z nil) .. ))
  (at level 39, x at level 39, y at level 39, z at level 39,
   (* starting with a space to make sure we never create an opening comment *)
   format " '[v' *  x  '//' *  y  '//' *  ..  '//' *  z  ']'")
  : sep_list_scope.

Notation "m 'satisfies' <{ l }>" := (seps l%sep_list m)
  (at level 10,
   format "'[v' m  'satisfies'  <{ '//'  l '//' }> ']'")
  : live_scope.

Notation "<{ l1 }> ==> <{ l2 }>" := (impl1 (seps l1%sep_list) (seps l2%sep_list))
  (at level 10,
   format "'[v' <{ l1 '//' }>  ==>  <{ '//'   l2 '//' }> ']'")
  : live_scope.

Notation "<{ l1 }> <==> <{ l2 }>" := (iff1 (seps l1%sep_list) (seps l2%sep_list))
  (at level 10,
   format "'[v' <{ l1 '//' }>  <==>  <{ '//'   l2 '//' }> ']'")
  : live_scope.

End MySepNotations.

Section NotationTests.
  Context {width : Z} {word : Word.Interface.word width} {mem : map.map word byte}.

  Goal Some (fun (a b: word) (v: word) =>
               seps ( * (a |-> scalar v) * (b |-> scalar v) * (emp True) )%sep_list) = None.
  Abort.

  Goal (forall (a b: word) (v: word) (current_mem: mem),
          seps ( * a |-> scalar v * b |-> scalar v * emp True )%sep_list current_mem).
  Proof. intros. (*
  Note how `satisfies` does not increase the indentation of the `*` bullet points,
  each bullet point is indented by just two spaces:

  current_mem satisfies <{
    * a |-> scalar v
    * b |-> scalar v
    * emp True
  }>
  *)
  match goal with |- ?G => enough G as M end. Abort.

  Context (a b c d e f g h: word) (frobnicate: word -> word -> word) (v: word).

  Let manyseps := (
     * a |-> scalar v * b |-> scalar v * emp True * c |-> scalar v
     * d |->  scalar v
     * e |-> scalar (frobnicate (frobnicate (frobnicate v (frobnicate v v)) (frobnicate
          (frobnicate v (frobnicate v v)) (frobnicate v (frobnicate v v)))) (frobnicate v v))
     * f |-> scalar v
     * (frobnicate (frobnicate (frobnicate v (frobnicate v v)) (frobnicate
          (frobnicate v (frobnicate v v)) (frobnicate v (frobnicate v v)))) (frobnicate v v)) |->
       scalar v
     * h |-> (scalar v) * emp True
     * (frobnicate (frobnicate (frobnicate v (frobnicate v v)) (frobnicate
          (frobnicate v (frobnicate v v)) (frobnicate v (frobnicate v v)))) (frobnicate v v)) |->
       scalar (frobnicate (frobnicate (frobnicate v (frobnicate v v)) (frobnicate
          (frobnicate v (frobnicate v v)) (frobnicate v (frobnicate v v)))) (frobnicate v v))
  )%sep_list.

  Goal forall (a b c d e f g h: word) (frobnicate: word -> word -> word) (v: word) (m: mem),
     m satisfies <{ manyseps }>.
  Proof.
    intros. subst manyseps. match goal with |- ?G => enough G end.
  Abort.

  Goal forall (a b: word) (v: word),
    <{ * a |-> scalar v
       * b |-> scalar v
       * emp True
    }> ==> <{
       * b |-> scalar v
       * a |-> scalar v
    }>.
  Proof. intros. match goal with |- ?G => enough G end. Abort.

  Goal forall (a b: word) (v: word),
    <{ manyseps }> ==> <{
       * b |-> scalar v
       * a |-> scalar v
    }>.
  Proof. intros. subst manyseps. match goal with |- ?G => enough G end. Abort.

  Goal forall (a b: word) (v: word),
    <{ manyseps }> <==> <{
       * b |-> scalar v
       * a |-> scalar v
    }>.
  Proof. intros. subst manyseps. match goal with |- ?G => enough G end. Abort.

End NotationTests.

Ltac impl_ecancel_step_with_splitting :=
  lazymatch goal with
  | |- Lift1Prop.impl1 (seps ?L) (seps (?R1 :: ?RRest)) =>
    let iLi := index_and_element_of L in (* <-- multi-success! *)
    let i := lazymatch iLi with (?i, _) => i end in
    let Li := lazymatch iLi with (_, ?Li) => Li end in
    refine (impl1_cancel_part_of_ith_left_with_first_right i _ _ R1 RRest _ _);
    cbn [hd app firstn tl skipn];
    [typeclasses eauto|]
  end.

Ltac ecancel_with_remaining_emp_Prop :=
  cancel_seps;
  repeat ecancel_step_by_implication;
  repeat impl_ecancel_step_with_splitting;
  refine (impl1_done _ _ _).

Ltac ecancel_assumption_with_remaining_emp_Prop :=
  match goal with
  | H: seps _ ?m |- seps _ ?m =>
    refine (Morphisms.subrelation_refl Lift1Prop.impl1 _ _ _ m H)
  end;
  ecancel_with_remaining_emp_Prop.

Ltac simpli_step :=
  match goal with
  | H: context[word.unsigned ?x] |- _ => progress (ring_simplify x in H)
  | H: context[word.unsigned (word.of_Z _)] |- _ =>
    rewrite word.unsigned_of_Z_nowrap in H by Lia.lia
  | _ => progress groundcbv_in_all
  end.

Ltac is_fresh x := assert_succeeds (pose proof tt as x).

Ltac make_fresh x :=
  tryif is_fresh x then idtac else let x' := fresh x "_0" in rename x into x'.

Ltac put_into_current_locals is_decl :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.put ?l ?x ?v) _ =>
    let i := string_to_ident x in
    let old_i := fresh i "_0" in
    lazymatch is_decl with
    | true => idtac
    | false => rename i into old_i
    end;
    pose (i := v);
    lazymatch goal with
    | |- wp_cmd ?call ?c ?t ?m (map.put ?l ?x ?v) ?post => change
        (wp_cmd  call  c  t  m (map.put  l  x  i)  post)
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

Ltac map_with_ltac f l :=
  lazymatch l with
  | ?h :: ?t =>
    let t' := map_with_ltac f t in
    let h' := f h in constr:(h' :: t')
  | nil => open_constr:(@nil _)
  end.

Ltac eval_expr_step :=
  lazymatch goal with
  | |- wp_expr _ _ (expr.load access_size.word _) _ => eapply wp_load_word
  (* once the address of a load, or the address and value of a store have been evaluated,
     the goal will have two existentials: *)
  | |- exists (v: @word.rep _ _) (R: @map.rep _ _ _ -> Prop), seps _ _ => do 2 eexists
  (* loads, stores and function calls all can lead to sep goals like this: *)
  | |- seps _ _ => ecancel_assumption_with_remaining_emp_Prop
  | |- wp_expr _ _ (expr.load _ _) _ => eapply wp_load_old
  | |- wp_expr _ _ (expr.var _) _ => eapply wp_var; [ reflexivity |]
  | |- wp_expr _ _ (expr.literal _) _ => eapply wp_literal
  | |- wp_expr _ _ (expr.op _ _ _) _ => eapply wp_op; cbv [interp_binop]
  end.

Ltac eval_dexpr_step :=
  lazymatch goal with
  | |- dexpr_bool_prop _ _ (expr.lazy_and _ _) _ =>
      eapply dexpr_lazy_and; [|intro]
  | |- dexpr_bool_prop _ _ (expr.op _ _ _) _ =>
      eapply dexpr_bool_op_prop_unf
  | |- dexpr _ _ (expr.var _) _ => eapply dexpr_var; reflexivity
  | |- dexpr _ _ (expr.literal _) _ => eapply dexpr_literal
  end.

Ltac start :=
  let eargnames := open_constr:(_: list string) in
  refine (existT _ (eargnames, _, _) _);
  let call := fresh "call" in
  intro call;
  let n := fresh "Scope0" in pose proof (mk_scope_marker FunctionBody) as n;
  intros;
  (* since the arguments will get renamed, it is useful to have a list of their
     names, so that we can always see their current renamed names *)
  let arguments := fresh "arguments" in
  lazymatch goal with
  | |- vc_func ?call ?f ?t ?m ?argvalues ?post =>
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
    split; [reflexivity|]
  end.

(* Note: contrary to add_last_var_to_post, this one makes Post a goal rather
   than a hypothesis, because if it was a hypothesis, it wouldn't be possible
   to clear vars *)
Ltac add_last_hyp_to_post :=
  let last_hyp := match goal with H: _ |- _ => H end in
  let T := type of last_hyp in
  lazymatch T with
  | scope_marker _ => fail "done (scope marker reached)"
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
  | |- ?E ?T ?M ?L =>
      add_equality_to_post L Post;
      add_equality_to_post T Post;
      (* only add equality for memory if it was not changed in the branch and therefore
         does not have a sep log assertion that will be packaged *)
      try (is_in_post_evar_scope M; add_equality_to_post M Post)
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
         | |- _ lastvar _ _ => move lastvar at top
         | |- _ _ lastvar _ => move lastvar at top
         | |- _ _ _ lastvar => move lastvar at top
         | |- _ => add_var_to_post lastvar Post
         end
  end.

Ltac package_context :=
  let Post := fresh "Post" in
  eassert _ as Post by (repeat add_last_hyp_to_post; apply ands_nil);
  add_equalities_to_post Post;
  repeat add_last_var_to_post Post;
  lazymatch goal with
  | |- _ ?T ?M ?L => pattern T, M, L in Post
  end;
  exact Post.

Inductive snippet :=
| SAssign(is_decl: bool)(x: string)(e: Syntax.expr)
| SStore(sz: access_size)(addr val: Syntax.expr)
| SIf(cond: Syntax.expr)
| SElse
| SEnd
| SRet(xs: list string)
| SEmpty.

Ltac assign is_decl name val :=
  eapply (wp_set _ name val);
  repeat eval_expr_step;
  [.. (* maybe some unsolved side conditions *)
  | try (put_into_current_locals is_decl; repeat simpli_step) ].

(* TODO change order of definitions so that this hook is not needed any more *)
Ltac transfer_sep_order := fail "not yet implemented".

Ltac store sz addr val :=
  eapply (wp_store _ addr val);
  repeat eval_expr_step;
  [.. (* maybe some unsolved side conditions *)
  | lazymatch goal with
    | |- forall (_: @map.rep _ _ _), seps _ _ -> _ =>
        intros; transfer_sep_order; repeat simpli_step
    | |- _ => idtac (* expression evaluation did not work fully automatically *)
    end ].

Ltac destruct_locals tup names :=
  lazymatch names with
  | ?s :: ?rest => let name := string_to_ident s in
                   make_fresh name; destruct tup as (name & tup); destruct_locals tup rest
  | nil => destruct tup (* becomes tt *)
  end.

Ltac cond c :=
  lazymatch goal with
  | |- wp_cmd ?call _ ?t ?m (reconstruct ?vars ?vals) _ =>
    eapply (wp_if_bool_dexpr call c vars vals);
    [ repeat eval_dexpr_step
    | let b := fresh "Scope0" in pose proof (mk_scope_marker ThenBranch) as b; intro
    | let b := fresh "Scope0" in pose proof (mk_scope_marker ElseBranch) as b; intro
    | intros;
      lazymatch goal with
      | |- wp_cmd _ _ _ _ (reconstruct ?names ?tup) _ => destruct_locals tup names
      end ]
  end.

Ltac els :=
  assert_scope_kind ThenBranch;
  eapply wp_skip;
  eexists; split; [ reflexivity | ];
  package_context.

(*
  lazymatch goal with
  | b := (cons ThenBranch ?l) : list block_kind |- _ => clear b
  | _ => fail "Not in a then-branch"
  end;
  eapply wp_skip;
  eexists; split;
  [ lazymatch goal with
    | cl := current_locals_marker (reconstruct ?vars ?vals) |- _ =>
      cbv [cl current_locals_marker]; reflexivity
    end
  | ].
*)

Ltac close_block :=
  lazymatch goal with
  | B: scope_marker ?sk |- _ =>
      lazymatch sk with
      | ElseBranch =>
          eapply wp_skip;
          eexists; split; [ reflexivity | ];
          package_context
      | LoopBody => fail "Closing a loop body is not yet implemented"
      | _ => fail "Can't end a block here"
      end
  | _ => fail "no scope marker found"
  end.

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
    eexists; split; [reflexivity|]
  end.

Ltac prettify_goal :=
  cbv beta in *;
  fwd.

Ltac add_snippet s :=
  lazymatch s with
  | SAssign ?is_decl ?y ?e => assign is_decl y e
  | SStore ?sz ?addr ?val => store sz addr val
  | SIf ?e => cond e
  | SElse => els
  | SEnd => close_block
  | SRet ?retnames => ret retnames
  | SEmpty => prettify_goal
  end.

Ltac after_snippet :=
  cbn [PrimitivePair.pair._1 PrimitivePair.pair._2].

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
Notation "a <= b" := (live_expr:(!(b < a)))
  (in custom live_expr at level 6, a custom live_expr, b custom live_expr,
   no associativity, only parsing).
Notation "a > b" := (live_expr:(b < a))
  (in custom live_expr at level 6, a custom live_expr, b custom live_expr,
   no associativity, only parsing).
Notation "a >= b" := (live_expr:(b <= a))
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
Infix "&&&" := (expr.op bopname.eager_and)
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

Declare Custom Entry snippet.

Notation "*/ s /*" := s (s custom snippet at level 100).
Notation "*/ /*" := SEmpty.
Notation "x = e ;" := (SAssign false x e) (* rhs as in "already declared" (but still on lhs) *)
  (in custom snippet at level 0, x custom rhs_var at level 100, e custom live_expr at level 100).
Notation "'uintptr_t' x = e ;" := (SAssign true x e)
  (in custom snippet at level 0, x custom lhs_var at level 100, e custom live_expr at level 100).
Notation "store( a , v ) ;" := (SStore access_size.word a v)
  (in custom snippet at level 0, a custom live_expr at level 100, v custom live_expr at level 100).
Notation "'return' l ;" := (SRet l)
  (in custom snippet at level 0, l custom rhs_var_list at level 1).

Notation "'if' ( e ) {" := (SIf e) (in custom snippet at level 0, e custom live_expr).
Notation "}" := SEnd (in custom snippet at level 0).
Notation "} 'else' {" := SElse (in custom snippet at level 0).

Tactic Notation "#" constr(s) := add_snippet s; after_snippet.

Set Ltac Backtrace.

Require Import Coq.Sorting.Permutation Coq.Sorting.Sorting.

Module FstNatOrder <: Orders.TotalLeBool.
  Definition t: Type := nat * nat.
  Definition leb: t -> t -> bool :=
    fun '(x, _) '(y, _) => Nat.leb x y.
  Theorem leb_total: forall a1 a2, leb a1 a2 = true \/ leb a2 a1 = true.
  Proof.
    unfold leb. intros [x _] [y _]. destr (x <=? y)%nat. 1: auto.
    right. apply Nat.leb_le. unfold lt in E. eapply Nat.le_trans. 2: exact E.
    do 2 constructor.
  Qed.
End FstNatOrder.

Module FstNatSorting := Sort FstNatOrder.

Lemma iff1_refl{A: Type}(P: A -> Prop): iff1 P P. Proof. reflexivity. Qed.
Lemma iff1_sym{A: Type}{P Q: A -> Prop}: iff1 P Q -> iff1 Q P.
Proof. intros. symmetry. assumption. Qed.

Ltac iff1_syntactic_reflexivity :=
  lazymatch goal with
  | |- iff1 ?x ?y => first [is_evar x | is_evar y | constr_eq x y]
  end;
  exact (iff1_refl _).

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

Load LiveVerif.
Import SepLogPredsWithAddrLast.
Import MySepNotations.
(* to re-override Notations loaded trough `Load LiveVerif/bedrock2.Map.SeparationLogic` *)

(* Note: If you re-import ZnWords after this, you'll get the old better_lia again *)
Ltac better_lia ::=
  Z.div_mod_to_equations;
  adhoc_lia_performance_fixes;
  Lia.lia.

Local Set Default Goal Selector "1".

Lemma seps'_Permutation: forall (l1 l2: list (mem -> Prop)),
    Permutation l1 l2 -> iff1 (seps' l1) (seps' l2).
Proof.
  induction 1.
  - reflexivity.
  - simpl. rewrite IHPermutation. reflexivity.
  - simpl. cancel.
  - etransitivity; eassumption.
Qed.

Lemma seps_Permutation: forall (l1 l2: list (mem -> Prop)),
    Permutation l1 l2 -> iff1 (seps l1) (seps l2).
Proof.
  intros.
  etransitivity. 2: eapply seps'_iff1_seps.
  etransitivity. 2: eapply seps'_Permutation; exact H.
  symmetry. eapply seps'_iff1_seps.
Qed.

Fixpoint zip_with_counter{A: Type}(l: list A)(start: nat): list (A * nat) :=
  match l with
  | nil => nil
  | x :: xs => (x, start) :: zip_with_counter xs (S start)
  end.

Definition zip_with_index{A: Type}(l: list A): list (A * nat) := zip_with_counter l 0.

Lemma snd_zip_with_counter: forall {A: Type} (l: list A) (start: nat),
    List.map snd (zip_with_counter l start) = List.seq start (List.length l).
Proof. induction l; simpl; intros. 1: reflexivity. f_equal. apply IHl. Qed.

Lemma snd_zip_with_index: forall {A: Type} (l: list A),
    List.map snd (zip_with_index l) = List.seq 0 (List.length l).
Proof. intros. apply snd_zip_with_counter. Qed.

Lemma List__map_nth_seq_self{A: Type}(d: A)(l: list A):
  List.map (fun i => List.nth i l d) (List.seq 0 (List.length l)) = l.
Proof.
  induction l; cbn -[List.nth]. 1: reflexivity.
  unfold List.nth at 1.
  f_equal.
  etransitivity. 2: exact IHl.
  rewrite <- List.seq_shift.
  rewrite List.map_map.
  reflexivity.
Qed.

(* redefinitions so that cbv on it does not cbv user-defined terms *)
Definition my_list_map{A B: Type}(f: A -> B): list A -> list B :=
  Eval unfold List.map in (List.map f).
Definition my_list_nth{A: Type}: nat -> list A -> A -> A :=
  Eval unfold List.nth in (@List.nth A).

Definition apply_permutation_with_default(p: list nat){A: Type}(l: list A)(d: A): list A :=
  my_list_map (fun i => my_list_nth i l d) p.

Definition apply_permutation(p: list nat){A: Type}(l: list A): list A :=
  match l with
  | nil => nil
  | cons d _ => apply_permutation_with_default p l d
  end.

Lemma apply_permutation_with_default_is_Permutation: forall (p: list nat) A (l: list A) d,
    Permutation p (List.seq 0 (List.length l)) ->
    Permutation l (apply_permutation_with_default p l d).
Proof.
  unfold apply_permutation_with_default. intros.
  eapply Permutation_trans. 2: {
    eapply Permutation_map.
    eapply Permutation_sym.
    exact H.
  }
  rewrite List__map_nth_seq_self.
  apply Permutation_refl.
Qed.

Lemma apply_permutation_is_Permutation: forall (p: list nat) (A: Type) (l: list A),
    Permutation p (List.seq 0 (List.length l)) ->
    Permutation l (apply_permutation p l).
Proof.
  intros. unfold apply_permutation. destruct l.
  - apply Permutation_refl.
  - apply apply_permutation_with_default_is_Permutation. assumption.
Qed.

Definition order_to_permutation(order: list nat): list nat :=
  List.map snd (FstNatSorting.sort (zip_with_index order)).

Lemma order_to_permutation_is_Permutation(order: list nat):
    Permutation (order_to_permutation order) (List.seq 0 (List.length order)).
Proof.
  unfold order_to_permutation.
  eapply Permutation_trans. {
    eapply Permutation_map.
    eapply Permutation_sym.
    eapply FstNatSorting.Permuted_sort.
  }
  rewrite snd_zip_with_index.
  eapply Permutation_refl.
Qed.

(* `order` and `l` must have the same length.
    The i-th element of `order` is the sort key of the i-th element of `l`.
    Returns `l` sorted according to these sort keys. *)
Definition reorder(order: list nat){A: Type}(l: list A): list A :=
  apply_permutation (order_to_permutation order) l.

Lemma reorder_is_iff1: forall (order: list nat) (l: list (mem -> Prop)),
    List.length order = List.length l ->
    iff1 (seps l) (seps (reorder order l)).
Proof.
  intros.
  apply seps_Permutation.
  unfold reorder.
  apply apply_permutation_is_Permutation.
  rewrite <- H.
  apply order_to_permutation_is_Permutation.
Qed.

(* for lists with concrete structure/length, but elements that should not be cbv'd *)
Ltac list_length l :=
  lazymatch l with
  | nil => constr:(O)
  | cons _ ?tail => let r := list_length tail in constr:(S r)
  end.

Ltac clause_index clause clauses start_index default_index :=
  lazymatch clauses with
  | cons (at_addr ?a _) ?tail =>
    lazymatch clause with
    | at_addr a _ => constr:(start_index)
    | _ => clause_index clause tail (S start_index) default_index
    end
  | cons clause _ => constr:(start_index)
  | cons _ ?tail => clause_index clause tail (S start_index) default_index
  | nil => constr:(default_index)
  end.

Ltac get_order_rec old_clauses new_clauses default_index :=
  lazymatch new_clauses with
  | nil => constr:(@nil nat)
  | cons ?clause ?tail =>
    let priority := clause_index clause old_clauses 0%nat default_index in
    let rest := get_order_rec old_clauses tail priority in
    constr:(priority :: rest)
  end.

Ltac get_order old_clauses new_clauses :=
  (* if the first clause is not found in old_clauses, we put it at the end;
     if a non-first clause is not found, we put it after the clause that's
     to the left of it in new_clauses, so we give it the same priority value,
     so the returned order might have duplicate priority values, and we rely
     on mergesort being stable to keep the order between clauses of the same priority *)
  let n := list_length old_clauses in
  get_order_rec old_clauses new_clauses n.

(* Given an old and a new sep hyp, transfers the order of the sepclauses from the old one
   to the new one (and first also removes nested seps in the new sep hyp) *)
Ltac transfer_sep_order ::=
  lazymatch goal with
  | HOld: seps ?old_clauses ?mOld, HNew: seps ?new_nested ?mNew |- wp_cmd _ _ _ ?mNew _ _ =>
    let tmem := type of mNew in
    let E := fresh "E" in
    eassert (@iff1 tmem (seps new_nested) _) as E;
    [ (* first equivalence step: from `seps new_nested` to `Tree.to_sep tree` *)
      let stars := eval cbn[seps] in (seps new_nested) in
      let tree := reify stars in
      transitivity (Tree.to_sep tree); [
        cbn [seps Tree.to_sep Tree.interp]; iff1_syntactic_reflexivity
      |];
      (* second equivalence step: from `Tree.to_sep tree` to `seps (Tree.flatten tree)` *)
      transitivity (seps (Tree.flatten tree)); [
        exact (iff1_sym (Tree.flatten_iff1_to_sep tree))
      |];
      (* third equivalence step: from `seps (Tree.flatten tree)` to `seps new_clauses` *)
      etransitivity; [
        cbn [SeparationLogic.Tree.flatten SeparationLogic.Tree.interp SeparationLogic.app];
        iff1_syntactic_reflexivity
      |];
      let new_clauses := lazymatch goal with |- iff1 (seps ?C) _ => C end in
      (* fourth equivalence step: from `seps new_clauses` to `seps (reorder order new_clauses)` *)
      let order := get_order old_clauses new_clauses in
      etransitivity; [
        eapply (reorder_is_iff1 order new_clauses); reflexivity
      |];
      (* fifth equivalence step: from `seps (reorder order new_clauses)` to cbv'd version of it *)
      cbv [reorder];
      let r := eval vm_compute in (order_to_permutation order) in
          change (order_to_permutation order) with r;
      cbv [apply_permutation apply_permutation_with_default my_list_map my_list_nth];
      reflexivity
    | let HNewNew := fresh in pose proof (proj1 (E mNew) HNew) as HNewNew;
      clear E HOld HNew;
      try clear mOld;
      make_fresh mOld;
      rename HNewNew into HOld, mNew into mOld ]
  end.

Lemma reordering_test: forall addr1 addr2 addr3 addr4 v1_old v1_new v2 v3 v4 R (m m': mem)
                              call t l c post,
    seps [addr1 |-> scalar v1_old; addr2 |-> scalar v2; addr3 |-> scalar v3; R] m ->
    (* value at addr1 was updated, addr2 was consumed, addr4 was added, and order was changed: *)
    seps [R; addr3 |-> scalar v3; addr4 |-> scalar v4; addr1 |-> scalar v1_new] m' ->
    (* desired order:
    seps [addr1 |-> scalar v1_new; addr3 |-> scalar v3; addr4 |-> scalar v4; R] m1 *)
    True ->
    wp_cmd call c t m' l post.
Proof.
  intros *. intros M M2 ExtraHyp.
          (* 0                        1                    2                    3
  M  : seps [addr1 |-> scalar v1_old; addr2 |-> scalar v2; addr3 |-> scalar v3; R] m0
  M2 : seps [R; addr3 |-> scalar v3; addr4 |-> scalar v4; addr1 |-> scalar v1_new] m1
  order :=  [3; 2;                   2;                   0                      ] *)
  transfer_sep_order.
  lazymatch type of M with
  | seps [addr1 |-> scalar v1_new; addr3 |-> scalar v3; addr4 |-> scalar v4; R] m => idtac
  end.
Abort.

Tactic Notation ".*" constr(s) "*" := add_snippet s; after_snippet.

Section Merging.
  Lemma if_dlet_l: forall (b: bool) (T: Type) (rhs: T) (body: T -> Prop) (P: Prop),
      (if b then dlet rhs (fun binder => body binder) else P) ->
      dlet rhs (fun binder => if b then body binder else P).
  Proof. unfold dlet. intros. assumption. Qed.

  Lemma if_ands_same_head: forall (b: bool) (P: Prop) (Qs1 Qs2: list Prop),
      (if b then ands (P :: Qs1) else ands (P :: Qs2)) ->
      P /\ (if b then ands Qs1 else ands Qs2).
  Proof. cbn. intros. destruct b; intuition idtac. Qed.

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
    intros. eapply merge_ands_at_indices in H1; [|eassumption..].
    destruct b; assumption.
  Qed.

  Lemma merge_ands_at_indices_same: forall i j (P: Prop) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = P ->
      nth j Ps2 = P ->
      (if b then ands Ps1 else ands Ps2) ->
      P /\ (if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2)).
  Proof.
    intros. eapply merge_ands_at_indices in H1; [|eassumption..].
    destruct b; assumption.
  Qed.
End Merging.

Ltac find_eq_by_lhs lhs Ps :=
  lazymatch Ps with
  | ?h :: ?t => lazymatch h with
                | lhs = _ => constr:((0%nat, h))
                | _ => lazymatch find_eq_by_lhs lhs t with
                       | (?i, ?P) => constr:((S i, P))
                       end
                end
  end.

Ltac merge_pair_with_same_lhs :=
  lazymatch goal with
  | H: if _ then ands ?Ps else ands ?Qs |- _ => once (
      lazymatch index_and_element_of Ps with
      | (?i, ?P) =>
          lazymatch P with
          | ?lhs = ?rhs1 =>
              lazymatch find_eq_by_lhs lhs Qs with
              | (?j, lhs = ?rhs2) =>
                  eapply (@merge_ands_at_indices_same_lhs i j _ lhs rhs1 rhs2) in H;
                  [  cbn [app firstn tl skipn] in H; destruct H
                  | cbn [hd skipn]; reflexivity .. ]
              end
          end
      end)
  end.

Definition u_min: {f: list string * list string * cmd &
  forall call t m a b,
    vc_func call f t m [a; b] (fun t' m' retvs =>
      t' = t /\ m' = m /\
      (word.unsigned a <  word.unsigned b /\ retvs = [a] \/
       word.unsigned b <= word.unsigned a /\ retvs = [b])
  )}.
(**)  start.                                                                    (**)
.**/  uintptr_t r = 0;                                                          /**.
.**/  if (a < b) {                                                              /**.
.**/    r = a;                                                                  /**.
.**/  } else {                                                                  /**.
.**/    r = b;                                                                  /**.
.**/  }                                                                         /**.
.**/                                                                            /**.

  repeat merge_pair_with_same_lhs.

.**/  return r; /**.
destruct cond0; intuition (blia || idtac).
{
(**)  admit.                                                                    (**)
Abort.

Definition u_min: {f: list string * list string * cmd &
  forall call t m a b,
    vc_func call f t m [a; b] (fun t' m' retvs =>
      t' = t /\ m' = m /\
      (word.unsigned a <  word.unsigned b /\ retvs = [a] \/
       word.unsigned b <= word.unsigned a /\ retvs = [b])
  )}. .**/
  /**. start.                                                                   .**/
  uintptr_t r = 0;                                                         /**. .**/
  if (a < b) {                                                             /**. .**/
    r = a;                                                                 /**. .**/
  } else {                                                                 /**. .**/
    r = b;                                                                 /**. .**/
  }                                                                        /**. .**/
  /**.
Abort.

Definition u_min: {f: list string * list string * cmd &
  forall call t m a b,
    vc_func call f t m [a; b] (fun t' m' retvs =>
      t' = t /\ m' = m /\
      (word.unsigned a <  word.unsigned b /\ retvs = [a] \/
       word.unsigned b <= word.unsigned a /\ retvs = [b])
  )}.
      start.
.**/  uintptr_t r = 0;                                                          /**.
.**/  if (a < b) {                                                              /**.
.**/    r = a;                                                                  /**.
.**/  } else {                                                                  /**.
.**/    r = b;                                                                  /**.
.**/  }                                                                         /**.
Abort.

Definition u_min: {f: list string * list string * cmd &
  forall call t m a b,
    vc_func call f t m [a; b] (fun t' m' retvs =>
      t' = t /\ m' = m /\
      (word.unsigned a <  word.unsigned b /\ retvs = [a] \/
       word.unsigned b <= word.unsigned a /\ retvs = [b])
  )}. .**/
  /**. start. .**/                                                         /**. .**/
  uintptr_t r = 0;                                                         /**. .**/
  if (a < b) {                                                             /**. .**/
    r = a;                                                                 /**. .**/
  } else {                                                                 /**. .**/
    r = b;                                                                 /**. .**/
  }                                                                        /**. .**/
  /**.
Abort.

Definition sort3: {f: list string * list string * cmd &
  forall call t m a vs R,
    m satisfies <{
      * a |-> word_array vs
      * R
    }> /\
    List.length vs = 3%nat ->
    vc_func call f t m [a] (fun t' m' retvs =>
      exists v0 v1 v2,
        t' = t /\
        Permutation vs [v0; v1; v2] /\
        \[v0] <= \[v1] <= \[v2] /\
        m satisfies <{
          * a |-> word_array [v0; v1; v2]
          * R
        }>
  )}.
      start. destruct H as [M ?].
.**/  uintptr_t w0 = load(a);                                                   /**.
.**/  uintptr_t w1 = load(a+4);                                                 /**.
(*
Ltac assign is_decl name val ::=
  eapply (wp_set _ name val).
(*
  repeat eval_expr_step;
  [.. (* maybe some unsolved side conditions *)
  | try (put_into_current_locals is_decl; repeat simpli_step) ].
*)

.**/  uintptr_t w2 = load(a+8);                                                 /**.
eval_expr_step.
eval_expr_step.
eval_expr_step.
eval_expr_step.
eval_expr_step.
*)

.**/  uintptr_t w2 = load(a+8);                                                 /**.

(* adding more rewrite hints is costly:
Ltac fwd_rewrites ::= fail.
.**/  if (w1 < w0) {                                                 /**.
Ltac fwd_rewrites ::= fwd_rewrites_autorewrite.
(* Time rewrite @word.unsigned_ltu in * by typeclasses eauto. (* fast *) *)
(*  Time autorewrite with fwd_rewrites in *. (* 0.372 secs *)*)

Hint Rewrite @word.unsigned_ltu using typeclasses eauto: foo_test.
Time autorewrite with foo_test in *.
Print Rewrite HintDb foo_test.
Print Rewrite HintDb fwd_rewrites.
*)

.**/  if (w1 < w0 && w1 < w2) {                                                 /**.
.**/    store(a, w1);                                                           /**.
.**/    w1 = w0;                                                                /**.
  assert (exists foo, foo + foo = 2) as Foo. {
    exists 1. reflexivity.
  }
  destruct Foo as (foo & Foo).

  move m at bottom.
  move w1 at bottom.

  assert (exists bar: nat, (bar + bar = 4 * Z.to_nat foo)%nat) as Bar. {
    exists 2%nat. blia.
  }
  destruct Bar as (bar & Bar).
  set (baz := foo + foo).
  assert (w1 ^+ w0 ^+ word.of_Z baz = word.of_Z baz ^+ w1 ^+ w1) as E by ZnWords.
  rename w1 into w1tmp.
  pose (w1 := w0 ^+ word.of_Z baz ^- word.of_Z baz).
  move w1 after w1tmp.
  replace w1tmp with w1 in * by ZnWords. clear w1tmp.




  (* else branch: *)
.**/   if (w2 < w0 && w2 < w1) {                                                /**.
.**/     store(a, w2);                                                          /**.
.**/     w2 = w0;                                                               /**.
(*
Close Scope live_scope. Undelimit Scope live_scope. idtac.

.**/  }                                                                         /**.
.**/  if (w2 < w1) {                                                            /**.
.**/    store(a+4, w2);                                                         /**.
.**/    store(a+8, w1);                                                         /**.
.**/  } else {                                                                  /**.
.**/    store(a+4, w1);                                                         /**.
.**/    store(a+8, w2);                                                         /**.
.**/  }                                                                         /**.
*)
Abort.

(* TODO: write down postcondition only at end *)
Definition swap_locals: {f: list string * list string * cmd &
  forall call tr m a b,
    vc_func call f tr m [a; b] (fun tr' m' retvs =>
      tr' = tr /\ m' = m /\ retvs = [b; a]
  )}.
    (* note: we could just return ["b", "a"] and then the body would be just skip *)
    start. .**/
  uintptr_t t = a;                                                         /**. .**/
  a = b;                                                                   /**. .**/
  b = t;                                                                   /**. .**/
  uintptr_t res1 = a;                                                      /**. .**/
  uintptr_t res2 = b;                                                      /**. .**/
  return res1, res2;                                                       /**. .**/
/**.
  intuition congruence.
Defined.

(* TODO: write down postcondition only at end *)
Definition swap: {f: list string * list string * cmd &
  forall call t m a_addr b_addr a b R,
    m satisfies <{
      * a_addr |-> scalar a
      * b_addr |-> scalar b
      * R
    }> ->
    vc_func call f t m [a_addr; b_addr] (fun t' m' retvs =>
      m' satisfies <{
        * a_addr |-> scalar b
        * b_addr |-> scalar a
        * R
      }> /\ retvs = [] /\ t' = t
  )}.
    start.
#*/ uintptr_t t = load(a_addr);                                              /*.
#*/ store(a_addr, load(b_addr));                                             /*.
#*/ store(b_addr, t);                                                        /*.
    ret (@nil string).
    subst. intuition solve[cbn[seps] in *; ecancel_assumption].
Defined.

Goal False.
  let r := eval unfold swap_locals in
  match swap_locals with
  | existT _ f _ => f
  end in pose r.
Abort.

Definition foo(a b: word): word := a ^+ b.

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
