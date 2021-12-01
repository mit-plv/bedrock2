(* begin move *)

Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Z.Lia.
Require Import coqutil.Byte coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Tactics.letexists coqutil.Tactics.Tactics coqutil.Tactics.rewr coqutil.Tactics.rdelta.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.fwd.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.WeakestPrecondition bedrock2.ProgramLogic bedrock2.Loops.
Require Import coqutil.Word.Bitwidth32.
Require Import Coq.Strings.String.
Require Import bedrock2Examples.LiveVerif.string_to_ident.
Require Import bedrock2Examples.LiveVerif.ident_to_string.
Import List.ListNotations. Local Open Scope list_scope.

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
End __. End SepLogPredsWithAddrLast.

(* Note: This notation is *not* intended to be used together with a `*` that means `sep`,
   but with a `*` that means `word.mul`, so that we can write `addr + 4 * offs |-> element`,
   so `*` and `+` need to bind stronger than `|->`.
   Given that `+` is at level 50 and `*` is at level 40, we choose level 55: *)
Notation "addr |-> clause" := (at_addr addr clause) (at level 55).

Section WithParams.
  Import bedrock2.Syntax.
  Context {word: word.word 32} {mem: map.map word byte} {locals: map.map string word}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {locals_ok: map.ok locals}.
  Context {ext_spec: ExtSpec}.

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

  Lemma weaken_wp_expr: forall m l e (post1 post2: word -> Prop),
      wp_expr m l e post1 ->
      (forall v, post1 v -> post2 v) ->
      wp_expr m l e post2.
  Proof.
    intros. constructor. inversion H.
    eapply WeakestPreconditionProperties.Proper_expr; eassumption.
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

  Lemma wp_store: forall call sz ea ev t m l rest post,
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

  Definition current_locals_marker(l: locals): locals := l.
  Definition arguments_marker(args: list word): list word := args.

End WithParams.

Declare Scope live_scope.
Delimit Scope live_scope with live.
Local Open Scope live_scope.

Inductive ignore_above_this_line := mk_ignore_above_this_line.
Notation "'ignore' 'above' 'this' 'line' : '____'" := ignore_above_this_line
  (only printing) : live_scope.

Notation "'ready' 'for' 'next' 'command'" := (wp_cmd _ _ _ _ _ _)
  (at level 0, only printing) : live_scope.

Declare Scope reconstruct_locals_scope.
Delimit Scope reconstruct_locals_scope with reconstruct_locals.

Notation "[ x ]" := (PrimitivePair.pair.mk x tt)
  (only printing) : reconstruct_locals_scope.
Notation "[ x ; y ; .. ; z ]" :=
  (PrimitivePair.pair.mk x (PrimitivePair.pair.mk y .. (PrimitivePair.pair.mk z tt) ..))
  (only printing) : reconstruct_locals_scope.

Notation "l" := (current_locals_marker (reconstruct _ l%reconstruct_locals))
  (at level 100, only printing) : live_scope.
Notation "l" := (arguments_marker l)
  (at level 100, only printing) : live_scope.

(* intro-and-position *)
Ltac intro_p n :=
  lazymatch goal with
  | separator: ignore_above_this_line |- forall _: @word.rep _ _, _ =>
    intro n; move n after separator (* after-wrt-moving-direction = above *)
  | |- forall _: _, _ => intro n
  end.

Ltac intro_p_autonamed :=
  lazymatch goal with
  | |- forall x: ?T, _ => let n := fresh x in intro_p n
  end.

Ltac intros_p := repeat intro_p_autonamed.

Ltac make_fresh x :=
  tryif is_var x then let x' := fresh x "0" in rename x into x' else idtac.

Ltac put_into_current_locals :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.put ?l ?x ?v) _ =>
    let i := string_to_ident x in
    make_fresh i;
    let n := fresh "L0" in
    apply wp_locals_put; intro_p i; intro_p n
  end;
  lazymatch goal with
  | cl := current_locals_marker (reconstruct _ _) |- _ =>
    subst cl;
    lazymatch goal with
    | |- wp_cmd ?call ?c ?t ?m ?l ?post =>
      let keys := eval vm_compute in (map.keys l) in
      let values := eval vm_compute in (map.getmany_of_list l keys) in
      let values := lazymatch values with Some ?values => values end in
      let values := eval vm_compute in (tuple.of_list values) in
      change (let cl := current_locals_marker (reconstruct keys values) in
              wp_cmd call c t m cl post);
      intro cl;
      lazymatch goal with
      | arguments := arguments_marker _ |- _ =>
        move cl before arguments (* before-wrt-moving-direction = below *)
      end
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
  match goal with
  | |- wp_expr _ _ (expr.load access_size.word _) _ => eapply wp_load_word
  | |- wp_expr _ _ (expr.load _ _) _ => eapply wp_load_old
  | |- wp_expr _ _ (expr.var _) _ => eapply wp_var; [ reflexivity |]
  end.

Ltac start :=
  let eargnames := open_constr:(_: list string) in
  refine (existT _ (eargnames, _, _) _);
  let call := fresh "call" in
  intro call;
  let n := fresh "____" in pose proof mk_ignore_above_this_line as n;
  intros_p;
  (* since the arguments will get renamed, it is useful to have a list of their
     names, so that we can always see their current renamed names *)
  lazymatch goal with
  | |- vc_func ?call ?f ?t ?m ?argvalues ?post =>
    let arguments := fresh "arguments" in pose (arguments_marker argvalues) as arguments;
    let argnames := map_with_ltac varconstr_to_string argvalues in
    unify eargnames argnames
  end;
  unfold vc_func;
  lazymatch goal with
  | |- exists l, map.of_list_zip ?keys ?values = Some l /\ _ =>
    let values := eval vm_compute in (tuple.of_list values) in
    let cl := fresh "current_locals" in
    refine (let cl := current_locals_marker (reconstruct keys values) in ex_intro _ cl _);
    split; [reflexivity|]
  end;
  lazymatch goal with
  | separator: ignore_above_this_line |- wp_cmd _ _ ?t ?m _ _ =>
    move t after separator; let tn := fresh "current_trace" in rename t into tn;
    move m after separator; let mn := fresh "current_mem" in rename m into mn
  end.

Inductive snippet :=
| SAssign(x: string)(e: Syntax.expr)
| SStore(sz: access_size)(addr val: Syntax.expr)
| SRet(xs: list string)
(*
| SIf(cond: Syntax.expr)(merge: bool)
| SEnd
| SElse
*).

Ltac assign name val :=
  eapply (wp_set _ name val);
  repeat eval_expr_step;
  [.. (* maybe some unsolved side conditions *) | try put_into_current_locals].

Ltac store sz addr val :=
  eapply (wp_store _ sz addr val);
  repeat eval_expr_step.

Ltac ret retnames :=
  eapply wp_skip;
  lazymatch goal with
  | |- exists _, map.getmany_of_list _ ?eretnames = Some _ /\ _ =>
    unify eretnames retnames;
    eexists; split; [reflexivity|]
  end.

Ltac add_snippet s :=
  lazymatch s with
  | SAssign ?y ?e => assign y e
  | SStore ?sz ?addr ?val => store sz addr val
  | SRet ?retnames => ret retnames
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

Notation "x" := (expr.var x)
  (in custom live_expr at level 0, x custom rhs_var at level 0, only parsing).

Notation "load1( a )" := (expr.load access_size.one a)
  (in custom live_expr at level 0, a custom live_expr at level 100, only parsing).
Notation "load2( a )" := (expr.load access_size.two a)
  (in custom live_expr at level 0, a custom live_expr at level 100, only parsing).
Notation "load4( a )" := (expr.load access_size.four a)
  (in custom live_expr at level 0, a custom live_expr at level 100, only parsing).
Notation  "load( a )" := (expr.load access_size.word a)
  (in custom live_expr at level 0, a custom live_expr at level 100, only parsing).

Notation "live_expr:( e )" := e
  (e custom live_expr at level 100, only parsing).

Declare Custom Entry snippet.

Notation "*/ s /*" := s (s custom snippet at level 100).
Notation "x = e ;" := (SAssign x e)
  (in custom snippet at level 0, x custom lhs_var at level 100, e custom live_expr at level 100).
Notation "store( a , v ) ;" := (SStore access_size.word a v)
  (in custom snippet at level 0, a custom live_expr at level 100, v custom live_expr at level 100).
Notation "'return' l ;" := (SRet l)
  (in custom snippet at level 0, l custom rhs_var_list at level 1).

(*
Notation "'if' ( e ) '/*merge*/' {" := (SIf e true) (in custom snippet at level 0, e custom bedrock_expr).
Notation "'if' ( e ) '/*split*/' {" := (SIf e false) (in custom snippet at level 0, e custom bedrock_expr).
Notation "}" := SEnd (in custom snippet at level 0).
Notation "'else' {" := SElse (in custom snippet at level 0).
*)

Tactic Notation "#" constr(s) := add_snippet s; after_snippet.

Set Ltac Backtrace.

(* end move *)


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


Load LiveVerif.
Import SepLogPredsWithAddrLast.

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

Definition apply_permutation_with_default(p: list nat){A: Type}(l: list A)(d: A): list A :=
  List.map (fun i => List.nth i l d) p.

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

Lemma reordering_test: forall addr1 addr2 addr3 addr4 v1_old v1_new v2 v3 v4 R (m0 m1: mem),
    seps [addr1 |-> scalar v1_old; addr2 |-> scalar v2; addr3 |-> scalar v3; R] m0 ->
    (* value at addr1 was updated, addr2 was consumed, addr4 was added, and order was changed: *)
    seps [R; addr3 |-> scalar v3; addr4 |-> scalar v4; addr1 |-> scalar v1_new] m1 ->
    (* desired order: *)
    seps [addr1 |-> scalar v1_new; addr3 |-> scalar v3; addr4 |-> scalar v4; R] m1.
Proof.
  intros. (* 0                        1                    2                    3
  H  : seps [addr1 |-> scalar v1_old; addr2 |-> scalar v2; addr3 |-> scalar v3; R] m0
  H0 : seps [R; addr3 |-> scalar v3; addr4 |-> scalar v4; addr1 |-> scalar v1_new] m1
  order :=  [3; 2;                   2;                   0                      ] *)
  pose [3%nat; 2%nat; 2%nat; 0%nat] as order.
  eassert (@iff1 mem _ _) as E. {
    etransitivity.
    1: match goal with
       | _: seps ?l m1 |- _ => eapply (reorder_is_iff1 order l)
       end.
    1: reflexivity.
    cbv [reorder].
    let r := eval vm_compute in (order_to_permutation order) in
        change (order_to_permutation order) with r.
    cbv [apply_permutation apply_permutation_with_default List.map List.nth].
    reflexivity.
  }
  eapply E.
  exact H0.
Qed.

(* TODO: write down postcondition only at end *)
Definition swap_locals: {f: list string * list string * cmd &
  forall call t m a b,
    vc_func call f t m [a; b] (fun t' m' retvs =>
      t' = t /\ m' = m /\ retvs = [b; a]
  )}.
    (* note: we could just return ["b", "a"] and then the body would be just skip *)
    start.
#*/ t = a;                                                                   /*.
#*/ a = b;                                                                   /*.
#*/ b = t;                                                                   /*.
#*/ res1 = a;                                                                /*.
#*/ res2 = b;                                                                /*.
#*/ return res1, res2;                                                       /*.
    intuition congruence.
Defined.

(* TODO: write down postcondition only at end *)
Definition swap: {f: list string * list string * cmd &
  forall call t m a_addr b_addr a b R,
    seps [a_addr |-> scalar a; b_addr |-> scalar b; R] m ->
    vc_func call f t m [a_addr; b_addr] (fun t' m' retvs =>
      t' = t /\ seps [a_addr |-> scalar b; b_addr |-> scalar a; R] m' /\ retvs = []
  )}.
    start.
#*/ t = load(a_addr);                                                        /*.

    do 2 eexists.
    refine (Morphisms.subrelation_refl Lift1Prop.impl1 _ _ _ current_mem x).
    (* Here we can make goal modifications influenced by the canceling problem,
       and the goal modifications will still be visible in the continuation subgoal: *)
    remember a as we_could_have_split_a_into_two_pieces eqn: E.
    ecancel_step_by_implication.
    eapply impl1_done.

    put_into_current_locals.

    (* Changes made in load subgoal still visible: *)

#*/ store(a_addr, load(b_addr));                                             /*.

    do 2 eexists.
    refine (Morphisms.subrelation_refl Lift1Prop.impl1 _ _ _ current_mem x).
    (* TODO: how to print seps list with emps? *)
    ecancel_step_by_implication.
    eapply impl1_done.
    eapply store_word_of_sep_cps.
    refine (Morphisms.subrelation_refl Lift1Prop.impl1 _ _ _ current_mem x).
    ecancel_step_by_implication.
    eapply impl1_done.
    unfold seps. (* will need rearrangement anyways to preserve order *)
    intros.

#*/ store(b_addr, t);                                                        /*.

    eapply store_word_of_sep_cps.
    refine (Morphisms.subrelation_refl Lift1Prop.impl1 _ _ _ m' H).
    unfold seps at 1.
    reify_goal.
    ecancel_step_by_implication.
    eapply impl1_done.
    intros.
    cbn [seps] in *.
    change ((seps [a_addr |-> scalar b; b_addr |-> scalar b; R]) m') in H.
    change ((seps [b_addr |-> scalar t; a_addr |-> scalar b; R]) m'0) in H0.
    (* Note: order of sep clauses was changed *)

Undelimit Scope live_scope.
Close Scope live_scope.

  match goal with
  | HOld: seps _ ?mOld, H: seps _ ?m |- wp_cmd _ _ _ ?m _ _ => idtac HOld H
  end.

idtac.

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