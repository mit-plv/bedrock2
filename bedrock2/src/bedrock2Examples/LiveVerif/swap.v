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

Section WithParams.
  Import bedrock2.Syntax.
  Context {word: word.word 32} {mem: map.map word byte} {locals: map.map string word}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem} {locals_ok: map.ok locals}.
  Context {ext_spec: ExtSpec}.

  (* non-unfoldable wrappers, their definition might be swapped with something else later,
     as long as it satisfies the lemmas that follow below *)

  Inductive wp_expr(m: mem)(l: locals)(e: expr)(post: word -> Prop): Prop :=
    mk_wp_expr: WeakestPrecondition.expr m l e post -> wp_expr m l e post.

  Lemma wp_var: forall m l x v (post: word -> Prop),
      map.get l x = Some v ->
      post v ->
      wp_expr m l (expr.var x) post.
  Proof.
    intros. constructor. cbn. unfold WeakestPrecondition.get. eauto.
  Qed.

  Lemma wp_load: forall m l sz addr (post: word -> Prop),
      wp_expr m l addr (fun a => exists v, Memory.load sz m a = Some v /\ post v) ->
      wp_expr m l (expr.load sz addr) post.
  Proof.
    intros. constructor. cbn. unfold load. inversion H. assumption.
  Qed.

  Inductive wp_cmd(call: (string -> trace -> mem -> list word ->
                          (trace -> mem -> list word -> Prop) -> Prop))
            (c: cmd)(t: trace)(m: mem)(l: locals)(post: trace -> mem -> locals -> Prop): Prop :=
    mk_wp_cmd: WeakestPrecondition.cmd call c t m l post -> wp_cmd call c t m l post.

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

  Lemma wp_store: forall call sz ea ev t m l rest post,
      wp_expr m l ea (fun a =>
        wp_expr m l ev (fun v =>
          exists m', Memory.store sz m a v = Some m' /\ wp_cmd call rest t m' l post)) ->
      wp_cmd call (cmd.seq (cmd.store sz ea ev) rest) t m l post.
  Proof.
    intros. constructor. cbn.
    eapply wp_expr_to_dexpr in H. unfold dexpr in *. fwd.
    eapply wp_expr_to_dexpr in Hp1. unfold dexpr in *. fwd.
    destruct Hp1p1p1. unfold store. eauto 10.
  Qed.

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
  | |- wp_expr _ _ (expr.load _ _) _ => eapply wp_load
  | |- wp_expr _ _ (expr.var _) _ => eapply wp_var; [ reflexivity |]
  | |- exists _, _ /\ _ => eexists; split
  | |- Memory.load access_size.word _ _ = Some _ =>
    eapply Scalars.load_word_of_sep; try solve [ecancel_assumption]
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
| SRet(xs: list string)
(*
| SIf(cond: Syntax.expr)(merge: bool)
| SEnd
| SElse
*).

Ltac assign name val :=
  eapply (wp_set _ name val);
  repeat eval_expr_step;
  [.. (* maybe some unsolved side conditions *) | put_into_current_locals].

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


Load LiveVerif.

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
    (scalar a_addr a * scalar b_addr b * R)%sep m ->
    vc_func call f t m [a_addr; b_addr] (fun t' m' retvs =>
      t' = t /\ (scalar a_addr b * scalar b_addr a * R)%sep m' /\ retvs = []
  )}.
    start.
#*/ t = load(a_addr);                                                        /*.

  Undelimit Scope live_scope.
  Close Scope live_scope.
{

  eapply (wp_store _ access_size.word live_expr:(a_addr) (live_expr:(load(b_addr)))).
  eval_expr_step.
  eval_expr_step.
  eval_expr_step.
  eval_expr_step.
  { eval_expr_step. }
  eapply Scalars.store_word_of_sep.
1:

try solve [ecancel_assumption].

Abort.

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
