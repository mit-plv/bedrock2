Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Ltac2.Ltac2. Set Default Proof Mode "Classic".
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Datatypes.Inhabited.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface coqutil.Word.Bitwidth coqutil.Word.Properties.
Require Import coqutil.Tactics.syntactic_unify.
Require Import bedrock2.find_hyp.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.ident_ops.
Require Import coqutil.Tactics.pattern_tuple.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.groundcbv.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.TacticError. Local Open Scope Z_scope.
Require Import LiveVerif.string_to_ident.
Require Import bedrock2.ident_to_string.
Require Import LiveVerif.LiveRules.

Definition dlet{A B: Type}(rhs: A)(body: A -> B): B := body rhs.

Lemma let_to_dlet{A: Type}(rhs: A)(body: A -> Prop):
  (let x := rhs in body x) -> dlet rhs body.
Proof. exact id. Qed.

(* `vpattern x in H` is like `pattern x in H`, but x must be a variable and is
   used as the binder in the lambda being created *)
Ltac vpattern_in x H :=
  pattern x in H;
  lazymatch type of H with
  | ?f x => change ((fun x => ltac:(let r := eval cbv beta in (f x) in exact r)) x) in H
  end.
Tactic Notation "vpattern" ident(x) "in" ident(H) := vpattern_in x H.

Declare Scope live_scope.
Delimit Scope live_scope with live.
Local Open Scope live_scope.

Inductive scope_kind: Set :=
| FunctionParams | FunctionBody
| IfCondition | ThenBranch | ElseBranch
| LoopBody | LoopInvOrPreOrPost.
Inductive scope_marker(sk: scope_kind): Prop := mk_scope_marker.

Notation "'____' sk '____'" := (scope_marker sk) (only printing) : live_scope.

Ltac assert_scope_kind expected :=
  let sk := lazymatch goal with
            | H: scope_marker ?sk |- _ => sk
            | _ => fail "no scope marker found"
            end in
  tryif constr_eq sk expected then idtac
  else fail "This snippet is only allowed in a" expected "block, but we're in a" sk "block".

(* When a memory assertion is encountered in conclusion the be proven,
   we need to know in which of the two modes we are:
   a) prove function precondition, with continuation in the "Rest" argument
      of the canceling judgment
   b) prove invariant or postcondition, where "Rest" argument should be True,
      even if there's more stuff to prove.
   See also HeapletwiseHyps.will_merge_back_later.
   This marker tells us that we are in mode b). *)
Definition packaged_mem_clause_marker(P: Prop) := P.

Fixpoint ands(Ps: list Prop): Prop :=
  match Ps with
  | cons P rest => P /\ ands rest
  | nil => True
  end.

Lemma ands_nil: ands nil. Proof. cbn. auto. Qed.
Lemma ands_cons: forall [P: Prop] [Ps: list Prop], P -> ands Ps -> ands (P :: Ps).
Proof. cbn. auto. Qed.

Ltac destruct_ands H :=
  lazymatch type of H with
  | ands nil => clear H
  | ands (cons _ _) => destruct H as [? H]; destruct_ands H
  end.

Ltac has_unique_eq_def x :=
  match goal with
  | H1: x = _, H2: x = _ |- _ => fail 1 x "has two definitions:" H1 "and" H2
  | H1: x = _, H2: _ = x |- _ => fail 1 x "has two definitions:" H1 "and" H2
  | H1: _ = x, H2: _ = x |- _ => fail 1 x "has two definitions:" H1 "and" H2
  | H: x = _ |- _ => idtac
  | H: _ = x |- _ => idtac
  | |- _ => fail 1 x "has no definition"
  end.

Ltac has_no_eq_def x :=
  match goal with
  | H: x = _ |- _ => fail 1 x "has definition" H
  | H: _ = x |- _ => fail 1 x "has definition" H
  | |- _ => idtac
  end.

Ltac not_letbound x :=
  assert_fails (idtac; let _ := eval cbv delta [x] in x in idtac).

Ltac subst_vars_with_unique_var_rhs :=
  repeat match goal with
    | H: ?x = ?rhs |- _ => is_var x; is_var rhs; not_letbound x; has_unique_eq_def x; subst x
    | x := ?rhs |- _ => is_var rhs; has_no_eq_def x; subst x
    end.

(* Can be customized with ::= *)
Ltac is_substitutable_rhs_for_package_context rhs :=
  first [ is_var rhs
        | is_const rhs
        | lazymatch isZcst rhs with true => idtac end
        | lazymatch rhs with
          | word.of_Z ?x => is_substitutable_rhs_for_package_context x
          | word.unsigned ?x => is_substitutable_rhs_for_package_context x
          end ].

(* Note: Don't do this when some variables are local variables, because
   we always want to keep local variables as variables in the context. *)
Ltac subst_small_rhses :=
  repeat match goal with
    | H: ?x = ?rhs |- _ =>
        is_var x;
        is_substitutable_rhs_for_package_context rhs;
        not_letbound x;
        has_unique_eq_def x;
        subst x
    end.

Ltac add_hyp_to_post Post :=
  match goal with
  | H: ?T |- _ =>
      tryif constr_eq H Post then fail else idtac;
      tryif ident_starts_with Def H then fail else idtac; (* to be added last as an elet *)
      lazymatch T with
      | scope_marker _ => fail 1 "done (scope marker reached)"
      | _ => idtac
      end;
      eapply (ands_cons H) in Post; clear H
  end.

Ltac add_eq_as_elet_to_post E Post :=
  lazymatch type of E with
  | ?x = ?rhs =>
      vpattern x in Post;
      lazymatch type of Post with
      | ?f x => eapply (mk_elet rhs f x E) in Post
      end;
      clear x E
  end.

Ltac add_var_as_exists_to_post x Post :=
  vpattern x in Post;
  lazymatch type of Post with
  | ?f x => eapply (ex_intro f x) in Post
  end;
  clear x.

Ltac last_var_except p :=
  match goal with
  | x: _ |- _ => lazymatch x with
                 | p => fail
                 | _ => x
                 end
  end.

Ltac add_last_var_or_hyp_to_post Post :=
  let lastvar := last_var_except Post in
  let T := type of lastvar in
  lazymatch T with
  | scope_marker _ => fail "done (scope marker reached)"
  | _ => idtac
  end;
  tryif ident_starts_with Def lastvar then
    add_eq_as_elet_to_post lastvar Post
  else (clear lastvar || add_var_as_exists_to_post lastvar Post).

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
  clearbody y;
  (* y (t or m or l or measure) will be patterned out at end of package_context *)
  move y at top.

Ltac add_mem_equality_to_Post_or_move_at_top m Post :=
  lazymatch type of Post with
  | context[m] =>
      (* current packaged context contains an assertion about memory (the usual case) *)
      move m at top
  | _ =>
      (* we're in a function that does not use the heap at all *)
      add_equality_to_post m Post
  end.

Ltac add_equalities_to_post Post :=
  lazymatch goal with
  (* loop pre/post *)
  | |- ?E (?Ghosts, ?Measure, ?T, ?M, ?L) =>
      add_equality_to_post L Post;
      add_mem_equality_to_Post_or_move_at_top M Post;
      lazymatch type of Post with
      | context[T] => idtac (* current packaged context already says something about the
                               trace, so only keep that *)
      | _ => add_equality_to_post T Post (* no assertion about trace, so let's add a default
                                            assertion saying it doesn't change *)
      end;
      add_equality_to_post Measure Post
  (* loop invariant *)
  | |- ?E ?Measure ?T ?M ?L =>
      add_equality_to_post L Post;
      add_mem_equality_to_Post_or_move_at_top M Post;
      add_equality_to_post T Post;
      add_equality_to_post Measure Post
  (* if branch post *)
  | |- ?E ?T ?M ?L =>
      add_equality_to_post L Post;
      add_mem_equality_to_Post_or_move_at_top M Post;
      add_equality_to_post T Post
  end.

Ltac get_current_mem :=
  lazymatch goal with
  | |- ?E (_, ?t, ?m, ?l) => m
  | |- ?E ?t ?m ?l => m
  | |- ?g => fail "Unexpected goal shape while looking for current mem:" g
  end.

Ltac move_mem_hyp_just_below_scope_marker :=
  let m := get_current_mem in
  lazymatch goal with
  | H: ?p m |- _ =>
      change (packaged_mem_clause_marker (p m)) in H;
      move H at bottom;
      lazymatch goal with
      | s: scope_marker _ |- _ =>
          move H before s (* <-- "before" in the direction of movement *)
      end
      (* Note: the two above moves should be replaced by one single `move H below s`,
         but `below` is not implemented yet: https://github.com/coq/coq/issues/15209 *)
  | |- _ => idtac (* do nothing if this function does not use the heap *)
  end.

(* can be overridden with
   Ltac log_packaged_context P ::= idtac P. *)
Ltac log_packaged_context P := idtac.

Ltac package_context :=
  (* We always package sep log assertion, even if memory was not changed in current block.
     When proving a loop invariant at the end of a loop body, it tends to work better
     if memory hyps come earlier, because they can help determine evars *)
  move_mem_hyp_just_below_scope_marker;
  let Post := fresh "Post" in
  pose proof ands_nil as Post;
  repeat add_hyp_to_post Post;
  add_equalities_to_post Post;
  repeat add_last_var_or_hyp_to_post Post;
  let lasthyp := last_var_except Post in
  lazymatch type of lasthyp with
  | scope_marker _ => idtac
  | _ => idtac "Warning: package_context failed to package" lasthyp "(and maybe more)."
               "Note that ghost vars need to be above the loop invariant marker."
  end;
  lazymatch goal with
  | |- _ ?Measure ?T ?M ?L => pattern Measure, T, M, L in Post
  | |- _ ?T ?M ?L => pattern T, M, L in Post
  | |- _ ?tup => pattern_tuple_in_hyp tup Post
  end;
  (let t := type of Post in log_packaged_context t);
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
    forall i j [word: Type] [mem: map.map word Byte.byte]
           (m: mem) (l1 l2: list (mem -> Prop)) (b: bool) (Ps1 Ps2: list Prop),
      nth i Ps1 = seps l1 m ->
      nth j Ps2 = seps l2 m ->
      (if b then ands Ps1 else ands Ps2) ->
      seps (cons (seps (if b then l1 else l2)) nil) m /\
        if b then ands (remove_nth i Ps1) else ands (remove_nth j Ps2).
  Proof.
    intros. eapply merge_ands_at_indices in H1; [ | eassumption.. ].
    destruct b; assumption.
  Qed.
End MergingAnd.

Section MergingSep.
  Context {width: Z} {word: word.word width}
          {word_ok: word.ok word} {mem: map.map word Byte.byte} {ok: map.ok mem}.

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
  Lemma merge_seps_at_indices_same_addr_and_pred (m: mem) i j [V: Type] a (v1 v2 v: V)
        (pred: V -> word -> mem -> Prop) (Ps1 Ps2 Qs: list (mem -> Prop)) (b: bool):
    nth i Ps1 = pred v1 a ->
    nth j Ps2 = pred v2 a ->
    (if b then v1 else v2) = v ->
    seps ((seps (if b then Ps1 else Ps2)) :: Qs) m ->
    seps ((seps (if b then (remove_nth i Ps1) else (remove_nth j Ps2))) :: pred v a :: Qs) m.
  Proof.
    intros. subst v. eapply (merge_seps_at_indices m i j) in H2; [ | eassumption.. ].
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
    seps ((seps (if b then nil else nil)) :: Qs) m ->
    seps Qs m.
  Proof.
    intros.
    pose proof (seps'_iff1_seps (seps (if b then nil else nil) :: Qs)) as A.
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

Lemma push_if_into_arg1{A B: Type}(f: A -> B)(a1 a2: A)(cond: bool):
  (if cond then f a1 else f a2) = f (if cond then a1 else a2).
Proof. destruct cond; reflexivity. Qed.

Lemma push_if_into_arg2{A1 A2 B: Type}(f: A1 -> A2 -> B)(a1 a1': A1)(a2 a2': A2)(cond: bool):
  (if cond then f a1 a2 else f a1' a2') =
    f (if cond then a1 else a1') (if cond then a2 else a2').
Proof. destruct cond; reflexivity. Qed.

Lemma push_if_into_cons_tuple_same_key(c: bool)(k: String.string)[V: Type](v1 v2: V) t1 t2:
  (if c then cons (k, v1) t1 else cons (k, v2) t2)
  = cons (k, if c then v1 else v2) (if c then t1 else t2).
Proof. destruct c; reflexivity. Qed.

Lemma if_same{A: Type}(cond: bool)(a: A): (if cond then a else a) = a.
Proof. destruct cond; reflexivity. Qed.

Ltac2 rec copy_string(src: string)(dst: string)(index: int)(count: int) :=
  if Int.equal count 0 then () else
    (String.set dst index (String.get src index);
     copy_string src dst (Int.add index 1) (Int.sub count 1)).

Ltac2 append_quote_to_string(s: string) :=
  let r := String.make (Int.add (String.length s) 1) (String.get "'" 0) in
  copy_string s r 0 (String.length s);
  r.

Ltac2 append_quote_to_ident(i: ident) :=
  Option.get (Ident.of_string (append_quote_to_string (Ident.to_string i))).

Ltac2 is_fresh(x: ident) :=
  match Control.case (fun _ => Control.hyp x) with
  | Val _ => false
  | Err _ => true
  end.

Ltac2 rec fresh'_from_existing_ident(i: ident) :=
  let i' := append_quote_to_ident i in
  if is_fresh i' then i' else fresh'_from_existing_ident i'.

Ltac2 make_existing_ident_fresh(i: ident) :=
  let i' := fresh'_from_existing_ident i in Std.rename [(i, i')].

Ltac2 constr_to_ident(c: constr) :=
  match Constr.Unsafe.kind c with
  | Constr.Unsafe.Var i => i
  | _ => Control.throw_invalid_argument "not a Constr.Unsafe.Var"
  end.

Ltac make_existing_ident_fresh :=
  ltac2:(c |- make_existing_ident_fresh
                (constr_to_ident (Option.get (Ltac1.to_constr c)))).

Ltac is_fresh x := assert_succeeds (pose proof tt as x).

(* Appends ' instead of increasing counters, which makes it easier to distinguish
   old versions of local variables from the current ones, because C variable names
   cannot contain '.
   Note that in order to pass an ident from Ltac1 to Ltac2, we have to convert
   it to a constr, which only works if the ident refers to an existing variable.
   TODO using Ltac1 Tactic Notation and Ltac2's Ltac1.to_ident, we could also
   pass an ident from Ltac1 to Ltac2, and simplify the code a bit. *)
Ltac make_fresh x :=
  tryif is_fresh x then idtac else make_existing_ident_fresh constr:(x).

(* old:
Ltac make_fresh x :=
  tryif is_fresh x then idtac else let x' := fresh x "'" in rename x into x'.
*)

Ltac intro_word name :=
  let lowest :=
    match goal with
    | h: ?t |- _ =>
        lazymatch t with
        | @word.rep _ _ => h
        | scope_marker _ => h
        | trace => h
        end
    end in
  intro name before lowest.

Section PullELet.
  Context {A: Type}.

  Lemma pull_if_elet_l (c: bool) (a: A) (P: A -> Prop) (F: Prop):
    (if c then elet a P else F) -> elet a (fun x => if c then P x else F).
  Proof.
    destruct c.
    - intros [x E B]. econstructor; eassumption.
    - intros. econstructor. 1: reflexivity. assumption.
  Qed.

  Lemma pull_if_elet_r (c: bool) (a: A) (P: A -> Prop) (T: Prop):
    (if c then T else elet a P) -> elet a (fun x => if c then T else P x).
  Proof.
    destruct c.
    - intros. econstructor. 1: reflexivity. assumption.
    - intros [x E B]. econstructor; eassumption.
  Qed.
End PullELet.

Ltac pull_elet_dlet_and_exists_step :=
  lazymatch goal with
  | H: if _ then elet _ (fun x => _) else _ |- _ =>
      make_fresh x;
      lazymatch type of H with
      | if ?c then elet ?rhs ?body else ?els =>
          eapply (pull_if_elet_l c rhs body els) in H;
          case H;
          clear H;
          intro_word x;
          intros ?Def0 H
      end
  | H: if _ then _ else elet _ (fun x => _) |- _ =>
      make_fresh x;
      lazymatch type of H with
      | if ?c then ?thn else elet ?rhs ?body =>
          eapply (pull_if_elet_r c rhs body thn) in H;
          case H;
          clear H;
          intro_word x;
          intros ?Def0 H
      end
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
          | cbn [hd skipn];
            repeat first [ rewrite if_same
                         | rewrite push_if_into_arg1
                         | rewrite push_if_into_arg2 ];
            reflexivity .. ]
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
      | _ => constr:(false)
      end
  | _ => constr:(false)
  end.

Ltac same_addr_and_pred P Q :=
  lazymatch P with
  | ?pred ?valueP ?addr =>
      lazymatch Q with
      | pred ?valueQ addr => constr:(true)
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
                 | seps _ m => constr:(true)
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
      merge_pair H Ps Qs same_addr_and_pred (merge_seps_at_indices_same_addr_and_pred m)
  end.

Ltac merge_seps_done :=
  lazymatch goal with
  | H: seps ((seps (if ?b then nil else nil)) :: ?Rs) ?m |- exec _ _ _ ?m _ _ =>
      (* memory was modified in different ways in then/else branch *)
      eapply merge_seps_done in H; cbn [seps] in H
  | H: seps _ ?m |- exec _ _ _ ?m _ _ =>
      (* memory was not modified (or in exactly the same way in both branches) *)
      cbn [seps] in H
  | H: ?m = _ |- exec _ _ _ ?m _ _ =>
      (* this function does not use the heap *)
      idtac
  | |- _ => fail 1000 "failed to match the sepclauses of the then-branch and else-branch"
  end.

Ltac list_map_ignoring_failures f l :=
  lazymatch l with
  | nil => open_constr:(@nil _)
  | cons ?h ?t =>
      let r := list_map_ignoring_failures f t in
      match constr:(Set) with
      | _ => let h' := f h in constr:(cons h' r)
      | _ => r
      end
  end.

Ltac key_of_pair_if_not_in term pair :=
  lazymatch pair with
  | (?key, _) =>
      lazymatch term with
      | context[(key, _)] => fail
      | _ => key
      end
  end.

Ltac normalize_locals_expr l :=
  let keys := eval lazy in (map.keys l) in
  let values := eval hnf in
    (match map.getmany_of_list l keys with
     | Some vs => vs
     | None => nil
     end) in
  let kvs := eval unfold List.combine in (List.combine keys values) in
  constr:(map.of_list kvs).

Ltac normalize_locals_wp :=
  lazymatch goal with
  | |- wp_cmd ?call ?c ?t ?m ?l ?post =>
      let l' := normalize_locals_expr l in change (wp_cmd call c t m l' post)
  end.

Ltac normalize_locals_eq :=
  lazymatch goal with
  | |- ?l = ?r => let l' := normalize_locals_expr l in change (l' = r)
  end.

Ltac normalize_locals_post :=
  lazymatch goal with
  | |- ?post ?t ?m ?l =>
        let l' := normalize_locals_expr l in
        change (post t m l')
  end.

Ltac after_if :=
  let H := fresh in
  intros ? ? ? [?c ?Def0 H];
  cbv beta delta [packaged_mem_clause_marker] in H;
  repeat pull_elet_dlet_and_exists_step;
  repeat merge_and_pair constr_eqb merge_ands_at_indices_same_prop;
  repeat merge_and_pair neg_prop merge_ands_at_indices_neg_prop;
  repeat merge_and_pair same_lhs merge_ands_at_indices_same_lhs;
  repeat merge_and_pair seps_about_same_mem merge_ands_at_indices_seps_same_mem;
  repeat merge_sep_pair_step;
  merge_seps_done;
  try match goal with
    | H: if _ then ands nil else ands nil |- _ => clear H
    end;
  lazymatch goal with
  | H: ?l = (if _ then map.of_list ?l1 else map.of_list ?l2) |- wp_cmd _ _ _ _ ?l _ =>
      (* common case: then branch and else branch modified locals in different ways *)
      subst l;
      eapply wp_push_if_into_merge_locals
  | H: ?l = map.of_list _ |- wp_cmd _ _ _ _ ?l _ =>
      (* special case: then branch and else branch modified locals in exactly the same
         way, so `merge_and_pair constr_eqb merge_ands_at_indices_same_prop` already
         got rid (or did not introduce at all) the if *)
      subst l
  | |- _ => fail 1000 "unexpected shape of locals"
  end.

Ltac unpackage_context_step :=
  lazymatch goal with
  | H: elet _ (fun x => _) |- _ => make_fresh x; destruct H as [x ?Def0 H]
  | H: exists x,  _ |- _ => make_fresh x; destruct H as [x H]
  | H: dlet _ (fun x => _) |- _ =>
      make_fresh x;
      lazymatch type of H with
      | dlet ?rhs ?body =>
          pose (x := rhs);
          let t := beta1 body x in
          change t in H
      end
  | H: ands _ |- _ =>
      cbv beta delta [packaged_mem_clause_marker] in H;
      destruct_ands H
  end.

Ltac unpackage_context :=
  cbn [seps] in *;
  repeat unpackage_context_step;
  lazymatch goal with
  | H: ?l = @map.of_list String.string (@word.rep _ _) _ _ |- _ => subst l
  end.
