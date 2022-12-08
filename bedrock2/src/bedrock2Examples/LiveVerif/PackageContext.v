Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Datatypes.Inhabited.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import bedrock2.groundcbv.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.TacticError. Local Open Scope Z_scope.
Require Import bedrock2Examples.LiveVerif.string_to_ident.
Require Import bedrock2.ident_to_string.
Require Import bedrock2.HeapletwiseHyps.
Require Import bedrock2.bottom_up_simpl_ltac1.
Require Import bedrock2Examples.LiveVerif.LiveRules.

Definition dlet{A B: Type}(rhs: A)(body: A -> B): B := body rhs.

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

Inductive scope_kind :=
  FunctionBody | IfCondition | ThenBranch | ElseBranch | LoopBody | LoopInvariant.
Inductive scope_marker: scope_kind -> Set := mk_scope_marker sk : scope_marker sk.

Notation "'____' sk '____'" := (scope_marker sk) (only printing) : live_scope.

Ltac assert_scope_kind expected :=
  let sk := lazymatch goal with
            | H: scope_marker ?sk |- _ => sk
            | _ => fail "no scope marker found"
            end in
  tryif constr_eq sk expected then idtac
  else fail "This snippet is only allowed in a" expected "block, but we're in a" sk "block".

Fixpoint ands(Ps: list Prop): Prop :=
  match Ps with
  | cons P rest => P /\ ands rest
  | nil => True
  end.

Lemma ands_nil: ands nil. Proof. cbn. auto. Qed.
Lemma ands_cons: forall [P: Prop] [Ps: list Prop], P -> ands Ps -> ands (P :: Ps).
Proof. cbn. auto. Qed.

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
  Lemma merge_seps_at_indices_same_addr_and_pred (m: mem) i j [V: Type] a (v1 v2: V)
        (pred: V -> word -> mem -> Prop) (Ps1 Ps2 Qs: list (mem -> Prop)) (b: bool):
    nth i Ps1 = pred v1 a ->
    nth j Ps2 = pred v2 a ->
    seps ((seps (if b then Ps1 else Ps2)) :: Qs) m ->
    seps ((seps (if b then (remove_nth i Ps1) else (remove_nth j Ps2)))
            :: pred (if b then v1 else v2) a :: Qs) m.
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

Lemma push_if_into_cons_tuple_same_key(cond: bool)(k: String.string)(v1 v2: Z) t1 t2:
  (if cond then cons (k, v1) t1 else cons (k, v2) t2)
  = cons (k, if cond then v1 else v2) (if cond then t1 else t2).
Proof. destruct cond; reflexivity. Qed.

Lemma if_same{A: Type}(cond: bool)(a: A): (if cond then a else a) = a.
Proof. destruct cond; reflexivity. Qed.

Ltac is_fresh x := assert_succeeds (pose proof tt as x).

Ltac make_fresh x :=
  tryif is_fresh x then idtac else let x' := fresh x "_0" in rename x into x'.

Ltac letbind_locals start_index :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.of_list ?kvs) _ =>
      lazymatch eval hnf in (List.nth_error kvs start_index) with
      | None => idtac (* done *)
      | Some (?name, ?val) =>
          tryif is_var val then
            letbind_locals (S start_index)
          else (
            let tmp := fresh in
            set (tmp := val);
            let namei := string_to_ident name in
            make_fresh namei;
            rename tmp into namei;
            letbind_locals (S start_index)
         )
      end
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
  intros ? ? ? ?;
  repeat pull_dlet_and_exists_step;
  repeat merge_and_pair constr_eqb merge_ands_at_indices_same_prop;
  repeat merge_and_pair neg_prop merge_ands_at_indices_neg_prop;
  repeat merge_and_pair same_lhs merge_ands_at_indices_same_lhs;
  repeat merge_and_pair seps_about_same_mem merge_ands_at_indices_seps_same_mem;
  repeat merge_sep_pair_step;
  repeat match goal with
  | H: if ?b then ?thn else ?els |- _ =>
      clear H;
      assert_succeeds ( (* test if clearing H was justified because it's redundant: *)
        (* TODO this isn't general enough, after "unfold ands", we might also need
           to subst all locals and simplify unsigned_of_Z, so it would be better to
           not package at all the Props that follow from the branching condition *)
        idtac;
        let sp := constr:(_: BoolSpec _ _ b) in
        lazymatch type of sp with
        | BoolSpec ?Pt ?Pf _ =>
            assert ((Pt -> thn) /\ (Pf -> els)) by (unfold ands; clear; intuition auto)
        end)
    end;
  lazymatch goal with
  | H: ?l = _ |- wp_cmd _ _ _ _ ?l _ =>
      repeat (rewrite ?push_if_into_cons_tuple_same_key,
                      ?if_same,
                      ?push_if_into_arg1,
                      ?push_if_into_arg2 in H);
      subst l
  end;
  letbind_locals 0%nat.
