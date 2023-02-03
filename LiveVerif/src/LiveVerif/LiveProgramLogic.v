Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import Coq.Strings.String.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.foreach_hyp.
Require Import coqutil.Datatypes.RecordSetters.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import bedrock2.groundcbv.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.TacticError. Local Open Scope Z_scope.
Require Import LiveVerif.string_to_ident.
Require Import bedrock2.find_hyp.
Require Import bedrock2.ident_to_string.
Require Import bedrock2.HeapletwiseHyps.
Require Import bedrock2.HeapletwiseAutoSplitMerge.
Require Import bedrock2.PurifySep.
Require Import bedrock2.bottom_up_simpl_ltac1.
Require Import LiveVerif.LiveRules.
Require Import LiveVerif.PackageContext.
Require Import LiveVerif.LiveSnippet.

Definition functions_correct
  (* universally quantified abstract function list containing all functions: *)
  (qfs: list (string * func)):
  (* specs of a subset of functions for which to assert correctness *)
  list (list (string * func) -> Prop (* spec_of mentioning function name *)) -> Prop :=
  List.Forall (fun spec => spec qfs).

Definition function_with_callees: Type :=
  func * list (list (string * func) -> Prop (* spec_of mentioning function name *)).

Definition program_logic_goal_for(name: string)(f: function_with_callees)
  {spec: bedrock2.ProgramLogic.spec_of name}: Prop :=
  match f with
  | (impl, callees) => forall functions,
      functions_correct functions callees -> spec (cons (name, impl) functions)
  end.

Definition nth_spec(specs: list (list (string * func) -> Prop))(n: nat) :=
  Eval unfold List.nth in (List.nth n specs (fun _ => True)).

Lemma nth_function_correct: forall fs n specs spec,
    nth_spec specs n = spec ->
    functions_correct fs specs ->
    spec fs.
Proof.
  unfold functions_correct. intros. subst spec.
  eapply (proj1 (List.Forall_nth_default' _ _ _ I)) in H0.
  exact H0.
Qed.

Definition ready{P: Prop} := P.

Ltac purify_heapletwise_pred H pred m :=
  let HP := fresh H "P" in eassert (purify pred _) as HP by eauto with purify;
  specialize (HP m H).

Ltac purify_heapletwise_hyp_of_type H t :=
  match t with
  | ?R ?m => purify_heapletwise_pred H R m
  | with_mem ?m ?R => purify_heapletwise_pred H R m
  | _ => idtac
  end.

Ltac purify_heapletwise_hyps := foreach_hyp purify_heapletwise_hyp_of_type.

Ltac bottom_up_simpl_sidecond_hook ::=
  purify_heapletwise_hyps;
  try bottom_up_simpl_in_goal;
  lia.

Ltac start :=
  lazymatch goal with
  | |- @program_logic_goal_for ?fname ?evar ?spec =>
      lazymatch open_constr:((_, _): function_with_callees) with
      | ?p => unify evar p
      end;
      subst evar;
      unfold program_logic_goal_for, spec;
      let fs := fresh "fs" in
      intro fs;
      let n := fresh "Scope0" in pose proof (mk_scope_marker FunctionBody) as n;
      intros;
      WeakestPrecondition.unfold1_call_goal;
      cbv match beta delta [WeakestPrecondition.call_body];
      lazymatch goal with
      | |- if ?test then ?T else _ =>
        replace test with true by reflexivity; change T
      end;
      eapply prove_func;
      [ lazymatch goal with
        | |- map.of_list_zip ?argnames_evar ?argvalues = Some ?locals_evar =>
             let argnames := map_with_ltac varconstr_to_string argvalues in
             unify argnames_evar argnames;
             let kvs := eval unfold List.combine in (List.combine argnames argvalues) in
             unify locals_evar (map.of_list kvs);
             reflexivity
        end
      | ]
  | |- _ => fail "goal needs to be of shape (@program_logic_goal_for ?fname ?evar ?spec)"
  end.

Ltac put_into_current_locals :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.put ?l ?x ?v) _ =>
    let i := string_to_ident x in
    make_fresh i;
    (* match again because there might have been a renaming *)
    lazymatch goal with
    | |- wp_cmd ?call ?c ?t ?m (map.put ?l ?x ?v) ?post =>
        tryif (is_var v; lazymatch l with
                         | context[(_, v)] => fail
                         | _ => idtac
                         end)
        then (* v is a variable, but not a program variable, so we can rename it into x
                instead of posing a new variable *)
          rename v into i
        else (
          (* tradeoff between goal size blowup and not having to follow too many aliases *)
          let v' := rdelta_var v in
          pose (i := v');
          change (wp_cmd call c t m (map.put l x i) post)
        )
    end;
    normalize_locals_wp
  end.

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

Ltac destruct_ifs :=
  repeat match goal with
         | H: context[if ?b then _ else _] |- _ =>
             let t := type of b in constr_eq t bool; destr b
         | |- context[if ?b then _ else _] =>
             let t := type of b in constr_eq t bool; destr b
         end.

Ltac allow_all_substs := constr:(true). (* TODO default to false *)
Ltac allow_all_splits := constr:(true). (* TODO default to false *)

Ltac prove_concrete_post_pre :=
    purify_heapletwise_hyps;
    let H := fresh "M" in collect_heaplets_into_one_sepclause H;
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
    lazymatch allow_all_substs with
    | true => repeat match goal with
                | x := _ |- _ => subst x
                end
    | false => idtac
    end;
    lazymatch allow_all_splits with
    | true => destruct_ifs
    | false => idtac
    end;
    repeat match goal with
           | H: ands (_ :: _) |- _ => destruct H
           | H: ands nil |- _ => clear H
           end;
    cbn [List.app List.firstn List.nth] in *;
    repeat match goal with
           | |- _ /\ _ => split
           | |- ?x = ?x => reflexivity
           | |- sep _ _ _ => ecancel_assumption
           | H: _ \/ _ |- _ =>
               lazymatch allow_all_splits with
               | true => destruct H
               end
           | |- exists _, _ => eexists
           end;
    try bottom_up_simpl_in_goal.

Create HintDb prove_post.

Ltac prove_concrete_post :=
  prove_concrete_post_pre;
  try congruence;
  try ZnWords;
  intuition (congruence || ZnWords || eauto with prove_post).

Definition final_postcond_marker(P: Prop) := P.

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
    eexists; split;
    [ reflexivity
    | lazymatch goal with
      | |- ?G => change (final_postcond_marker G)
      end ]
  end.

Ltac strip_conss l :=
  lazymatch l with
  | cons _ ?t => strip_conss t
  | _ => l
  end.

Ltac package_heapletwise_context :=
  let H := fresh "M" in collect_heaplets_into_one_sepclause H;
  package_context.

Ltac prove_loop_invariant := try solve [prove_concrete_post].

Ltac unset_loop_body_vars :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.of_list ?l) ?post =>
      let newvars := list_map_ignoring_failures ltac:(key_of_pair_if_not_in post) l in
      eapply (wp_unset_many newvars);
      normalize_locals_wp
  end.

Ltac close_block :=
  lazymatch goal with
  | B: scope_marker ?sk |- _ =>
      lazymatch sk with
      | ElseBranch =>
          eapply wp_skip;
          package_heapletwise_context
      | LoopBody =>
          unset_loop_body_vars;
          eapply wp_skip;
          lazymatch goal with
          | |- exists _, _ /\ _ => eexists; split
          end;
          prove_loop_invariant
      | FunctionBody =>
          lazymatch goal with
          | H: functions_correct ?fs ?l |- _ =>
              let T := lazymatch type of l with list ?T => T end in
              let e := strip_conss l in
              unify e (@nil T)
          end;
          lazymatch goal with
          | |- wp_cmd _ _ _ _ _ _ => ret (@nil String.string)
          | |- @final_postcond_marker ?g => idtac (* ret was already called *)
          end;
          lazymatch goal with
          | |- @final_postcond_marker ?g => change g
          end;
          prove_concrete_post
      | _ => fail "Can't end a block here"
      end
  | _ => fail "no scope marker found"
  end.

(* Given a list l and an element e,
   returns a suffix of l starting with e and e's index in l,
   or if not found, returns l with all cons stripped, and the number of stripped cons *)
Ltac suffix_and_index_of e l :=
  lazymatch l with
  | cons e _ => constr:((l, O))
  | cons _ ?rest =>
      lazymatch suffix_and_index_of e rest with
      | (?s, ?n) => constr:((s, S n))
      end
  | _ => constr:((l, O))
  end.

Ltac is_evar_b x :=
  match constr:(Set) with
  | _ => let __ := match constr:(Set) with
                   | _ => is_evar x
                   end in
         constr:(true)
  | _ => constr:(false)
  end.

(* Given an element e and a list l ending in an evar, if e is in the list,
   return its index, else instantiate the evar with the cons of e and a new evar
   for the new tail, and also return the index of e *)
Ltac index_of_or_else_add e l :=
  lazymatch suffix_and_index_of e l with
  | (?suffix, ?n) =>
      lazymatch is_evar_b suffix with
      | true =>
          let new_tail := open_constr:(cons e _) in
          let __ := match constr:(Set) with
                    | _ => unify suffix new_tail
                    end in n
      | false => n
      end
  end.

Goal exists x y, cons x (cons 22 y) = cons 33 (cons 22 (cons 11 nil)).
  do 2 eexists.
  lazymatch goal with
  | |- ?xs = _ => lazymatch index_of_or_else_add 22 xs with 1%nat => idtac end
  end.
  lazymatch goal with
  | |- ?xs = _ => lazymatch index_of_or_else_add 11 xs with 2%nat => idtac end
  end.
  lazymatch goal with
  | |- ?xs = _ => lazymatch index_of_or_else_add 11 xs with 2%nat => idtac end
  end.
  reflexivity.
Abort.

(* lhs:    option (bool (* is_decl *) * string (* varname *))
   fname:  string
   arges:  list expr *)
Ltac call lhs fname arges :=
  let resnames := lazymatch lhs with
                  | Some (_, ?resname) => constr:(cons resname nil)
                  | None => constr:(@nil String.string)
                  end in
  eapply (wp_call _ _ _ _ resnames arges);
  [ let s := lazymatch constr:(_ : ProgramLogic.spec_of fname) with ?sp => sp end in
    lazymatch goal with
    | H: functions_correct ?fs ?l |- _ =>
        let n := index_of_or_else_add s l in
        eapply (nth_function_correct _ n) in H; [ | cbv [nth_spec]; reflexivity ];
        let h := head s in
        unfold h in H;
        eapply H
    end
  | ];
  [ (* exactly one goal should be left, because spec may only have 1 precondition
       (joined with /\) *) ].

(* Assigns default well_founded relations to types.
   Use lower costs to override existing entries. *)
Create HintDb wf_of_type.

#[export] Hint Resolve word.well_founded_lt_unsigned | 4 : wf_of_type.

Lemma Z_lt_downto_0_wf: well_founded (fun n m : Z => 0 <= n < m).
Proof. exact (Z.lt_wf 0). Qed.

#[export] Hint Resolve Z_lt_downto_0_wf | 4 : wf_of_type.

Tactic Notation "loop" "invariant" "above" ident(i) :=
  let n := fresh "Scope0" in pose proof (mk_scope_marker LoopInvariant) as n;
  move n after i.

Ltac while cond measure0 :=
  eapply (wp_while measure0 cond);
  [ package_heapletwise_context
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
    destruct_loop_invariant;
    lazymatch goal with
    | |- exists b, dexpr_bool3 _ _ _ b _ _ _ => eexists
    | |- _ => fail "assertion failure: hypothesis of wp_while has unexpected shape"
    end ].

Ltac is_local_var name :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.of_list ?l) _ =>
      lazymatch l with
      | context[(name, _)] => idtac
      | _ => fail 0 name "needs to be declared first"
      end
  end.

Ltac isnt_local_var name :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.of_list ?l) _ =>
      lazymatch l with
      | context[(name, _)] => fail 0 name "has already been declared"
      | _ => idtac
      end
  end.

Ltac add_regular_snippet s :=
  lazymatch s with
  | SAssign ?is_decl ?name ?rhs =>
      lazymatch is_decl with
      | true => isnt_local_var name
      | false => is_local_var name
      end;
      lazymatch rhs with
      | RCall ?fname ?arges => call (Some (is_decl, name)) fname arges
      | RExpr ?e => eapply (wp_set _ name e)
      end
  | SVoidCall ?fname ?arges => call (@None (prod bool string)) fname arges
  | SStore access_size.word ?addr ?val => eapply (wp_store_uintptr _ addr val)
  | SStore ?sz ?addr ?val => eapply (wp_store_uint _ sz addr val)
  | SIf ?c => eapply (wp_if_bool_dexpr _ c);
              let n := fresh "Scope0" in
              pose proof (mk_scope_marker IfCondition) as n
  | SElse =>
      assert_scope_kind ThenBranch;
      eapply wp_skip;
      package_heapletwise_context
  | SWhile ?cond ?measure0 => while cond measure0
  | SStart => fail "SStart can only be used to start a function"
  | SEnd => close_block
  | SRet ?retnames => ret retnames
  | SEmpty => idtac
  end.

Ltac add_snippet s :=
  lazymatch goal with
  | |- @ready _ => unfold ready; add_regular_snippet s
  | |- program_logic_goal_for _ _ =>
      lazymatch s with
      | SStart => start
      | _ => fail "expected {, but got" s
      end
  | |- final_postcond_marker _ =>
      lazymatch s with
      | SEnd => close_block
      | _ => fail "expected }, but got" s
      end
  | |- _ => fail "can't add snippet in non-ready goal"
  end.

Ltac after_if_cleanup :=
  lazymatch goal with
  | |- after_if _ _ ?Q1 ?Q2 _ _ =>
      tryif is_evar Q1 then
        fail "can't end if yet because" Q1 "not yet instantiated"
      else
        tryif is_evar Q2 then
          fail "can't end if yet because" Q2 "not yet instantiated"
        else
          after_if
  | _ => fail "expected after_if goal"
  end.

Ltac after_loop_cleanup :=
  lazymatch goal with
  | |- after_loop ?fs ?rest ?t ?m ?l ?post => unfold after_loop
  | _ => fail "expected after_loop goal"
  end.

Lemma BoolSpec_expr_branches{Bt Bf: Prop}{b: bool}{H: BoolSpec Bt Bf b}(Pt Pf Pa: Prop):
  (Bt -> Pt) ->
  (Bf -> Pf) ->
  Pa ->
  bool_expr_branches b Pt Pf Pa.
Proof.
  intros. unfold bool_expr_branches. destruct H; auto.
Qed.

Ltac subst_unless_local_var x :=
  lazymatch goal with
  | |- wp_cmd _ _ _ _ (map.of_list ?l) _ =>
      lazymatch l with
      | context[(_, x)] => fail (* don't subst local variables *)
      | _ => subst x
      end
  end.

Ltac cleanup_step :=
  match goal with
  | x := ?rhs |- _ => is_substitutable_rhs rhs; subst_unless_local_var x
  | x := _ |- _ => clear x
  | _: ?x = ?y |- _ =>
      first [ is_var x; is_substitutable_rhs y; subst_unless_local_var x
            | is_var y; is_substitutable_rhs x; subst_unless_local_var y ]
  | |- _ => progress fwd
  end.

Definition don't_know_how_to_prove_equal{A: Type} := @eq A.
Notation "'don't_know_how_to_prove_equal' x y" :=
  (don't_know_how_to_prove_equal x y)
  (only printing, at level 10, x at level 0, y at level 0,
   format "don't_know_how_to_prove_equal '//' x '//' y").

Ltac default_eq_prover :=
  match goal with
  | |- ?l = ?r => _syntactic_unify_deltavar l r; reflexivity
  | H: ?l = ?r |- ?l = ?r => exact H
  | |- _ => repeat match goal with
              | x := _ |- _ => subst x
              end;
            try bottom_up_simpl_in_goal;
            lazymatch goal with
            | |- ?l = ?r => tryif constr_eq l r then reflexivity
                            else change (don't_know_how_to_prove_equal l r)
            end
  end.

Ltac eq_prover_hook := default_eq_prover.

Ltac simpl_hook := repeat bottom_up_simpl_in_hyps_and_vars; try record.simp.

Ltac program_logic_step :=
  lazymatch goal with
  | |- dexpr_bool3 _ _ (expr.lazy_and _ _)       _ _ _ _ => eapply dexpr_bool3_lazy_and
  | |- dexpr_bool3 _ _ (expr.lazy_or _ _)        _ _ _ _ => eapply dexpr_bool3_lazy_or
  | |- dexpr_bool3 _ _ (expr.not _)              _ _ _ _ => eapply dexpr_bool3_not
  | |- dexpr_bool3 _ _ (expr.op bopname.eq _ _)  _ _ _ _ => eapply dexpr_bool3_eq
  | |- dexpr_bool3 _ _ (expr.op bopname.ltu _ _) _ _ _ _ => eapply dexpr_bool3_ltu
  | |- dexpr1 _ _ (expr.var _)     _ _ => eapply dexpr1_var; [reflexivity| ]
  | |- dexpr1 _ _ (expr.literal _) _ _ => eapply dexpr1_literal
  | |- dexpr1 _ _ (expr.op _ _ _)  _ _ => eapply dexpr1_binop_unf
  | |- dexpr1 _ _ (expr.load access_size.word _)  _ _ => eapply dexpr1_load_uintptr
  | |- dexpr1 _ _ (expr.load _ _)  _ _ => eapply dexpr1_load_uint
  | |- dexprs1 _ _ (cons _ _) _ _ => eapply dexprs1_cons
  | |- dexprs1 _ _ nil _ _ => eapply dexprs1_nil
  | |- bool_expr_branches _ _ _ _ => eapply BoolSpec_expr_branches; [ intro | intro | ]
  | |- then_branch_marker ?G =>
      let n := fresh "Scope0" in
      pose proof (mk_scope_marker ThenBranch) as n;
      change G
  | |- else_branch_marker ?G =>
      let n := fresh "Scope0" in
      pose proof (mk_scope_marker ElseBranch) as n;
      change G
  | |- pop_scope_marker (after_loop ?fs ?rest ?t ?m ?l ?post) =>
      lazymatch goal with
      | H: scope_marker LoopBody |- pop_scope_marker ?g => clear H; change g
      end
  | |- pop_scope_marker (after_if _ _ _ _ _ _) =>
      lazymatch goal with
      | H: scope_marker IfCondition |- pop_scope_marker ?g => clear H; change g
      end
  | |- True => constructor
  | |- wp_cmd _ _ _ _ (map.put ?l ?x ?v) _ => put_into_current_locals
  | |- iff1 (seps ?LHS) (seps ?RHS) =>
      first
        [ constr_eq LHS RHS; exact (iff1_refl _)
        | cancel_step
        | cancel_emp_l
        | cancel_emp_r
        | lazymatch goal with
          | |- iff1 (seps (cons ?x nil)) _ => is_evar x
          | |- iff1 _ (seps (cons ?x nil)) => is_evar x
          end;
          cbn [seps];
          exact (iff1_refl _) ]
  | |- dlet _ (fun x => _) => eapply let_to_dlet; make_fresh x; intro x
  | |- forall t' m' (retvs: list ?word),
      _ -> exists l', map.putmany_of_list_zip _ retvs ?l = Some l' /\ wp_cmd _ _ _ _ _ _
    => (* after a function call *)
      let retvsname := fresh retvs in
      intros ? ? retvsname (? & ? & ?);
      subst retvsname
  | |- exists (l: @map.rep String.string (@word.rep _ _) _),
         map.putmany_of_list_zip _ _ _ = Some _ /\ _ =>
      eexists; split; [reflexivity| ]
  | |- @eq (@map.rep string (@word.rep _ _) _) (map.of_list _) (map.of_list _) =>
      (* doesn't make the goal unprovable because we keep tuple lists passed
         to map.of_list sorted by key, and all values in the key-value tuples
         are variables or evars *)
      repeat f_equal
  | |- _ => first
      [ cleanup_step
      | progress autounfold with live_always_unfold in *
      | lazymatch goal with
        | |- exists _, _ => eexists
        end
      | progress simpl_hook
      | match goal with
        (* We try ZnWords first because it also solves some goals of shape
           (_ = _) and (_ /\ _) *)
        | |- _ => ZnWords (* TODO replace by better/faster tactic *)
        | |- _ = _ => eq_prover_hook
        | |- ?P /\ ?Q => split
        | |- wp_cmd _ _ _ _ _ _ =>
              lazymatch goal with
              | |- ?G => change (@ready G)
              end
        end ]
  end.

(* needs to run before merging because before merging, some interesting hypotheses
   are exposed that will get purified into useful facts to prove sideconditions *)
Ltac program_logic_step_before_merging :=
  match goal with
  | |- ?P /\ _ =>
      Lia.is_lia P;
      split;
      [ purify_heapletwise_hyps; try bottom_up_simpl_in_goal; Lia.lia | ]
  | |- _ => progress bottom_up_simpl_in_hyps (* TODO too expensive to run so early *)
  end.

Ltac step0 :=
  first [ heapletwise_step
        | program_logic_step_before_merging
        | split_merge_step
        | program_logic_step ].

Ltac step :=
  assert_no_error; (* <-- useful when debugging with `step. step. step. ...` *)
  step0.

Ltac step_is_done :=
  lazymatch goal with
  | |- @ready _ => idtac
  | |- @final_postcond_marker _ => idtac
  | |- don't_know_how_to_prove_equal _ _ => idtac
  | |- after_if _ _ _ _ _ _ => idtac
  | |- after_loop _ _ _ _ _ _ => idtac
  end.

Ltac run_steps :=
  lazymatch goal with
  | _: tactic_error _ |- _ => idtac
  | |- _ => tryif step_is_done then idtac
            else tryif step then run_steps
            else pose_err Error:("The 'step' tactic should not fail here")
  end.

(* can be overridden with idtac for debugging *)
Ltac run_steps_hook := run_steps.

Ltac next_snippet s :=
  assert_no_error;
  lazymatch goal with
  | |- after_if _ _ ?Q1 ?Q2 _ _ => after_if_cleanup; run_steps_hook
  | |- after_loop ?fs ?rest ?t ?m ?l ?post => after_loop_cleanup; run_steps_hook
  | |- _ => idtac
  end;
  add_snippet s;
  run_steps_hook.

Tactic Notation ".*" constr(s) "*" := next_snippet s.

(* optional "end if." comment after closing brace, triggers unpacking of merged
   then/else postcondition *)
Tactic Notation "end" "if" := after_if_cleanup; run_steps_hook.

(* optional "end while." comment after closing brace, triggers some cleanup *)
Tactic Notation "end" "while" := after_loop_cleanup; run_steps_hook.

(* for situations where we want to avoid repeating the function name *)
Notation fnspec := (ProgramLogic.spec_of _) (only parsing).

(* To work around https://github.com/coq/coq/issues/7903
   Notations with binders and inline ltac:() don't work, so if the RHS of
   a notation is b and contains binders as well as an occurrence of `ident_to_string x`
   (which expands to ltac:()), we get errors that the binders are not found.
   So instead of writing b, we can write (fun x: string => b) and replace
   `ident_to_string x` by x in b, and then pass (fun x: string => b) to
   with_ident_as_string, which reverts that replacement, ie it turns
   (fun x: string => b) back into `b["x"/x]`. *)
Ltac with_ident_as_string f :=
  lazymatch f with
  | fun x => _ => beta1 f (ident_to_string x)
  end.

(* same as above, but without beta1, beta1 removes casts *)
Ltac with_ident_as_string_no_beta f :=
  lazymatch f with
  | fun x => _ => constr:(f (ident_to_string x))
  end.

(* Notations have (almost) the same RHS as the `fnspec!` notations in
   bedrock2.WeakestPrecondition, but only allow 0 or 1 return value
   (for C compatibility) and use a different syntax in the LHS (to match
   C syntax and live verif comment markers) *)

Declare Custom Entry funspec.

(* One return value: *)
Notation "'uintptr_t' fname ( 'uintptr_t' a1 , 'uintptr_t' .. , 'uintptr_t' an ) /**# 'ghost_args' := g1 .. gn ; 'requires' t1 m1 := pre ; 'ensures' t2 m2 r := post #* */ /* *" :=
  (fun fname: String.string =>
     (fun fs =>
        (forall a1, .. (forall an, (forall g1, .. (forall gn,
           (forall t1 m1, pre ->
              WeakestPrecondition.call fs fname t1 m1
                (@cons (@word.rep _ _) a1 .. (@cons (@word.rep _ _) an nil) ..)
                (fun t2 m2 retvs => exists r, retvs = cons r nil /\ post))) .. )) .. ))
     : ProgramLogic.spec_of fname)
(in custom funspec at level 1,
 fname name,
 a1 closed binder, an closed binder,
 g1 closed binder, gn closed binder,
 t1 name, t2 name, m1 name, m2 name, r name,
 pre constr at level 200,
 post constr at level 200,
 only parsing).

(* No return value: *)
Notation "'void' fname ( 'uintptr_t' a1 , 'uintptr_t' .. , 'uintptr_t' an ) /**# 'ghost_args' := g1 .. gn ; 'requires' t1 m1 := pre ; 'ensures' t2 m2 := post #* */ /* *" :=
  (fun fname: String.string =>
     (fun fs =>
        (forall a1, .. (forall an, (forall g1, .. (forall gn,
           (forall t1 m1, pre ->
              WeakestPrecondition.call fs fname t1 m1
                (@cons (@word.rep _ _) a1 .. (@cons (@word.rep _ _) an nil) ..)
                (fun t2 m2 retvs => retvs = nil /\ post))) .. )) .. ))
     : ProgramLogic.spec_of fname)
(in custom funspec at level 1,
 fname name,
 a1 closed binder, an closed binder,
 g1 closed binder, gn closed binder,
 t1 name, t2 name, m1 name, m2 name,
 pre constr at level 200,
 post constr at level 200,
 only parsing).

Notation ".* */ x" :=
  (match x with (* <-- typecheck x before passing it to Ltac, to get better error messages *)
   | _ => ltac:(let r := with_ident_as_string_no_beta x in exact r)
   end)
  (at level 200, x custom funspec at level 1, only parsing).

Notation "'fun_correct!' f" := (program_logic_goal_for (ident_to_string f) f)
  (at level 10, f name, only parsing).

Notation ".* */ //" := True (only parsing).
