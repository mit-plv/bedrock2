Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.micromega.Lia.
Require Import coqutil.Z.Lia.
Require Import Coq.Strings.String.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Map.Interface coqutil.Map.Properties.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import coqutil.Tactics.foreach_hyp.
Require Import coqutil.Tactics.grepeat.
Require Import coqutil.Tactics.pattern_tuple.
Require Import coqutil.Datatypes.RecordSetters.
Require Import bedrock2.Syntax bedrock2.Semantics.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic bedrock2.Array.
Require Import bedrock2.unzify.
Require Import bedrock2.Scalars.
Require Import bedrock2.TacticError. Local Open Scope Z_scope.
Require Import bedrock2.SuppressibleWarnings.
Require Import LiveVerif.string_to_ident.
Require Import bedrock2.find_hyp.
Require Import bedrock2.ident_to_string.
Require Import bedrock2.HeapletwiseHyps.
Require Import bedrock2.HeapletwiseAutoSplitMerge.
Require Import bedrock2.SepLib.
Require Import bedrock2.sepapp.
Require Import bedrock2.canceling_sepapps.
Require Import bedrock2.PurifySep.
Require Import bedrock2.PurifyHeapletwise.
Require Import bedrock2.bottom_up_simpl.
Require Import bedrock2.safe_implication.
Require Import bedrock2.ZListEqProver.
Require Import bedrock2.to_from_anybytes.
Require Import bedrock2.syntactic_f_equal_with_ZnWords.
Require Import coqutil.Tactics.ident_ops.
Require Import bedrock2.Logging.
Require Import LiveVerif.LiveRules.
Require Import LiveVerif.PackageContext.
Require Import LiveVerif.LiveSnippet.
Require Import bedrock2.LogSidecond.

Definition functions_correct
  (* universally quantified abstract function list containing all functions: *)
  (qfs: Semantics.env):
  (* specs of a subset of functions for which to assert correctness *)
  list (Semantics.env -> Prop (* spec_of mentioning function name *)) -> Prop :=
  List.Forall (fun spec => spec qfs).

Definition function_with_callees: Type :=
  func * list (Semantics.env -> Prop (* spec_of mentioning function name *)).

Definition program_logic_goal_for(name: string)(f: function_with_callees)
  {spec: bedrock2.ProgramLogic.spec_of name}: Prop :=
  match f with
  | (impl, callees) => forall functions,
      map.get functions name = Some impl ->
      functions_correct functions callees ->
      spec functions
  end.

Definition nth_spec(specs: list (Semantics.env -> Prop))(n: nat) :=
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

(* State container, defined in such a way that updating the state doesn't affect or grow
   the proof term.
   Lives in Prop because some tactics might clear all non-Props. *)
Definition currently(contents: Type) := True.

Ltac pose_state s :=
  let n := fresh "state" in
  pose proof (I : currently s) as n;
  move n at top.

Ltac get_state :=
  lazymatch reverse goal with
  | state: currently ?s |- _ => s
  end.

Ltac set_state s :=
  lazymatch reverse goal with
  | state: currently _ |- _ => change (currently s) in state
  end.

Inductive displaying: Type :=.
Inductive stepping: Type :=.

Definition ready{P: Prop} := P.

(* heapletwise- and word-aware lia, successor of ZnWords *)
Ltac hwlia := zify_hyps; puri_simpli_zify_hyps true; zify_goal; xlia zchecker.

Ltac2 Set bottom_up_simpl_sidecond_hook := fun _ => ltac1:(zify_goal; xlia zchecker).

Ltac word_lia_hook_for_split_merge ::= zify_goal; xlia zchecker.

Ltac intros_until_trace :=
  repeat lazymatch goal with
    | |- forall (_: trace), _ => fail (* done *)
    | |- forall _, _ => intros ?
    end.

Ltac print_stats f := f ltac_identity.
Ltac don't_print_stats f := idtac.

(* use ::= to set _stats to print_stats or don't_print_stats *)
Ltac _stats := don't_print_stats.

Tactic Notation "stats" tactic0(f) := _stats f.

(* used by bedrock2.LogSidecond, which is used to log simplifications by bottom_up_simpl: *)
#[export] Hint Extern 1 (SidecondIrrelevant (with_mem _ _)) =>
  constructor : typeclass_instances.
#[export] Hint Extern 1 (SidecondIrrelevant (scope_marker _)) =>
  constructor : typeclass_instances.
#[export] Hint Extern 1 (SidecondIrrelevant (currently _)) =>
  constructor : typeclass_instances.
#[export] Hint Extern 1 (SidecondIrrelevant (ext_spec.ok _)) =>
  constructor : typeclass_instances.
#[export] Hint Extern 1 (SidecondIrrelevant (DisjointUnion.mmap.du _ _ = _)) =>
  constructor : typeclass_instances.
#[export] Hint Extern 1 (SidecondIrrelevant (functions_correct _ _)) =>
  constructor : typeclass_instances.
#[export] Hint Extern 1 (SidecondIrrelevant (merge_step _)) =>
  constructor : typeclass_instances.
#[export] Hint Extern 1 (SidecondIrrelevant (fold_step _)) =>
  constructor : typeclass_instances.

Ltac pre_log_simpl_hook ::= unzify.

Ltac start :=
  lazymatch goal with
  | |- @program_logic_goal_for ?fname ?evar ?spec =>
      stats (fun _ => idtac "Stats: START" fname; idtac "Stats: SNIPPET");
      lazymatch open_constr:((_, _): function_with_callees) with
      | ?p => unify evar p
      end;
      subst evar;
      (* strip implicit arguments if spec was defined in another file *)
      let spec_head := head spec in
      unfold program_logic_goal_for, spec_head;
      let fs := fresh "fs" in
      let G := fresh "EnvContains" in
      let fs_ok := fresh "fs_ok" in
      intros fs G fs_ok;
      let nP := fresh "Scope0" in pose proof (mk_scope_marker FunctionParams) as nP;
      intros_until_trace;
      let nB := fresh "Scope0" in pose proof (mk_scope_marker FunctionBody) as nB;
      lazymatch goal with
      | |- forall (t : trace) (m : @map.rep (@word.rep _ _) Init.Byte.byte _), _ => intros
      end;
      eapply prove_func;
      [ exact G
      | lazymatch goal with
        | |- map.of_list_zip ?argnames_evar ?argvalues = Some ?locals_evar =>
             let argnames := map_with_ltac varconstr_to_string argvalues in
             unify argnames_evar argnames;
             let kvs := eval unfold List.combine in (List.combine argnames argvalues) in
             unify locals_evar (map.of_list kvs);
             reflexivity
        end
      | clear G ];
      first [eapply simplify_no_return_post | eapply simplify_1retval_post];
      pose_state stepping
  | |- _ => fail "goal needs to be of shape (@program_logic_goal_for ?fname ?evar ?spec)"
  end.

Ltac is_function_param x :=
  lazymatch goal with
  | p: scope_marker FunctionParams, b: scope_marker FunctionBody |- _ =>
      ident_is_above p x; ident_is_above x b
  | _ => fail 1000 "could not find FunctionParams and FunctionBody scope_marker"
  end.

Ltac is_in_snd x ps :=
  lazymatch ps with
  | (_, x) :: _ => idtac
  | _ :: ?rest => is_in_snd x rest
  | nil => fail "not found"
  | _ => fail 1000 ps "is not a concrete enough list"
  end.

Ltac put_into_current_locals :=
  lazymatch goal with
  | |- update_locals ?ks ?vs _ _ => try subst vs
  end;
  lazymatch goal with
  | |- update_locals nil nil ?l ?post => unfold update_locals
  | |- update_locals (cons ?x nil) (cons ?v nil) ?l ?post =>
      let i := string_to_ident x in
      make_fresh i;
      (* match again because there might have been a renaming *)
      lazymatch goal with
      | |- update_locals (cons ?x nil) (cons ?v nil) ?l ?post =>
          let tuples := lazymatch l with map.of_list ?ts => ts end in
          tryif (
              is_var v;
              assert_fails (idtac; is_function_param v); (* not a ghost or non-ghost arg *)
              assert_fails (idtac; is_in_snd v tuples) (* not a local program variable *))
          then (* we can rename v into i instead of creating a new variable & equation *)
            (rename v into i; unfold update_locals)
          else
            (eapply update_one_local_eq; intro_word i; let h := fresh "Def0" in intro h)
      end;
      normalize_locals_wp
  | |- update_locals ?ks ?vs _ _ => fail 1000 "update_locals for" ks "and" vs "not supported"
  end.

Ltac clear_until_LoopInvOrPreOrPost_marker :=
  repeat match goal with
         | x: ?T |- _ => lazymatch T with
                         | scope_marker LoopInvOrPreOrPost => fail 1
                         | _ => clear x
                         end
         end;
  match goal with
  | x: ?T |- _ => lazymatch T with
                  | scope_marker LoopInvOrPreOrPost => clear x
                  | _ => fail "call 'loop invariant above my_var.' before the loop"
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

Import Ltac2.Ltac2. Set Default Proof Mode "Classic".

Ltac2 filtered_bottom_up_simpl_in_hyp_of_type(h: ident)(t: constr): unit :=
  if Ident.starts_with @__ h then () else
    lazy_match! t with
    | functions_correct _ _ => ()
    | _ => bottom_up_simpl_in_hyp_of_type silent_if_no_progress h t
    end.

Ltac bsimpl_in_hyps := ltac2:(foreach_hyp filtered_bottom_up_simpl_in_hyp_of_type).

Ltac default_simpl_in_hyps := bsimpl_in_hyps; try record.simp_hyps.

Ltac default_simpl_in_all :=
  default_simpl_in_hyps; bottom_up_simpl_in_goal_nop_ok; try record.simp_goal.

Ltac after_command_simpl_hook := default_simpl_in_hyps.

(* Some ingredients for proving postconditions at end of blocks,
   too expensive in general, but useful when applied carefully. *)

Ltac destruct_lists_of_concrete_nat_length :=
  repeat match goal with
           | H: List.length ?l = S _ |- _ =>
               is_var l; destruct l;
               [ discriminate H
               | cbn [List.length] in H; eapply Nat.succ_inj in H ]
           | H: List.length ?l = O |- _ =>
               is_var l; destruct l;
               [ clear H
               | discriminate H ]
           end.

Ltac subst_all_let_bound_vars :=
  repeat match goal with
    | x := _ |- _ => subst x
    end.

Ltac destruct_ands_list :=
    repeat match goal with
           | H: ands (_ :: _) |- _ => destruct H
           | H: ands nil |- _ => clear H
           end.

Ltac destruct_ors :=
  repeat match goal with
    | H: ?P \/ ?Q |- _ => tryif (is_lia P; is_lia Q) then fail else destruct H
    end.

Create HintDb prove_post.

Ltac ret retexpr :=
  lazymatch goal with
  | B: scope_marker ?sk |- _ =>
      lazymatch sk with
      | FunctionBody => idtac
      | ThenBranch => idtac
      | ElseBranch => idtac
      | _ => fail "return inside a" sk "is not supported"
      end
  | |- _ => fail "block structure lost (could not find a scope_marker)"
  end;
  cbv beta;
  let P := lazymatch goal with
           | |- wp_cmd ?fs _ _ _ _ (fun t m l => expect_1expr_return ?P t m _) => P
           | |- wp_cmd ?fs _ _ _ _ (expect_1expr_return ?P) => P
           | |- _ => fail "return at this position is not supported"
           end in
  eapply (wp_return _ retexpr _ _ _ _ _ P _); [ reflexivity | reflexivity | ].

Ltac strip_conss l :=
  lazymatch l with
  | cons _ ?t => strip_conss t
  | _ => l
  end.

Ltac package_heapletwise_context :=
  collect_heaplets_into_one_sepclause;
  package_context.

Ltac close_function :=
  lazymatch goal with
  | H: functions_correct ?fs ?l |- _ =>
      let T := lazymatch type of l with list ?T => T end in
      let e := strip_conss l in
      unify e (@nil T)
  end.

Ltac close_block :=
  lazymatch goal with
  | B: scope_marker ?sk |- _ =>
      eapply wp_skip;
      lazymatch sk with
      | ThenBranch => idtac
          (* TODO would be better to fail already here rather than only when
             trying to do `else {`, but that requires needs_to_be_closed_by_single_rbrace
             to be used in such a way that it doesn't interfere with expect_1expr_return
          lazymatch goal with
          | |- needs_to_be_closed_by_single_rbrace ?g => change g
          | |- _ => fail "this then-branch needs to be closed by '} else {'"
          end *)
      | ElseBranch => idtac
      | LoopBody => idtac
      | FunctionBody => close_function
      | _ => fail "Can't end a block here"
      end;
      autounfold with heapletwise_always_unfold
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
  | (* one dexprs1 goal containing argument evaluation, precondition, and continuation
       after the call: *)
    lazymatch goal with
    | |- dexprs1 ?m ?l ?es ?vs (?calleePre /\ enable_frame_trick.enable_frame_trick ?cont) =>
        lazymatch calleePre with
        | context[m] => idtac (* default case: callee uses memory *)
        | _ => (* special case: callee does not use memory *)
            change (dexprs1 m l es vs (calleePre /\ cont))
        end
    end ].

(* Assigns default well_founded relations to types.
   Use lower costs to override existing entries. *)
Create HintDb wf_of_type.

#[export] Hint Resolve word.well_founded_lt_unsigned | 4 : wf_of_type.

Lemma Z_lt_downto_0_wf: well_founded (fun n m : Z => 0 <= n < m).
Proof. exact (Z.lt_wf 0). Qed.

#[export] Hint Resolve Z_lt_downto_0_wf | 4 : wf_of_type.

Ltac LoopInvOrPreOrPost_above i :=
  let n := fresh "Scope0" in pose proof (mk_scope_marker LoopInvOrPreOrPost) as n;
  move n after i.

Tactic Notation "loop" "invariant" "above" ident(i) := LoopInvOrPreOrPost_above i.
Tactic Notation "loop" "pre" "above" ident(i) := LoopInvOrPreOrPost_above i.

Ltac fix_local_names ksvs :=
  lazymatch ksvs with
  | cons (?s, ?v) ?rest =>
      let i := string_to_ident s in
      (tryif constr_eq i v then
          idtac (* nothing to do for v *)
        else
          (make_fresh i; rename v into i));
      fix_local_names rest
  | nil => idtac
  end.

Ltac clear_non_Props :=
  repeat match goal with
    | x: ?T |- _ =>
        lazymatch T with
        | _ => lazymatch type of T with
               | Prop => fail
               | _ => clear x
               end
        end
    end.

Ltac start_loop_body :=
  repeat match goal with
    | H: sep _ _ ?M |- _ => clear M H
    end;
  clear_until_LoopInvOrPreOrPost_marker;
  (* Note: will also appear after loop, where we'll have to clear it,
     but we have to pose it here because the foralls are shared between
     loop body and after the loop *)
  (let n := fresh "Scope0" in pose proof (mk_scope_marker LoopBody) as n);
  cbv beta zeta iota;
  intros *;
  clear_non_Props;
  repeat lazymatch goal with
  | |- (match ?p with (x, y) => _ end) -> _ =>
      let n1 := fresh x in
      let n2 := fresh y in
      destruct p as [n1 n2]
  end;
  intros;
  unpackage_context;
  lazymatch goal with
  | |- exists b, dexpr_bool3 _ (map.of_list ?ksvs) _ b _ _ _ =>
      fix_local_names ksvs;
      eexists
  | |- loop_body_marker (exec _ _ _ _ (map.of_list ?ksvs) _) =>
      fix_local_names ksvs
  | |- _ => fail "assertion failure: hypothesis of loop lemma has unexpected shape"
  end.

Ltac while cond measure0 :=
  eapply (wp_while measure0 cond);
  [ package_heapletwise_context
  | eauto with wf_of_type
  | start_loop_body ].

Ltac while_tailrec_use_functionpost cond ghosts0 measure0 :=
  lazymatch goal with
  | |- exec ?fs ?body ?t ?m ?l ?P =>
      let P' := eval pattern measure0 in P in change (exec fs body t m l P')
  end;
  lazymatch goal with
  | |- exec ?fs ?body ?t ?m ?l (?P ?v0) =>
      let P' := pattern_tuple_in_term P ghosts0 in
      change (exec fs body t m l (P' v0))
  end;
  eapply (wp_while_tailrec_use_functionpost measure0 ghosts0 cond);
  [ eauto with wf_of_type
  | package_heapletwise_context
  | start_loop_body ].

Ltac dowhile measure0 :=
  eapply (wp_dowhile measure0);
  [ package_heapletwise_context
  | eauto with wf_of_type
  | start_loop_body ].

Ltac dowhile_tailrec_use_functionpost ghosts0 measure0 :=
  lazymatch goal with
  | |- exec ?fs ?body ?t ?m ?l ?P =>
      let P' := eval pattern measure0 in P in change (exec fs body t m l P')
  end;
  lazymatch goal with
  | |- exec ?fs ?body ?t ?m ?l (?P ?v0) =>
      let P' := pattern_tuple_in_term P ghosts0 in
      change (exec fs body t m l (P' v0))
  end;
  eapply wp_dowhile_tailrec_use_functionpost with (g0 := ghosts0) (v0 := measure0);
  [ eauto with wf_of_type
  | package_heapletwise_context
  | start_loop_body ].

Ltac end_dowhile e :=
  lazymatch goal with
  (* from hypothesis of do-while lemma: *)
  | |- exec _ _ ?t ?m ?l (fun t' m' l' =>
     exists b, dexpr_bool3 _ _ ?condEvar _ _ _ _) => unify condEvar e
  end;
  close_block.

Ltac _new_ghosts g :=
  lazymatch goal with
  | |- provide_new_ghosts (fun _: ?G => _) =>
      let expected := prod_size G in
      let actual := pair_size g in
      tryif constr_eq actual expected
      then eexists g
      else let expected := eval cbv in (Z.of_nat expected) in
           let actual := eval cbv in (Z.of_nat actual) in
           fail "Expected" expected "ghosts, but got" actual
  end.

Tactic Notation "new_ghosts" open_constr(g) := _new_ghosts g.

Ltac guess_new_ghosts :=
  lazymatch goal with
  | |- provide_new_ghosts ?g => change (ex g)
  end.

Ltac manual_new_ghosts := fail.

(* Can be overridden to guess_new_ghosts or manual_new_ghosts *)
Ltac provide_new_ghosts_hook := guess_new_ghosts.

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
      | true => isnt_local_var name; eapply (wp_unset_at_end _ name)
      | false => is_local_var name
      end;
      lazymatch rhs with
      | RCall ?fname ?arges => call (Some (is_decl, name)) fname arges
      | RExpr ?e => eapply (wp_set _ name e)
      end
  | SVoidCall ?fname ?arges => call (@None (prod bool string)) fname arges
  | SStore access_size.word ?addr ?val => eapply (wp_store_uintptr _ addr val)
  | SStore ?sz ?addr ?val => eapply (wp_store_uint _ sz addr val)
  | SIf ?c ?spl =>
      lazymatch spl with
      | true => eapply (wp_if_bool_dexpr_split _ c)
      | false => eapply (wp_if_bool_dexpr _ c)
      end;
      let n := fresh "Scope0" in
      pose proof (mk_scope_marker IfCondition) as n
  | SElse ?startsWithClosingBrace =>
      lazymatch startsWithClosingBrace with
      | true =>
          assert_scope_kind ThenBranch;
          eapply wp_skip (* leaves a branch_post marker to be taken care of by step *)
      | false =>
          lazymatch goal with
          | |- needs_opening_else_and_lbrace ?g => change g
          | |- _ => fail "'else' is not expected here"
          end
      end
  | SWhile ?cond ?measure0 => while cond measure0
  | SWhileTailrec ?cond ?g0 ?m0 => while_tailrec_use_functionpost cond g0 m0
  | SDo ?measure0 => dowhile measure0
  | SDoTailrec ?ghosts0 ?measure0 => dowhile_tailrec_use_functionpost ghosts0 measure0
  | SEndDo ?c => end_dowhile c
  | SStart => fail "SStart can only be used to start a function"
  | SEnd => close_block
  | SRet ?retexpr => ret retexpr
  | SEmpty => idtac
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

(* Can be customized with ::= *)
Ltac is_substitutable_rhs_cleanup rhs :=
  first [ is_var rhs
        | is_const rhs
        | lazymatch isZcst rhs with true => idtac end
        | lazymatch rhs with
          | word.of_Z ?x => is_substitutable_rhs_cleanup x
          | word.unsigned ?x => is_substitutable_rhs_cleanup x
          end ].

Ltac cleanup_step :=
  match goal with
  | x := ?rhs |- _ => is_substitutable_rhs_cleanup rhs; subst_unless_local_var x
  | x := _ |- _ => clear x
  | _: ?x = ?y |- _ =>
      first [ is_var x; is_substitutable_rhs_cleanup y; subst_unless_local_var x
            | is_var y; is_substitutable_rhs_cleanup x; subst_unless_local_var y ]
  | |- _ => progress fwd
  end.

Lemma eq_to_impl1[mem: Type]: forall (P Q: mem -> Prop), P = Q -> impl1 P Q.
Proof. intros. subst. reflexivity. Qed.

Lemma eq_to_iff1[mem: Type]: forall (P Q: mem -> Prop), P = Q -> iff1 P Q.
Proof. intros. subst. reflexivity. Qed.

Ltac turn_relation_into_eq :=
  lazymatch goal with
  | |- _ = _ => idtac
  | |- impl1 _ _ => eapply eq_to_impl1
  | |- iff1 _ _ => eapply eq_to_iff1
  end.

Ltac default_careful_reflexivity_step :=
  match goal with
  | |- _ ?l ?r => is_evar l; reflexivity
  | |- _ ?l ?r => is_evar r; reflexivity
  | |- _ ?l ?r => constr_eq l r; reflexivity
  | |- _ => bottom_up_simpl_in_goal (* fails if nothing to simplify *)
  | |- _ => record.simp_goal (* fails if nothing to simplify *)
  | |- _ (sepapps nil _) (sepapps nil _) => reflexivity
  | |- _ (sepapps (cons _ _) _) (sepapps (cons _ _) _) =>
      turn_relation_into_eq; eapply f_equal2
  | |- _ (sepapps _ _) ?rhs =>
      let h := head rhs in
      unfold h;
      lazymatch goal with
      | |- _ (sepapps _ _) (sepapps _ _) => idtac
      end
  | |- _ ?lhs (sepapps _ _) =>
      let h := head lhs in
      unfold h;
      lazymatch goal with
      | |- _ (sepapps _ _) (sepapps _ _) => idtac
      end
  | |- eq (uintptr _) (uintptr _) => eapply f_equal
  | |- eq (uint ?nbits _) (uint ?nbits _) => eapply f_equal
  | |- _ ?l ?r => subst l
  | |- _ ?l ?r => subst r
  | |- _ => turn_relation_into_eq; syntactic_f_equal_with_ZnWords
  | |- @eq (list _) _ _ => list_eq_step
  | |- ?rel (?pred1 ?val1 ?addr1) (?pred2 ?val2 ?addr2) =>
      is_evar val2;
      (* When is it safe to instantiate the evar val2 with val1?

         Note: We assume a "unique value property": in (pred val addr), given pred
         and addr and a heaplet on which this clause holds, only one val is possible.
         This property holds as long as there is an abstraction function (rather than
         relation) from memory to high-level values.

         Note: The hyp_clause_matches_goal_clause in HeapletwiseHyps complements
         the code here: Since it doesn't split the proof into several steps, it can
         afford to instantiate evars a bit more aggressively: If everything matches
         syntactically (up to instantiating evars in the conclusion), it goes ahead
         and instantiates the evars.
         On the other hand, here we proceed step by step, and don't want to risk
         turning a provable "uint8 array implies uint32 array" goal into an unprovable
         goal by instantiating the list in the conclusion with the list of the hyp,
         and generating unprovable side conditions that uint8=uint32 and size1=size2. *)
      lazymatch rel with
      | @impl1 _ => idtac
      | @iff1 _ => idtac
      end;
      lazymatch pred2 with
      | pred1 => idtac
      | array ?elem ?sz2 =>
          lazymatch pred1 with
          | array elem ?sz1 =>
              assert_fails (idtac; has_evar sz1);
              assert_fails (idtac; has_evar sz2)
          end
      end;
      unify val2 val1
  end.

(* supposed to work on goals of the form (?rel ?lhs ?rhs), with rel being on of
   eq, impl1, iff1 *)
Ltac careful_reflexivity_step_hook := default_careful_reflexivity_step.

Ltac eval_dexpr_bool3_step e :=
  lazymatch e with
  | expr.lazy_and _ _       => eapply dexpr_bool3_lazy_and
  | expr.lazy_or _ _        => eapply dexpr_bool3_lazy_or
  | expr.not _              => eapply dexpr_bool3_not
  | expr.op bopname.eq _ _  => eapply dexpr_bool3_eq
  | expr.op bopname.ltu _ _ => eapply dexpr_bool3_ltu
  | expr.var _              => eapply dexpr_bool3_to_dexpr1
  | _ => fail 1000 "expression" e "not yet supported"
  end.

Ltac eval_dexpr1_step e :=
  lazymatch e with
  | expr.var _ => eapply dexpr1_var; [reflexivity| ]
  | expr.literal _ => eapply dexpr1_literal
  | expr.op _ _ _ => eapply dexpr1_binop_unf
  | expr.load access_size.word _ => eapply dexpr1_load_uintptr
  | expr.load _ _ => eapply dexpr1_load_uint
  | LiveExpr.deref access_size.word _ => eapply dexpr1_deref_uintptr
  | LiveExpr.deref _ _ => eapply dexpr1_deref_uint
  end.

Lemma eq_if_same{A: Type}(c: bool)(lhs rhs: A)(H: lhs = if c then rhs else rhs): lhs = rhs.
Proof. intros. destruct c; exact H. Qed.

Ltac clear_mem_split_eqs :=
  repeat match goal with
    | H: _ = DisjointUnion.mmap.Def _ |- _ => clear H
    end.

Ltac clear_heaplets :=
  repeat match goal with
    | m: @map.rep (@word.rep _ _) Coq.Init.Byte.byte _ |- _ => clear m
    end.

Ltac clear_traces :=
  repeat match goal with
    | t: trace |- _ => clear t
    end.

Ltac is_ground_string s :=
  lazymatch s with
  | String.EmptyString => idtac
  | String.String (Ascii.Ascii _ _ _ _ _ _ _ _) ?t => is_ground_string t
  | _ => fail 1000 s
  end.

Ltac is_tuple_list_with_ground_keys kvs :=
  lazymatch kvs with
  | cons (?s, _) ?rest => is_ground_string s; is_tuple_list_with_ground_keys rest
  | nil => idtac
  end.

Ltac is_map_expr_with_ground_keys l :=
  lazymatch l with
  | map.of_list ?kvs => is_tuple_list_with_ground_keys kvs
  | map.remove ?l' ?k => is_ground_string k; is_map_expr_with_ground_keys l'
  | map.put ?l' ?k _ => is_ground_string k; is_map_expr_with_ground_keys l'
  end.

Lemma contradictory_branch(B Q: Prop): ~ B -> B -> Q.
Proof. intuition idtac. Qed.

Ltac conclusion_shape_based_step logger :=
  lazymatch goal with
  | |- dexpr_bool3 _ _ ?e _ _ _ _ =>
      logger ltac:(fun _ => idtac "Evaluating expression" e);
      eval_dexpr_bool3_step e
  | |- dexpr1 _ _ ?e _ _ =>
      logger ltac:(fun _ => idtac "Evaluating expression" e);
      eval_dexpr1_step e
  | |- dexprs1 _ _ (cons _ _) _ _ =>
      logger ltac:(fun _ => idtac "Evaluating expression list");
      eapply dexprs1_cons
  | |- dexprs1 _ _ nil _ _ =>
      logger ltac:(fun _ => idtac "Done evaluating expression list");
      eapply dexprs1_nil
  | |- bool_expr_branches _ _ _ _ =>
      logger ltac:(fun _ => idtac "Splitting bool_expr_branches");
      eapply BoolSpec_expr_branches;
      [ first [ eapply contradictory_branch; zify_goal; xlia zchecker
              | intro ] .. | ]
  | |- then_branch_marker ?G =>
      logger ltac:(fun _ => idtac "Starting `then` branch");
      let n := fresh "Scope0" in
      pose proof (mk_scope_marker ThenBranch) as n;
      change G
  | |- else_branch_marker ?G =>
      logger ltac:(fun _ => idtac "Starting `else` branch");
      let n := fresh "Scope0" in
      pose proof (mk_scope_marker ElseBranch) as n;
      change G
  | |- package_context_marker ?Q ?t ?m ?l =>
      logger ltac:(fun _ => idtac "package_heapletwise_context");
      let l' := normalize_locals_expr l in
      change (Q t m l');
      package_heapletwise_context
  | |- loop_body_marker ?G =>
      logger ltac:(fun _ => idtac "Starting loop body");
      (* (mk_scope_marker LoopBody) is already posed by while tactic,
         nothing to do here at the moment *)
      change G
  | |- pop_scope_marker (after_loop ?fs ?rest ?t ?m ?l ?post) =>
      logger ltac:(fun _ => idtac "after_loop cleanup");
      lazymatch goal with
      | H: scope_marker LoopBody |- pop_scope_marker ?g => clear H; change g
      end;
      unfold after_loop
  | |- pop_scope_marker (after_if _ _ _ _ _ _) =>
      logger ltac:(fun _ => idtac
         "Removing IfCondition marker after if and clearing outdated memory");
      lazymatch goal with
      | H: scope_marker IfCondition |- pop_scope_marker ?g => clear H; change g
      end;
      clear_mem_split_eqs;
      clear_heapletwise_hyps;
      clear_heaplets
  | |- pop_scope_marker (wp_cmd _ cmd.skip _ _ _ (fun _ _ _ => True)) =>
      logger ltac:(fun _ => idtac
         "Removing IfCondition marker after tail if");
      lazymatch goal with
      | H: scope_marker IfCondition |- pop_scope_marker ?g => clear H; change g
      end
  | |- True =>
      logger ltac:(fun _ => idtac "constructor");
      constructor
  | |- dlet _ (fun x => _) =>
      logger ltac:(fun _ => idtac "introducing dlet");
      eapply let_to_dlet; make_fresh x; intro x
  | |- merge_locals _ (cons (?x, ?v1) _) (cons (?x, ?v2) _) _ =>
      tryif constr_eq v1 v2; is_var v1 then (
        logger ltac:(fun _ => idtac "merge_locals with equal key/value on both sides");
        eapply merge_locals_same
      ) else (
        logger ltac:(fun _ => idtac "introducing local of merge_locals");
        let i := string_to_ident x in
        make_fresh i;
        intro_word i;
        let h := fresh "Def0" in
        intro h;
        repeat first [ rewrite push_if_into_arg1 in h | rewrite push_if_into_arg2 in h ]
      )
  | |- merge_locals _ nil nil _ =>
      logger ltac:(fun _ => idtac "merge_locals done");
      unfold merge_locals
  | |- forall t' m' (retvs: list ?word), _ -> update_locals _ retvs ?l _ =>
      logger ltac:(fun _ => idtac "intro new state after function call");
      intros
  | |- state_implication _ _ =>
      logger ltac:(fun _ => idtac "state_implication: clear old state and intro new state");
      clear_mem_split_eqs;
      clear_heapletwise_hyps;
      clear_heaplets;
      clear_traces;
      intros ? ? ?;
      lazymatch goal with
      | |- expect_1expr_return _ _ _ _ -> expect_1expr_return _ _ _ _ =>
          let hGet := fresh in
          intros [? hGet ?];
          eapply mk_expect_1expr_return; [exact hGet | clear hGet]
      | |- _ => intro
      end
  | |- packaged_mem_clause_marker ?p =>
      (* the point of this marker was to prevent start_canceling from including the
         stuff on the rhs of /\ in the "Rest" argument of canceling, but once we're
         here, `split` has run, so there's nothing to the right any more that needs
         to be prevented from being put into the "Rest" argument, so we can now
         remove this marker *)
      logger ltac:(fun _ => idtac "remove packaged_mem_clause_marker");
      change p
  | |- @eq (@map.rep string (@word.rep _ _) _) ?LHS ?RHS =>
      is_map_expr_with_ground_keys LHS;
      is_map_expr_with_ground_keys RHS;
      logger ltac:(fun _ => idtac "proving equality between two locals maps");
      let LHS' := normalize_locals_expr LHS in
      let RHS' := normalize_locals_expr RHS in
      change (LHS' = RHS');
      repeat f_equal
  | |- ands _ =>
      logger ltac:(fun _ => idtac "cbn [ands]");
      cbn [ands]
  end.

Lemma prove_if {Bt Bf b} {_: BoolSpec Bt Bf b} (Pt Pf: Prop):
  (Bt -> Pt) -> (Bf -> Pf) -> if b then Pt else Pf.
Proof. intros. destruct H; auto. Qed.

Ltac evar_tuple t :=
  lazymatch t with
  | prod ?t1 ?t2 =>
      let e1 := evar_tuple t1 in
      let e2 := evar_tuple t2 in
      constr:(pair e1 e2)
  | _ => lazymatch open_constr:(_ : t) with
         | ?e => e
         end
  end.

Require Import coqutil.Tactics.Records.
Require Import coqutil.Tactics.rdelta.

Ltac lambda_calls_getter_on_its_arg lam :=
  lazymatch lam with
  | (fun x: ?tp => _) =>
      let dummy := constr:(fun x: tp => ltac:(
        let body := eval cbv beta in (lam x) in
        match body with
        | context[?getter x] => is_getter getter; exact x
        end)) in
      idtac
  end.

Ltac composite_eexists t body :=
  let t := rdelta t in
  tryif lambda_calls_getter_on_its_arg body then
    refine (@ex_intro t _ (ltac:(constructor) : t) _); record.simp_goal
  else
    let e := evar_tuple t in exists e.

Ltac step_hook := fail.

Ltac sidecond_step logger := first
      [ lazymatch goal with
        | |- @ex ?A ?P => composite_eexists A P
        | |- @ex1 ?A _ ?P _ => composite_eexists A P
        | |- elet _ _ => refine (mk_elet _ _ _ eq_refl _)
        end;
        logger ltac:(fun _ => idtac "eexists")
      | (* tried first because it also solves some goals of shape (_ = _) and (_ /\ _) *)
        zify_goal; xlia zchecker;
        logger ltac:(fun _ => idtac "zify_goal; xlia zchecker")
      | safe_implication_step;
        logger ltac:(fun _ => idtac "safe_implication_step")
      | lazymatch goal with
        | H: _ \/ _ |- _ =>
            destruct H as [H | H]; try (exfalso; congruence);
            [ logger ltac:(fun _ => idtac "discarding contradictory branch of \/ in" H) ]
        end
      | lazymatch goal with
        | |- ?g =>
            is_destructible_and g;
            split;
            logger ltac:(fun _ => idtac "split")
        end
      | lazymatch goal with
        | |- _ = _ =>
            careful_reflexivity_step_hook;
            logger ltac:(fun _ => idtac "careful_reflexivity_step_hook")
        | |- impl1 ?lhs ?rhs =>
            first [ lazymatch lhs with
                    | sep _ _ => fail "not an atomic sep clause"
                    | _ => idtac
                    end;
                    lazymatch rhs with
                    | sep _ _ => fail "not an atomic sep clause"
                    | anyval _ _ =>
                        first [ eapply contiguous_implies_anyval_of_fillable;
                                [ solve [eauto with contiguous]
                                | solve [eauto with fillable] ];
                                logger ltac:(fun _ => idtac
                                         "contiguous_implies_anyval_of_fillable")
                              | (* if rhs is a sepapps (potentially behind definitions),
                                   `eauto with fillable` above failed, so we get here *)
                                eapply contiguous_implies_anyval_of_sepapps;
                                [ solve [eauto with contiguous]
                                | reflexivity (* relies on unification with unfolding,
                                                 let's hope it won't blow up... *)
                                | (* solved by further `step` invocations *) ];
                                logger ltac:(fun _ => idtac
                                         "contiguous_implies_anyval_of_sepapps") ]
                    | ?P ?e ?addr =>
                        is_evar e;
                        solve [ refine (contiguous_info_implies_proj1 _ _ _ _ _ _ _);
                                [ eauto with fillable
                                | eauto with contiguous ] ];
                        logger ltac:(fun _ => idtac
                                 "contiguous_implies_anyval_of_sepapps")
                    end
                  | (* goes last because it might wrap goal in don't_know_how_to_prove *)
                    careful_reflexivity_step_hook;
                    logger ltac:(fun _ => idtac "careful_reflexivity_step_hook") ]
        | |- iff1 _ _ =>
            careful_reflexivity_step_hook;
            logger ltac:(fun _ => idtac "careful_reflexivity_step_hook")
        | |- forall _, _ =>
            logger ltac:(fun _ => idtac "intro");
            intro (* don't put this too early, and only one intro at a time, because
                     heapletwise has a specialize intro that renames and moves new hyps *)
        end ].

(* means: already logged or tried to log *)
Inductive already_logged: Type := mk_already_logged.
Ltac clear_already_logged :=
  lazymatch goal with
  | H: already_logged |- _ => clear H
  | |- _ => idtac
  end.

Global Set Printing Depth 1000000.

Ltac log_goal :=
  lazymatch goal with
  | H: already_logged |- _ => idtac
  | |- if _ then _ else _ => idtac
  | |- wp_cmd _ _ _ _ _ _ => idtac
  | |- impl1 _ _ => idtac
  | |- context[@map.get] => idtac
  | |- context[@map.put] => idtac
  | |- context[@map.remove] => idtac
  | |- ?g =>
      let H := fresh "already_logged_marker" in pose proof mk_already_logged as H;
      (* make sure the goal is not too easy: *)
      tryif assert_fails (unzify; solve [intuition auto | congruence | lia])
      then
        tryif (assert_fails
          (assert g by (repeat (first [step_hook | sidecond_step ignore_logger_thunk]))))
        then
          (* goal not provable and we don't know if it's provable, so we don't log it *)
          idtac
        else
          (* solvable and not too easy: log *)
          assert_fails ((* to revert all effects *)
              idtac "<<<<<<";
              unzify;
              repeat lazymatch goal with
                | H: ?t |- _ =>
                    lazymatch t with
                    | already_logged => clear H
                    | with_mem _ _ => clear H
                    | scope_marker _ => clear H
                    | currently _ => clear H
                    | ExtSpec => clear H
                    | ext_spec.ok _ => clear H
                    | DisjointUnion.mmap.du _ _ = _ => clear H
                    | functions_correct _ _ => clear H
                    | _ => lazymatch type of t with
                           | Prop => revert H
                           | _ => clear H || revert H
                           end
                    end
                end;
              lazymatch goal with
              | |- ?g => idtac g; idtac ">>>>>>"
              end;
              fail)
      else idtac (* goal is too easy, not logging, but still succeeding so
                    that already_logged stays around *)
  end.

Ltac final_program_logic_step logger :=
  (* Note: Here, the logger has to be invoked *after* the tactic, because we only
     find out whether it's the right one by running it.
     To make sure that the logger is run exactly once, the thunk should only contain
     and idtac taking a string. *)
  first
      [ cleanup_step;
        logger ltac:(fun _ => idtac "cleanup_step")
      | (* Note: only invoked here because we first need to destruct /\ (done by
           cleanup_step) in hyps so that (retvs = [| ... |]) gets exposed *)
        put_into_current_locals;
        logger ltac:(fun _ => idtac "put_into_current_locals")
      | (*log_goal;*) sidecond_step logger
      | lazymatch goal with
        | |- if _ then _ else _ =>
            logger ltac:(fun _ => idtac "split if");
            eapply prove_if; intros; after_command_simpl_hook
        | |- wp_cmd _ _ _ _ _ _ =>
              lazymatch goal with
              | |- ?G => change (@ready G)
              end;
              after_command_simpl_hook;
              unzify;
              unpurify;
              set_state displaying;
              logger ltac:(fun _ => idtac "after_command_simpl_hook; unzify; unpurify")
        end ].

Ltac new_heapletwise_hyp_hook h t ::=
  puri_simpli_zify_hyp false h t.

Ltac heapletwise_hyp_pre_clear_hook H ::=
  let T := type of H in puri_simpli_zify_hyp false H T.

(* safe_to_cancel:
   An alternative mechanism to the range-based decisions on what's safe to cancel in
   HeapletwiseAutoSplitMerge.v.
   Needed if the size of the predicate is not yet known, eg the size could be
           match ?treeShape with
           | Leaf => 0
           | Node _ _ => 12
           end
*)

(* hypPred and conclPred are of type (word -> mem -> Prop) *)
Ltac predicates_safe_to_cancel_hook hypPred conclPred := fail.

(* hypPred and conclPred are of type (word -> mem -> Prop) *)
Ltac predicates_safe_to_cancel hypPred conclPred :=
  first
    [ predicates_safe_to_cancel_hook hypPred conclPred
    | lazymatch conclPred with
      | uintptr ?v2 => lazymatch hypPred with
                       | uintptr ?v1 => tryif is_evar v2 then unify v1 v2 else idtac
                       end
      | uint ?nbits ?v2 => lazymatch hypPred with
                           | uint nbits ?v1 =>
                               tryif is_evar v2 then unify v1 v2 else idtac
                           end
      | array ?elem ?n2 ?vs2 => lazymatch hypPred with
                                | array elem ?n1 ?vs1 =>
                                    assert_succeeds (idtac; assert (n1 = n2)
                                                       by (zify_goal; xlia zchecker));
                                    tryif is_evar vs2 then unify vs1 vs2 else idtac
                                end
      | sepapps nil => lazymatch hypPred with
                       | sepapps nil => idtac
                       end
      | sepapps (cons (mk_sized_predicate ?P2 ?Psize) ?rest2) =>
            lazymatch hypPred with
            | sepapps (cons (mk_sized_predicate ?P1 Psize) ?rest1) =>
               tryif constr_eq P1 P2 then idtac else predicates_safe_to_cancel P1 P2;
               predicates_safe_to_cancel (sepapps rest1) (sepapps rest2)
            end
      end ].

(* can instantiate evars in goalClause *)
Ltac is_safe_to_cancel hypClause goalClause :=
  tryif constr_eq hypClause goalClause then idtac else
  (* DON'T do
  lazymatch hypClause with
  | goalClause => idtac
  ... because it seems sometimes goalClause with evars matches hypClause without evars
      even though they are not constr_eq *)
  lazymatch hypClause with
  | ?pred1 ?addr1 =>
      lazymatch goalClause with
      | ?pred2 ?addr2 =>
          first [ constr_eq addr1 addr2
                | assert_succeeds (idtac; assert (addr1 = addr2)
                                     by (zify_goal; xlia zchecker)) ];
          predicates_safe_to_cancel pred1 pred2
      end
  end.

Ltac hyp_clause_matches_goal_clause hypClause goalClause ::=
  is_safe_to_cancel hypClause goalClause.

Ltac fwd_subst H ::= idtac.

Ltac heapletwise_step' logger :=
  first [heapletwise_step | cancel_sepapps_step];
  logger ltac:(fun _ => idtac "heapletwise_step").

Ltac sepclause_impl_step_hook ::= first [ step_hook | sidecond_step ignore_logger_thunk ].

Ltac split_step' logger :=
  split_step;
  logger ltac:(fun _ => idtac "split_step").

Ltac merge_step' logger :=
  (* match to make sure we don't merge too early, but only once the wp_cmd
     of the remainder of the program shows up *)
  lazymatch goal with
  | |- wp_cmd ?fs ?rest ?t ?m ?l ?post =>
      merge_step;
      logger ltac:(fun _ => idtac "merge_step")
  end.

Ltac step_hook' logger :=
  step_hook;
  logger ltac:(fun _ => idtac "step_hook").

Ltac undisplay logger :=
  lazymatch reverse goal with
  | _: currently ?s |- _ =>
      constr_eq s displaying;
      zify_hyps;
      puri_simpli_zify_hyps false;
      set_state stepping;
      logger ltac:(fun _ => idtac "purify & zify")
  end.

Ltac step0 logger0 :=
  let logger f :=
    stats (fun _ => idtac "Stats: STEP");
    logger0 f in
  first [ heapletwise_step' logger
        | conclusion_shape_based_step logger
        | undisplay logger
        | step_hook' logger
        | split_step' logger
        | merge_step' logger
        | final_program_logic_step logger ].

Ltac step :=
  assert_no_error; (* <-- useful when debugging with `step. step. step. ...` *)
  step0 run_logger_thunk.

Ltac step_silent := step0 ignore_logger_thunk.

Ltac can_continue :=
  assert_no_error;
  check_for_warnings_hook.

Ltac one_step :=
  lazymatch goal with
  | |- @ready _ => fail
  | |- after_if _ _ _ _ _ _ => fail
  | |- needs_opening_else_and_lbrace _ => fail
  | |- expect_1expr_return _ _ _ _ => fail
  | |- provide_new_ghosts _ => provide_new_ghosts_hook
  | _: tactic_error _ |- _ => fail
  | |- _ => step_silent
  end.

Ltac steps := can_continue; grepeat0 ltac:(fun _ => one_step).

(* find the first step that makes predicate succeed, ie run steps just until
   but without the first step that makes predicate succeed, so that this
   interesting step can then be debugged in isolation *)
Ltac _find_step predicate :=
  repeat (step; assert_fails (idtac; predicate tt)).
Tactic Notation "find_step" tactic0(predicate) := _find_step predicate.

Goal True = True /\ True.
  steps. (* test stats: should print 3 lines if stats are enabled *)
Abort.

(* If really needed, this hook can be overridden with idtac for debugging,
   but the preferred way is to use /*?. instead of /**. *)
Ltac run_steps_internal_hook := grepeat0 ltac:(fun _ => one_step).

Ltac add_snippet s :=
  lazymatch goal with
  | |- @ready _ => unfold ready; add_regular_snippet s
  | |- program_logic_goal_for _ _ =>
      lazymatch s with
      | SStart => start
      | _ => fail "expected {, but got" s
      end
  | |- after_if ?fs ?b ?PThen ?PElse ?c ?Post =>
      after_if_cleanup; run_steps_internal_hook; unfold ready; add_regular_snippet s
  | |- needs_opening_else_and_lbrace ?g =>
      lazymatch s with
      | SElse false => add_regular_snippet s
      | _ => fail "expected 'else {', but got" s
      end
  | |- _ => fail "can't add snippet in non-ready goal"
  end.

Ltac next_snippet s :=
  can_continue;
  stats (fun _ =>
           lazymatch s with
           | SStart => idtac (* don't print now because only start will print fname *)
           | _ => idtac "Stats: SNIPPET"
           end);
  add_snippet s.

(* Standard usage:   .**/ snippet /**.    *)
Tactic Notation ".*" constr(s) "*" := next_snippet s; run_steps_internal_hook.

(* Debug mode (doesn't run verification steps):   .**/ snippet /*?.   *)
Tactic Notation ".*" constr(s) "?" := next_snippet s.

(* optional comment after closing brace, triggers merging of then/else postcondition *)
Ltac merge := after_if_cleanup; run_steps_internal_hook.

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

(* Needed for cases where we only want to give the signature, but no implementation *)
Declare Custom Entry optional_semicolon.
Notation "*/ ; /*" := tt (in custom optional_semicolon at level 1, only parsing).
Notation "*/ /*" := tt (in custom optional_semicolon at level 1, only parsing).

(* Notations have (almost) the same RHS as the `fnspec!` notations in
   bedrock2.WeakestPrecondition, but only allow 0 or 1 return value
   (for C compatibility) and use a different syntax in the LHS (to match
   C syntax and live verif comment markers) *)

Declare Custom Entry funspec.

(* One return value: *)
Notation "'uintptr_t' fname ( 'uintptr_t' a1 , 'uintptr_t' .. , 'uintptr_t' an ) /* *# 'ghost_args' := g1 .. gn ; 'requires' t1 m1 := pre ; 'ensures' t2 m2 r := post #* osemi *" :=
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
 osemi custom optional_semicolon at level 1,
 only parsing).

(* One return value and no arguments: *)
Notation "'uintptr_t' fname ( ) /* *# 'ghost_args' := g1 .. gn ; 'requires' t1 m1 := pre ; 'ensures' t2 m2 r := post #* osemi *" :=
  (fun fname: String.string =>
     (fun fs =>
        (forall g1, .. (forall gn,
           (forall t1 m1, pre ->
              WeakestPrecondition.call fs fname t1 m1 nil
                (fun t2 m2 retvs => exists r, retvs = cons r nil /\ post))) .. ))
     : ProgramLogic.spec_of fname)
(in custom funspec at level 1,
 fname name,
 g1 closed binder, gn closed binder,
 t1 name, t2 name, m1 name, m2 name, r name,
 pre constr at level 200,
 post constr at level 200,
 osemi custom optional_semicolon at level 1,
 only parsing).

(* No return value: *)
Notation "'void' fname ( 'uintptr_t' a1 , 'uintptr_t' .. , 'uintptr_t' an ) /* *# 'ghost_args' := g1 .. gn ; 'requires' t1 m1 := pre ; 'ensures' t2 m2 := post #* osemi *" :=
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
 osemi custom optional_semicolon at level 1,
 only parsing).

(* No return value an no arguments: *)
Notation "'void' fname ( ) /* *# 'ghost_args' := g1 .. gn ; 'requires' t1 m1 := pre ; 'ensures' t2 m2 := post #* osemi *" :=
  (fun fname: String.string =>
     (fun fs =>
        (forall g1, .. (forall gn,
           (forall t1 m1, pre ->
              WeakestPrecondition.call fs fname t1 m1 nil
                (fun t2 m2 retvs => retvs = nil /\ post))) .. ))
     : ProgramLogic.spec_of fname)
(in custom funspec at level 1,
 fname name,
 g1 closed binder, gn closed binder,
 t1 name, t2 name, m1 name, m2 name,
 pre constr at level 200,
 post constr at level 200,
 osemi custom optional_semicolon at level 1,
 only parsing).


(* Same definitions but without ghost_args: *)

(* One return value: *)
Notation "'uintptr_t' fname ( 'uintptr_t' a1 , 'uintptr_t' .. , 'uintptr_t' an ) /* *# 'requires' t1 m1 := pre ; 'ensures' t2 m2 r := post #* osemi *" :=
  (fun fname: String.string =>
     (fun fs =>
        (forall a1, .. (forall an,
           (forall t1 m1, pre ->
              WeakestPrecondition.call fs fname t1 m1
                (@cons (@word.rep _ _) a1 .. (@cons (@word.rep _ _) an nil) ..)
                (fun t2 m2 retvs => exists r, retvs = cons r nil /\ post))) .. ))
     : ProgramLogic.spec_of fname)
(in custom funspec at level 1,
 fname name,
 a1 closed binder, an closed binder,
 t1 name, t2 name, m1 name, m2 name, r name,
 pre constr at level 200,
 post constr at level 200,
 osemi custom optional_semicolon at level 1,
 only parsing).

(* One return value and no arguments: *)
Notation "'uintptr_t' fname ( ) /* *# 'requires' t1 m1 := pre ; 'ensures' t2 m2 r := post #* osemi *" :=
  (fun fname: String.string =>
     (fun fs =>
           (forall t1 m1, pre ->
              WeakestPrecondition.call fs fname t1 m1 nil
                (fun t2 m2 retvs => exists r, retvs = cons r nil /\ post)))
     : ProgramLogic.spec_of fname)
(in custom funspec at level 1,
 fname name,
 t1 name, t2 name, m1 name, m2 name, r name,
 pre constr at level 200,
 post constr at level 200,
 osemi custom optional_semicolon at level 1,
 only parsing).

(* No return value: *)
Notation "'void' fname ( 'uintptr_t' a1 , 'uintptr_t' .. , 'uintptr_t' an ) /* *# 'requires' t1 m1 := pre ; 'ensures' t2 m2 := post #* osemi *" :=
  (fun fname: String.string =>
     (fun fs =>
        (forall a1, .. (forall an,
           (forall t1 m1, pre ->
              WeakestPrecondition.call fs fname t1 m1
                (@cons (@word.rep _ _) a1 .. (@cons (@word.rep _ _) an nil) ..)
                (fun t2 m2 retvs => retvs = nil /\ post))) .. ))
     : ProgramLogic.spec_of fname)
(in custom funspec at level 1,
 fname name,
 a1 closed binder, an closed binder,
 t1 name, t2 name, m1 name, m2 name,
 pre constr at level 200,
 post constr at level 200,
 osemi custom optional_semicolon at level 1,
 only parsing).

(* No return value an no arguments: *)
Notation "'void' fname ( ) /* *# 'requires' t1 m1 := pre ; 'ensures' t2 m2 := post #* osemi *" :=
  (fun fname: String.string =>
     (fun fs =>
        (forall t1 m1, pre ->
           WeakestPrecondition.call fs fname t1 m1 nil
              (fun t2 m2 retvs => retvs = nil /\ post)))
     : ProgramLogic.spec_of fname)
(in custom funspec at level 1,
 fname name,
 t1 name, t2 name, m1 name, m2 name,
 pre constr at level 200,
 post constr at level 200,
 osemi custom optional_semicolon at level 1,
 only parsing).

Notation ".* */ x" :=
  (match x with (* <-- typecheck x before passing it to Ltac, to get better error messages *)
   | _ => ltac:(let r := with_ident_as_string_no_beta x in exact r)
   end)
  (at level 200, x custom funspec at level 1, only parsing).

Notation "'fun_correct!' f" := (program_logic_goal_for (ident_to_string f) f)
  (at level 10, f name, only parsing).

Notation ".* */ //" := True (at level 0, only parsing).
