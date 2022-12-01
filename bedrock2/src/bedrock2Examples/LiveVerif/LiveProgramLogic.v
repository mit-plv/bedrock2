Require Import Coq.ZArith.ZArith. Local Open Scope Z_scope.
Require Import Coq.Strings.String.
Require Import coqutil.Tactics.rdelta.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Tactics.syntactic_unify.
Require Import coqutil.Tactics.destr.
Require Import coqutil.Tactics.fwd.
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
Require Import bedrock2Examples.LiveVerif.PackageContext.
Require Import bedrock2Examples.LiveVerif.LiveSnippet.

Definition functions_correct
  (* universally quantified abstract function list containing all functions: *)
  (qfs: list (string * func)):
  (* subset of functions for which to assert correctness, along with their specs: *)
  list ((string * func) * (* name and impl *)
        (list (string * func) -> Prop) (* spec_of *))
  -> Prop := List.Forall (fun '(name_and_impl, spec) => spec (cons name_and_impl qfs)).

Definition function_with_callees: Type :=
  func * list ((string * func) * (* name and impl *)
               (list (string * func) -> Prop) (* spec_of *)).

Definition program_logic_goal_for(name: string)(f: function_with_callees)
  {spec: bedrock2.ProgramLogic.spec_of name}: Prop :=
  match f with
  | (impl, callees) => forall functions,
      functions_correct functions callees -> spec (cons (name, impl) functions)
  end.

Definition ready{P: Prop} := P.

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
    let is_decl := lazymatch l with
                   | context[(x, _)] => false
                   | _ => true
                   end in
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
        let kvs := eval unfold List.combine in (List.combine keys values) in
        change (wp_cmd call c t m (map.of_list kvs) post)
    end;
    lazymatch is_decl with
    | true => idtac
    | false => try clear old_i
    end
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

Ltac prove_concrete_post_pre :=
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
    destruct_ifs;
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
           | H: _ \/ _ |- _ => destruct H (* <-- might become expensive... *)
           end;
    try congruence;
    try ZnWords;
    intuition (congruence || ZnWords || eauto with prove_post).

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

Ltac close_block :=
  lazymatch goal with
  | B: scope_marker ?sk |- _ =>
      lazymatch sk with
      | ElseBranch =>
          eapply wp_skip;
          package_context
      | LoopBody =>
          eapply wp_skip;
          prove_concrete_post
      | FunctionBody =>
          lazymatch goal with
          | H: functions_correct ?fs ?l |- _ =>
              let T := lazymatch type of l with list ?T => T end in
              let e := strip_conss l in
              unify e (@nil T)
          end;
          lazymatch goal with
          | |- @ready ?g => change g
          | |- @final_postcond_marker ?g => change g
          | |- _ => idtac
          end;
          lazymatch goal with
          | |- wp_cmd _ _ _ _ _ _ => ret (@nil String.string)
          | |- _ => idtac (* ret nonEmptyVarList was already called *)
          end;
          prove_concrete_post
      | _ => fail "Can't end a block here"
      end
  | _ => fail "no scope marker found"
  end.

Ltac add_snippet s :=
  assert_no_error;
  lazymatch s with
  | SAssign ?is_decl ?name ?val => eapply (wp_set _ name val) (* TODO validate is_decl *)
  | SStore ?sz ?addr ?val => eapply (wp_store _ sz addr val)
  | SIf ?c => eapply (wp_if_bool_dexpr _ c); pose proof mk_temp_if_marker
  | SElse =>
      assert_scope_kind ThenBranch;
      eapply wp_skip;
      package_context
  | SWhile ?cond ?measure0 =>
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
        fwd
(* TODO;
        lazymatch goal with
        | |- exists b, dexpr_bool3 _ _ _ b _ _ _ => eexists
        | |- _ => fail "assertion failure: hypothesis of wp_while has unexpected shape"
        end*) ]
  | SStart => start
  | SEnd => close_block
  | SRet ?retnames => ret retnames
  | SEmpty => idtac
  end.

Lemma BoolSpec_expr_branches{Bt Bf: Prop}{b: bool}{H: BoolSpec Bt Bf b}(Pt Pf Pa: Prop):
  (Bt -> Pt) ->
  (Bf -> Pf) ->
  Pa ->
  bool_expr_branches b Pt Pf Pa.
Proof.
  intros. unfold bool_expr_branches. destruct H; auto.
Qed.

Ltac cleanup :=
  match goal with
  | x := _ |- _ => clear x
  | H: ?T |- _ => is_destructible_and T; let H' := fresh H in destruct H as (H & H')
  end.

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
  | |- dexpr1 _ _ (expr.load _ _)  _ _ => eapply dexpr1_load
  | |- bool_expr_branches _ _ _ _ => eapply BoolSpec_expr_branches; [ intro | intro | ]
  | |- then_branch_marker ?G =>
      let H := lazymatch goal with H: temp_if_marker |- _ => H end in
      let n := fresh "Scope0" in
      pose proof (mk_scope_marker ThenBranch) as n;
      move n before H;
      clear H;
      change G
  | |- else_branch_marker ?G =>
      let H := lazymatch goal with H: temp_if_marker |- _ => H end in
      let n := fresh "Scope0" in
      pose proof (mk_scope_marker ElseBranch) as n;
      move n before H;
      clear H;
      change G
  | |- after_if ?fs ?b ?Q1 ?Q2 ?rest ?post =>
      lazymatch goal with
      | H: temp_if_marker |- _ => clear H
      end;
      tryif is_evar Q1 then idtac (* need to first complete then-branch *)
      else tryif is_evar Q2 then idtac (* need to first complete else-branch *)
      else after_if
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
  | |- wp_cmd _ _ _ _ _ _ =>
      first [ cleanup
            | lazymatch goal with
              | |- ?G => change (@ready G)
              end ]
  end.

Ltac step := first [ heapletwise_step | program_logic_step ].

Ltac step_is_done :=
  match goal with
  | |- @ready _ => idtac
  | |- @final_postcond_marker _ => idtac
  | |- after_if _ _ ?Q1 ?Q2 _ _ => is_evar Q1
  | |- after_if _ _ ?Q1 ?Q2 _ _ => is_evar Q2
  end.

Ltac run_steps :=
  tryif step_is_done then idtac
  else tryif step then run_steps
  else pose_err Error:("'step' should not fail here").

(* can be overridden with idtac for debugging *)
Ltac run_steps_hook := run_steps.

Require Import Ltac2.Ltac2.

Ltac2 step () := ltac1:(step).

Ltac2 Notation "step" := step ().

Ltac2 add_snippet(s: constr) := ltac1:(s |- add_snippet s) (Ltac1.of_constr s).
Ltac2 run_steps_hook () := ltac1:(run_steps_hook).

Ltac2 next_snippet(s: unit -> constr) :=
  match Control.case (fun _ => Control.focus 1 2 (fun _ => ())) with
  | Val _ => (* there are >= 2 open goals *)
      Control.focus 1 1 (fun _ => add_snippet (s ()); run_steps_hook ());
      Control.focus 1 1 run_steps_hook
  | Err _ => (* at most 1 open goal *)
      Control.focus 1 1 (fun _ => add_snippet (s ()); run_steps_hook ())
  end.

Ltac2 Notation ".*" s(thunk(constr)) "*" := next_snippet s.
Ltac2 Notation "#*" s(thunk(constr)) "*" := next_snippet s.

(*
(* One return value: *)
Notation ".* */ 'uintptr_t' f ( 'uintptr_t' a1 , 'uintptr_t' .. , 'uintptr_t' an ) /**# 'ghost_args' := g1 .. gn ; 'requires' t1 m1 := pre ; 'ensures' t2 m2 r := post" :=
{ f : list String.string * list String.string * cmd &
  forall fs t1 m1, (forall a1, .. (forall an, (forall g1, .. (forall gn, pre ->
    vc_func fs f t1 m1 (cons a1 .. (cons an nil) ..)
      (fun t2 m2 retvs => exists r, retvs = cons r nil /\ post)) .. )) .. ) }
(at level 200,
 f name,
 a1 closed binder, an closed binder,
 g1 closed binder, gn closed binder,
 t1 name, t2 name, m1 name, m2 name, r name,
 pre at level 200,
 post at level 200).

(* No return value: *)
Notation ".* */ 'void' f ( 'uintptr_t' a1 , 'uintptr_t' .. , 'uintptr_t' an ) /**# 'ghost_args' := g1 .. gn ; 'requires' t1 m1 := pre ; 'ensures' t2 m2 := post" :=
{ f : list String.string * list String.string * cmd &
  forall fs t1 m1, (forall a1, .. (forall an, (forall g1, .. (forall gn, pre ->
    vc_func fs f t1 m1 (cons a1 .. (cons an nil) ..)
      (fun t2 m2 retvs => retvs = nil /\ post)) .. )) .. ) }
(at level 200,
 f name,
 a1 closed binder, an closed binder,
 g1 closed binder, gn closed binder,
 t1 name, t2 name, m1 name, m2 name,
 pre at level 200,
 post at level 200).
*)

Notation ".* */ //" := True (only parsing).
