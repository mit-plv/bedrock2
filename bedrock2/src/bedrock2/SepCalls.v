(* Separation logic automation for a general notion of function call,
   based on "call lemmas" of the form

   (_ * ...) mOld /\ (forall mNew vals, callPost vals -> (_ * ...) mNew -> finalPost) ->
   executing a snippet of code satisfies finalPost

   Applying the call lemma is not handled by this file, but solving the above conjunction
   (except for solving finalPost) is. *)

Require Import Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import coqutil.Z.Lia.
Require Import coqutil.Byte.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PropSet.
Require Import coqutil.Datatypes.Inhabited.
Require Import coqutil.Tactics.rewr coqutil.Tactics.rdelta.
Require Import Coq.Program.Tactics.
Require Import coqutil.Macros.symmetry.
Require Import coqutil.Tactics.Tactics.
Require Import coqutil.Tactics.autoforward.
Require Import coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.OfListWord.
Require Import coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Sorting.OrderToPermutation.
Require Import coqutil.Tactics.fwd.
Require Import coqutil.Tactics.ltac_list_ops.
Require Import bedrock2.Lift1Prop.
Require Import bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array.
Require Import bedrock2.ZnWords.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.groundcbv.
Require Import bedrock2.TacticError.
Require Import bedrock2.ident_to_string.
Require Import Coq.Strings.String. Open Scope string_scope.
Require Import Coq.Lists.List. (* to make sure `length` refers to list rather than string *)
Import List.ListNotations. Open Scope list_scope.

Section SepLog.
  Context {width: Z} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  Lemma icancel_start: forall (P Q: Tree.Tree (mem -> Prop)) (C: Prop) (m: mem),
      Tree.to_sep P m ->
      impl1 (seps (Tree.flatten P)) (seps (Tree.flatten Q)) /\ C ->
      Tree.to_sep Q m /\ C.
  Proof.
    intros * ? (? & ?). split. 2: assumption.
    eapply Tree.impl1_to_sep_of_impl1_flatten in H0.
    apply H0. assumption.
  Qed.

  (* R, typically instantiated to `seps [whatever; is; left]`, appears twice:
     On the left of the impl1 (this determines its value), and as the first
     element of the `seps` on the right (there, it is an evar for the frame). *)
  Lemma icancel_done_evar_r: forall (R: mem -> Prop) (C: Prop),
      C -> impl1 R (seps [R]) /\ C.
  Proof.
    unfold impl1, seps. auto.
  Qed.

  Lemma icancel_done_nil_r: forall (C: Prop),
      C -> impl1 (seps (map := mem) []) (seps []) /\ C.
  Proof. split. 2: assumption. exact impl1_refl. Qed.

  (* On goals of this shape, `typeclasses eauto with split_speclause_goal` will be called,
     which will pose its result `stmt` as a hypothesis and then shelve the goal.
     The shape of stmt has to be
       forall valAll valPart valFrame1 ... valFrameN,
         sidecondition saying that assembling valPart valFrame1 ... valFrameN = valAll ->
         iff1 (predAll valAll addrAll) (sep (predPart valPart addrPart)
                                            (seps [Frame...]))
     Note that stmt needs to be not only applicable to split oldAll into oldPart and a
     frame, but also to merge back a newPart and newFrame (potentially modified as well,
     eg if a function separately takes two record fields) into a newAll.
     So stmt needs to be more general than oldAll/oldPart.
     The specific shape of the RHS of the above iff1 is for compatibility with
     cancel_part_of_ith_lhs_with_first_rhs, so that no sep flattening is required
     during cancellation. *)
  Definition split_sepclause(oldAll oldPart: mem -> Prop)(oldFrame: list (mem -> Prop))
             (remainingGoal: Prop) :=
    iff1 oldAll (sep oldPart (seps oldFrame)) /\ remainingGoal.

  Let nth n xs := SeparationLogic.hd (emp(map:=mem) True) (SeparationLogic.skipn n xs).
  Let remove_nth n (xs : list (mem -> Prop)) :=
        (SeparationLogic.app (SeparationLogic.firstn n xs)
                             (SeparationLogic.tl (SeparationLogic.skipn n xs))).

  Lemma cancel_ith_lhs_with_first_rhs: forall i Ls R1 Rs C,
      impl1 (nth i Ls) R1 ->
      impl1 (seps (remove_nth i Ls)) (seps Rs) /\ C ->
      impl1 (seps Ls) (seps (R1 :: Rs)) /\ C.
  Proof.
    intros * ? (? & ?). split. 2: assumption.
    eapply (cancel_seps_at_indices_by_implication i 0%nat); eassumption.
  Qed.

  Lemma cancel_part_of_ith_lhs_with_first_rhs: forall i Ls Li Frame R1 Rs C,
      nth i Ls = Li ->
      split_sepclause Li R1 Frame
         (impl1 (seps (SeparationLogic.app (remove_nth i Ls) Frame)) (seps Rs) /\ C) ->
      impl1 (seps Ls) (seps (R1 :: Rs)) /\ C.
  Proof.
    intros. destruct H0 as (?&?&?). subst Li. split. 2: assumption.
    unfold nth, remove_nth in *.
    rewrite <-(seps_nth_to_head i Ls).
    rewrite H0.
    rewrite 2seps_app in H1. rewrite seps_app.
    rewrite seps_cons.
    cancel. cancel_seps_at_indices_by_implication 0%nat 0%nat. 1: exact impl1_refl.
    cbn [seps].
    etransitivity. 2: eassumption.
    ecancel.
  Qed.
End SepLog.

Definition split_merge_lemma(P: Prop) := P.

(* Hints for `(split_sepclause ?oldAll ?oldPart ?oldFrame ?remainginGoal)` goals *)
Create HintDb split_sepclause_goal.
#[global] Hint Opaque split_sepclause : split_sepclause_goal.

Ltac default_pose_split_merge_lemma_or_else error_handler :=
  first [ unshelve (solve [eauto with split_sepclause_goal])
        | error_handler Error:("This goal should be solvable by"
                               "eauto with split_sepclause_goal") ].

(* Hook that can be overriden with ::=, for users who don't want to use the
   split_sepclause_goal hint DB.
   In case of failure, should call error_handler with one argument of type tactic_error *)
Ltac pose_split_merge_lemma_or_else error_handler :=
  default_pose_split_merge_lemma_or_else error_handler.


(* Hints to solve the sideconditions of the `stmt` above, when using the iff1
   left-to-right, ie in the split direction *)
Create HintDb split_sepclause_sidecond.

Ltac default_solve_split_sepclause_sidecond_or_pose_err :=
  first [ solve [eauto with split_sepclause_sidecond]
        | pose_err Error:("This goal should be solvable by"
                          "eauto with split_sepclause_sidecond") ].

(* Hook that can be overriden with ::=, for users who don't want to use the
   split_sepclause_sidecond hint DB *)
Ltac solve_split_sepclause_sidecond_or_pose_err :=
  default_solve_split_sepclause_sidecond_or_pose_err.


(* Hints to solve the sideconditions of the `stmt` above, when using the iff1
   right-to-left, ie in the merge direction *)
Create HintDb merge_sepclause_sidecond.

Ltac default_solve_merge_sepclause_sidecond_or_pose_err :=
  first [ solve [eauto with merge_sepclause_sidecond]
        | pose_err Error:("This goal should be solvable by"
                          "eauto with merge_sepclause_sidecond") ].

(* Hook that can be overriden with ::=, for users who don't want to use the
   merge_sepclause_sidecond hint DB *)
Ltac solve_merge_sepclause_sidecond_or_pose_err :=
  default_solve_merge_sepclause_sidecond_or_pose_err.

Ltac split_ith_left_and_cancel_with_fst_right0 i are_you_sure_about_i :=
  eapply (cancel_part_of_ith_lhs_with_first_rhs i);
  cbn [SeparationLogic.hd SeparationLogic.tl
       SeparationLogic.app SeparationLogic.firstn SeparationLogic.skipn];
  [ reflexivity | ];
  pose_split_merge_lemma_or_else
    ltac:(fun e => lazymatch are_you_sure_about_i with
                   | true => pose_err e
                   | false => fail
                   | _ => fail 10000 "argument are_you_sure_about_i should be a bool"
                   end);
  lazymatch goal with
  | _: tactic_error _ |- _ => idtac
  | Sp: ?stmt |- _ =>
      tryif (assert_fails (idtac;
                           lazymatch ret_type stmt with
                           | iff1 ?predAll (sep ?predPart (seps ?Frame)) => idtac
                           end))
      then pose_err Error:("The conclusion of" Sp "is not of shape"
                                 "iff1 ?predAll (sep ?predPart (seps ?Frame))")
      else (
        split; (* also unfolds split_sepclause *)
        [ eapply Sp;
          (* sideconditions of Sp can be left unsolved for debugging *)
          solve_split_sepclause_sidecond_or_pose_err
        | change (split_merge_lemma stmt) in Sp
          (* this goal is the remaining (impl1 _ _ /\ _) after cancellation, and it's the
             only goal supposed to remain open unless debugging *) ]
      )
  end.

(* Can be called manually to debug *)
Ltac split_ith_left_and_cancel_with_fst_right i :=
  split_ith_left_and_cancel_with_fst_right0 i true.

(* Poses split_sepclause lemmas as hypotheses in the context, forming a stack of
   rewrite steps that have been performed, which can later be undone by
   pop_split_sepclause_stack *)
Ltac impl_ecancel_step_with_splitting :=
  lazymatch goal with
  | |- impl1 (seps ?L) _ /\ _ =>
    let iLi := index_and_element_of L in (* <-- multi-success! *)
    let i := lazymatch iLi with (?i, _) => i end in
    split_ith_left_and_cancel_with_fst_right0 i false; []
  end.

Ltac impl_ecancel_step_without_splitting :=
  lazymatch goal with
  | |- impl1 (seps ?L) (seps (?R1 :: ?Rs))  /\ _ =>
    assert_fails (idtac; let y := rdelta_var R1 in is_evar y);
    let iLi := index_and_element_of L in (* <-- multi-success! *)
    let i := lazymatch iLi with (?i, _) => i end in
    eapply (cancel_ith_lhs_with_first_rhs i L);
    cbn [SeparationLogic.hd SeparationLogic.tl
         SeparationLogic.app SeparationLogic.firstn SeparationLogic.skipn];
    [solve [auto 1 with nocore ecancel_impl]|]
  end.

Ltac use_sep_asm :=
  lazymatch goal with
  | |- _ _ /\ _ => idtac
  (* to make sure this cancellation code can also be used when there's no continutation
     postcondition, eg at the end of a proof where we just prove that the computed
     postcondition implies the desired postcondition *)
  | |- _ => refine (proj1 (_: _ /\ True))
  end;
  match goal with
  | H: ?P ?m |- ?Q ?m /\ ?C =>
      let treeP := reify P in
      let treeQ := reify Q in
      change (Tree.to_sep treeQ m /\ C);
      eapply (icancel_start treeP treeQ C);
      [ cbn [Tree.to_sep]; exact H | cbn [Tree.flatten Tree.interp SeparationLogic.app] ]
  end.

Ltac impl_ecancel :=
  repeat (impl_ecancel_step_with_splitting || impl_ecancel_step_without_splitting ).

Ltac finish_impl_ecancel :=
  lazymatch goal with
  | |- impl1 ?R (seps [?E]) /\ ?C => is_evar E; refine (icancel_done_evar_r R C _)
  | |- impl1 (seps []) (seps []) /\ ?C => refine (icancel_done_nil_r C _)
  | |- _ => pose_err Error:("impl_ecancel should cancel all clauses of this goal")
  end;
  lazymatch goal with
  | |- True => exact I
  | |- _ => idtac
  end.

Ltac clear_split_sepclause_stack :=
  repeat match goal with
         | H: split_merge_lemma _ |- _ => clear H
         end.

Ltac pop_split_sepclause_stack_step m :=
  let H := lazymatch goal with H: _ m |- _ => H end in
  let Sp := lazymatch goal with Sp: split_merge_lemma _ |- _ => Sp end in
  cbv [split_merge_lemma] in Sp;
  cbn [seps] in Sp, H;
  first [ seprewrite_in (symmetry! Sp) H;
          [ solve_merge_sepclause_sidecond_or_pose_err .. | clear Sp ]
        | let Hs := varconstr_to_string H in
          let Sps := varconstr_to_string Sp in
          let tac := eval cbv in ("seprewrite_in (symmetry! " ++ Sps ++ ") " ++ Hs)%string in
          pose_err Error:(tac "should succeed on this goal") ].

Ltac pop_split_sepclause_stack m :=
  match goal with
  | _: tactic_error _ |- _ => idtac
  | |- _ => tryif (progress pop_split_sepclause_stack_step m) then
             pop_split_sepclause_stack m
           else
             idtac
  end.

(* Note: this won't work if the new `(_ * ...) mNew` is under some existentials
   or under a disjunction *)
Ltac intro_new_mem :=
  lazymatch goal with
  | |- forall (m: @map.rep _ _ _), _ =>
      let mNew := fresh m in
      intro mNew; intros;
      pop_split_sepclause_stack mNew
  end.

(* ecancel an assumption (using impl1), and also split sepclauses on the left
   while canceling *)
Ltac scancel_asm :=
  use_sep_asm;
  impl_ecancel;
  match goal with
  | H: tactic_error _ |- _ => idtac
  | |- _ => finish_impl_ecancel
  end.
