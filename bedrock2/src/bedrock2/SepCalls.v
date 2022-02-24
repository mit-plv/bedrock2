(* Separation logic automation for a general notion of function call,
   based on "call lemmas" of the form

   seps [...] mOld /\ (forall mNew vals, callPost vals -> seps [...] mNew -> finalPost) ->
   executing a snippet of code satisfies finalPost

   Applying the call lemma is not handled by this file, but solving the above conjunction
   (except for solving finalPost) is. *)

Require Export Coq.ZArith.ZArith. Open Scope Z_scope.
Require Import coqutil.Z.Lia.
Require Export coqutil.Byte.
Require Import coqutil.Datatypes.HList.
Require Import coqutil.Datatypes.PropSet.
Require Export coqutil.Datatypes.Inhabited.
Require Import coqutil.Tactics.rewr coqutil.Tactics.rdelta.
Require Import Coq.Program.Tactics.
Require Export coqutil.Tactics.Tactics.
Require Export coqutil.Tactics.autoforward.
Require Export coqutil.Map.Interface coqutil.Map.Properties coqutil.Map.OfListWord.
Require Export coqutil.Word.Interface coqutil.Word.Properties.
Require Import coqutil.Sorting.OrderToPermutation.
Require Export coqutil.Tactics.fwd.
Require Import coqutil.Tactics.ltac_list_ops.
Require Export bedrock2.Lift1Prop.
Require Export bedrock2.Map.Separation bedrock2.Map.SeparationLogic.
Require Import bedrock2.Array.
Require Export bedrock2.ZnWords.
Require Import bedrock2.ptsto_bytes bedrock2.Scalars.
Require Import bedrock2.groundcbv.
Require Export bedrock2.TacticError.
Require Import Coq.Strings.String. Open Scope string_scope.
Export List.ListNotations. Open Scope list_scope.

Section SepLog.
  Context {width: Z} {word: word.word width} {mem: map.map word byte}.
  Context {word_ok: word.ok word} {mem_ok: map.ok mem}.

  (* Hides a sep behind a definition so that flattening operations keep
     memPred and its associated purePred together as one clause *)
  Definition with_pure(memPred: mem -> Prop)(purePred: Prop): mem -> Prop :=
    sep memPred (emp purePred).

  (* R, typically instantiated to `seps [whatever; is; left]`, appears twice:
     On the left of the impl1 (this determines its value), and as the first
     element of the `seps` on the right (there, it is an evar for the frame).
     P is the continuation postcondition. *)
  Lemma impl1_done: forall (R: mem -> Prop) (P: Prop),
      P -> impl1 R (seps [R; emp P]).
  Proof.
    unfold impl1, seps. intros. apply sep_emp_r. auto.
  Qed.

  (* All arguments except stmt are just ghost parameters to guide typeclass search.
     The shape of stmt will typically be
       forall valAll valPart valFrame1 ... valFrameN,
         sidecondition saying that assembling valPart valFrame1 ... valFrameN = valAll ->
         iff1 (seps [addrPart |-> predPart valPart; Frame...]) (addrAll |-> predAll valAll)
     but since that's a variable number of universally quantified variables, it would
     be a bit cumbersome to enforce that shape, and since it's not needed to enforce it,
     we don't.
     Note that stmt needs to be not only applicable to split oldAll into oldPart and a
     frame, but also to merge back a newPart and newFrame (potentially modified as well,
     eg if a function separately takes two record fields) into a newAll.
     So stmt needs to be more general than oldAll/oldPart.
     But we still pass in the specific oldPart so that typeclass search for split_sepclause
     can determine its length, either from a suchThat, or by computing it *)
  Definition split_sepclause(oldAll oldPart: mem -> Prop)(stmt: Prop) := stmt.

  Local Set Warnings "-notation-overridden".
  Local Infix "++" := SeparationLogic.app. Local Infix "++" := app : list_scope.
  Let nth n xs := SeparationLogic.hd (emp(map:=mem) True) (SeparationLogic.skipn n xs).
  Let remove_nth n (xs : list (mem -> Prop)) :=
    (SeparationLogic.firstn n xs ++ SeparationLogic.tl (SeparationLogic.skipn n xs)).

  Lemma rewrite_ith_in_lhs_of_impl1: forall i Ps Pi Qs R,
      nth i Ps = Pi ->
      iff1 (seps Qs) Pi /\ (* <-- used right-to-left *)
      impl1 (seps (remove_nth i Ps ++ Qs)) R ->
      impl1 (seps Ps) R.
  Proof.
    intros. destruct H0. subst Pi.
    unfold nth, remove_nth in *.
    rewrite <-(seps_nth_to_head i Ps).
    rewrite <- H0.
    rewrite 2seps_app in H1. rewrite seps_app.
    etransitivity. 2: eassumption.
    ecancel.
  Qed.

  (* Transforms the goal so that goal modifications that are made while proving Rs
     are still visible when proving the continuation Cont of the program *)
  Lemma put_and_r_into_emp_seps: forall (Cont: Prop) (Rs: list (mem -> Prop)) (m: mem),
      seps (SeparationLogic.app Rs [emp Cont]) m ->
      seps Rs m /\ Cont.
  Proof.
    intros. change SeparationLogic.app with (@List.app (mem -> Prop)) in H.
    apply seps_app in H. eapply sep_emp_r in H. assumption.
  Qed.
End SepLog.

(* Hints for `(split_sepclause ?oldAll ?oldPart ?stmt)` goals *)
Create HintDb split_sepclause_goal.

(* Hints to solve the sideconditions of the `stmt` above, when using the iff1
   right-to-left, ie in the split direction *)
Create HintDb split_sepclause_sidecond.

(* Hints to solve the sideconditions of the `stmt` above, when using the iff1
   left-to-right, ie in the merge direction *)
Create HintDb merge_sepclause_sidecond.

#[global] Hint Opaque split_sepclause : split_sepclause_goal.

Ltac split_ith_left_to_cancel_with_fst_right i :=
  lazymatch goal with
  | |- Lift1Prop.impl1 (seps ?L) (seps (?RHead :: ?RRest)) =>
    eapply (rewrite_ith_in_lhs_of_impl1 i L);
    cbn [hd app firstn tl skipn];
    [ reflexivity | ];
    (* Current goal is a conjunction of two subgoals:
       - iff1 for right-to-left-rewrite that we'll derive from a split_sepclause instance
       - new impl1 to be proven after this cancellation step *)
    let Li := lazymatch goal with |- iff1 _ ?Li /\ impl1 _ _ => Li end in
    let Sp := fresh "Sp" in
    eassert (split_sepclause Li RHead _) as Sp;
    [ (* can be left unsolved for debugging *)
      try typeclasses eauto with split_sepclause_goal
      (* typeclasses eauto instead of eauto because eauto unfolds split_sepclause
         and then just does `exact H` for the last Prop in the context, and it
         seems that `Hint Opaque` and `Hint Constants Opaque` don't fix that
         (and `Opaque split_sepclause` would fix it, but also affects the conversion
         algorithm) *)
    | split;
    [ lazymatch type of Sp with
      | split_sepclause _ _ ?stmt =>
          tryif is_evar stmt then
            idtac (* debugging and typeclasses eauto above failed *)
          else (
            cbv [split_sepclause] in Sp;
            eapply Sp;
            (* sideconditions of Sp can be left unsolved for debugging *)
            eauto with split_sepclause_sidecond
          )
      end
    | (* this goal is the remaining impl1 after cancellation, and it's the only
         goal supposed to remain open unless debugging *) ] ]
  end.

(* Poses split_sepclause lemmas as hypotheses in the context, forming a stack of
   rewrite steps that have been performed, which can later be undone by
   pop_split_sepclause_stack *)
Ltac impl_ecancel_step_with_splitting :=
  lazymatch goal with
  | |- Lift1Prop.impl1 (seps ?L) _ =>
    let iLi := index_and_element_of L in (* <-- multi-success! *)
    let i := lazymatch iLi with (?i, _) => i end in
    split_ith_left_to_cancel_with_fst_right i; []
  end.

Ltac use_sep_asm :=
  match goal with
  | H: seps _ ?m |- seps _ ?m =>
    refine (Morphisms.subrelation_refl Lift1Prop.impl1 _ _ _ m H)
  end.

Ltac impl_ecancel :=
  cancel_seps;
  repeat (repeat (once ecancel_step_by_implication); try impl_ecancel_step_with_splitting).

Ltac finish_impl_ecancel :=
  match goal with
  | |- impl1 ?R (seps [?E; emp ?P]) => is_evar E; refine (impl1_done R P _)
  | |- impl1 ?x (seps [?E]) => is_evar E; change (impl1 x E); exact impl1_refl
  | |- impl1 ?x ?y => first [ is_evar x | is_evar y | constr_eq x y ]; exact impl1_refl
  | |- _ => pose_err Error:("impl_ecancel should cancel all clauses of this goal (except maybe one remaining emp)")
  end.

Ltac impl_ecancel_assumption :=
  use_sep_asm;
  impl_ecancel;
  try finish_impl_ecancel.

Ltac clear_split_sepclause_stack :=
  repeat match goal with
         | H: split_sepclause _ _ _ |- _ => clear H
         end.

Ltac pop_split_sepclause_stack :=
  let H := lazymatch goal with H: seps _ ?m |- _ => H end in
  let Sp := lazymatch goal with Sp: split_sepclause _ _ _ |- _ => Sp end in
  ((cbv [split_sepclause] in Sp;
    cbn [seps] in Sp, H;
    seprewrite_in_by Sp H ltac:(eauto with merge_sepclause_sidecond)
   ) || let T := type of Sp in idtac "Note: Failed to merge sep clauses using" T);
  clear Sp.

(* Note: this won't work if the new `seps [...] mNew` is under some existentials
   or under a disjunction *)
Ltac intro_new_mem :=
  lazymatch goal with
  | |- forall (m: @map.rep _ _ _), _ =>
      let mNew := fresh m in
      intro mNew; intros;
      repeat pop_split_sepclause_stack
  end.

Ltac put_cont_into_emp_seps :=
  lazymatch goal with
  | |- seps ?Pre ?mOld /\ (forall mNew, _) =>
      apply put_and_r_into_emp_seps; cbn [SeparationLogic.app]
  | |- _ => fail 10000 "Expected a goal of the form" "(seps ?Pre ?mOld /\ (forall mNew, _))"
  end.

Ltac after_sep_call :=
  put_cont_into_emp_seps;
  use_sep_asm;
  impl_ecancel;
  match goal with
  | H: tactic_error _ |- _ => idtac
  | |- _ => finish_impl_ecancel
  end.
