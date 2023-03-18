Require Import Ltac2.Ltac2.
Require Import Coq.micromega.Lia.
Require Import coqutil.Map.Interface.
Require Import coqutil.Word.Interface.
Require Import coqutil.Tactics.fold_hyps coqutil.Tactics.foreach_hyp.
Require Import bedrock2.PurifySep.
Require Import bedrock2.HeapletwiseHyps.
Require Import coqutil.Tactics.ident_ops.
Require Import bedrock2.bottom_up_simpl_ltac1.
Require Import bedrock2.unzify.

Ltac is_var_b x :=
  match constr:(Set) with
  | _ => let __ := match constr:(Set) with
                   | _ => is_var x
                   end in
         constr:(true)
  | _ => constr:(false)
  end.

(* TODO replace by simple tactic failure? *)
Inductive nothing_to_purify: Prop := .

(* returns the name of the new purified hyp or nothing_to_purify *)
Ltac purified_hyp_name_of_pred h pred m :=
  lazymatch is_var_b pred with
  | true => constr:(nothing_to_purify)
  | false =>
      let g := open_constr:(purify pred _) in
      let pf := match constr:(Set) with
                | _ => constr:(ltac:(eauto with purify) : g)
                | _ => fail 1000 g "cannot be solved by eauto with purify"
                end in
      lazymatch type of pf with
      | purify pred True => constr:(nothing_to_purify)
      | purify pred ?p =>
          let hp := fresh "__pure_" h in
          let __ := match constr:(Set) with
                    | _ => pose proof (pf m h) as hp
                    end in
          hp
      end
  end.

(* returns the name of the new purified hyp or nothing_to_purify *)
Ltac purified_hyp_name h t :=
  lazymatch t with
  | with_mem ?m ?pred => purified_hyp_name_of_pred h pred m
  | ?pred ?m => lazymatch type of m with
                | @map.rep (@word.rep _ _) Byte.byte _ => purified_hyp_name_of_pred h pred m
                | _ => constr:(nothing_to_purify)
                end
  | _ => constr:(nothing_to_purify)
  end.

Ltac puri_simpli_zify_hyp fail_if_too_trivial h t :=
  try ((* try block starts here because everthing starting from here needs
          to be reverted if the resulting hyp is too trivial *)
      let hp := purified_hyp_name h t in
      lazymatch hp with
      | nothing_to_purify => idtac
      | _ => let tp := type of hp in
             bottom_up_simpl_in_hyp_of_type hp tp;
             let tp := type of hp in
             let wok := get_word_ok_or_dummy in
             let zo := zify_hyp_option wok hp tp in
             assert_succeeds
               (idtac;
                lazymatch zo with
                | @None ?tz => clear hp; fail_if_too_trivial tz
                | @Some ?tz ?hz => clear hp hz; fail_if_too_trivial tz
                end);
             apply_range_bounding_lemma_in_eqs
      end).

(* possible arguments for fail_if_too_trivial above: *)
Ltac accept_always t := idtac.
Ltac accept_unless_follows_by_xlia t := assert_fails (idtac; assert t by xlia zchecker).

Ltac puri_simpli_zify_hyps fail_if_too_trivial :=
  foreach_hyp (puri_simpli_zify_hyp fail_if_too_trivial).

Inductive derivability_test_marker: Prop := mk_derivability_test_marker.

Ltac clear_pure_hyp_if_derivable h tp :=
  tryif ident_starts_with __pure_ h then
    try (clear h; assert_succeeds (idtac; assert tp by (zify_goal; xlia zchecker)))
  else idtac.

Ltac clear_upto_marker marker :=
  lazymatch goal with
  | m: marker |- _ => foreach_hyp_upto_marker marker (fun h tp => clear h); clear m
  | |- _ => fail "marker not found"
  end.

Ltac unpurify :=
  pose proof mk_derivability_test_marker;
  puri_simpli_zify_hyps accept_always;
  foreach_hyp_from_marker_upwards derivability_test_marker clear_pure_hyp_if_derivable;
  clear_upto_marker derivability_test_marker.
